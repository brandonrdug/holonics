import AVFoundation
import CoreAudio
import Foundation
import Darwin

struct DeviceDescription: Codable {
    let id: UInt32
    let name: String
    let inputChannels: UInt32
    let outputChannels: UInt32
    let isDefaultInput: Bool
    let isDefaultOutput: Bool
}

struct HostTimebase: Codable {
    let nanosecondsNumerator: UInt32
    let ticksDenominator: UInt32
}

func currentHostTimebase() -> HostTimebase {
    var info = mach_timebase_info_data_t()
    mach_timebase_info(&info)
    return HostTimebase(nanosecondsNumerator: info.numer, ticksDenominator: info.denom)
}

struct BufferReceipt: Codable {
    let ordinal: UInt64
    let frameCount: UInt32
    let sampleTime: Double
    let sampleTimeValid: Bool
    let hostTime: UInt64
    let hostTimeValid: Bool
    let sampleOffset: UInt64
    let droppedFramesBefore: UInt64
    let accepted: Bool
    let timestampIssue: String?
    let late: Bool?
    let overflow: Bool?
}

struct AudioReceipt: Codable {
    let schema: String
    let operation: String
    let deviceName: String?
    let deviceUID: String?
    let sampleRate: Double
    let channelCount: UInt32
    let hardwareFormat: String
    let outputFormat: String
    let hostClock: String
    var hostTimebase: HostTimebase = currentHostTimebase()
    let buffers: [BufferReceipt]
    let totalFrames: UInt64
    let droppedFrames: UInt64?
    let lateBuffers: UInt64?
    let overflowBuffers: UInt64?
    let gapFrames: UInt64?
    let clippingSamples: UInt64?
    let refusedSamples: UInt64?
    let timestampRefusedFrames: UInt64?
    let conversionLoss: String
    let permission: String
    let captureStartHostTime: UInt64?
    let captureEndHostTime: UInt64?
    let playbackStartHostTime: UInt64?
    let playbackEndHostTime: UInt64?
    let playbackScheduledFileFrames: UInt64?
    let playbackScheduledSampleRate: Double?
    let playbackScheduledSampleStart: Double?
    let playbackScheduledSampleEnd: Double?
    let playbackPlayedFrames: UInt64?
    let completed: Bool
    let terminationReason: String
}

enum AudioToolError: Error, CustomStringConvertible {
    case usage(String)
    case coreAudio(String)
    case permission(String)
    case capture(String)
    case codec(String)

    var description: String {
        switch self {
        case .usage(let value), .coreAudio(let value), .permission(let value), .capture(let value), .codec(let value): return value
        }
    }
}

final class CaptureCollector {
    private let lock = NSLock()
    private(set) var pcm = [Int16]()
    private(set) var buffers = [BufferReceipt]()
    private(set) var clipping: UInt64 = 0
    private(set) var refused: UInt64 = 0
    private(set) var timestampRefusedFrames: UInt64 = 0
    private(set) var totalFrames: UInt64 = 0
    private(set) var droppedFrames: UInt64 = 0
    private(set) var gapFrames: UInt64 = 0
    // AVAudioEngine's tap does not expose a reliable late/overflow flag. Keep these unknown
    // rather than manufacturing zeroes from an unobserved condition.
    private var expectedSample: Double?
    private(set) var startHost: UInt64?
    private(set) var endHost: UInt64?

    func append(_ buffer: AVAudioPCMBuffer, time: AVAudioTime?) {
        let frameCount = buffer.frameLength
        let sampleTimeValid = time?.isSampleTimeValid == true
        let hostTimeValid = time?.isHostTimeValid == true
        let sampleTime = sampleTimeValid ? Double(time!.sampleTime) : -1
        let hostTime = hostTimeValid ? time!.hostTime : 0
        var local = [Int16]()
        local.reserveCapacity(Int(frameCount))
        let channels = Int(buffer.format.channelCount)
        if let float = buffer.floatChannelData {
            for frame in 0..<Int(frameCount) {
                var sum = 0.0
                for channel in 0..<channels { sum += Double(float[channel][frame]) }
                convert(sum / Double(max(channels, 1)), into: &local)
            }
        } else if let int16 = buffer.int16ChannelData {
            for frame in 0..<Int(frameCount) {
                var sum: Int64 = 0
                for channel in 0..<channels { sum += Int64(int16[channel][frame]) }
                let value = Int64((Double(sum) / Double(max(channels, 1))).rounded())
                if value < Int64(Int16.min) || value > Int64(Int16.max) { clipping += 1 }
                local.append(Int16(clamping: value))
            }
        } else {
            refused += UInt64(frameCount)
        }

        lock.lock()
        let offset = totalFrames
        var gap: UInt64 = 0
        var accepted = true
        var timestampIssue: String?
        if let expectedSample, sampleTime >= expectedSample, sampleTime - expectedSample > 0.5 {
            gap = UInt64((sampleTime - expectedSample).rounded())
            gapFrames += gap
            droppedFrames += gap
        } else if let expectedSample, sampleTime >= 0, sampleTime + 0.5 < expectedSample {
            accepted = false
            timestampIssue = "sample timestamp moved backwards or overlapped the preceding accepted buffer"
            timestampRefusedFrames += UInt64(frameCount)
            refused += UInt64(frameCount)
        }
        self.expectedSample = accepted && sampleTime >= 0 ? sampleTime + Double(frameCount) : nil
        let hostNow = mach_absolute_time()
        if startHost == nil { startHost = hostTime == 0 ? hostNow : hostTime }
        // Host ticks and audio sample positions are different clock domains; never add a frame
        // count to a host timestamp. This is the callback's observed host endpoint.
        endHost = hostTime == 0 ? hostNow : hostTime
        buffers.append(BufferReceipt(ordinal: UInt64(buffers.count), frameCount: frameCount, sampleTime: sampleTime, sampleTimeValid: sampleTimeValid, hostTime: hostTime, hostTimeValid: hostTimeValid, sampleOffset: offset, droppedFramesBefore: gap, accepted: accepted, timestampIssue: timestampIssue, late: nil, overflow: nil))
        if accepted {
            pcm.append(contentsOf: local)
            totalFrames += UInt64(frameCount)
        }
        lock.unlock()
    }

    private func convert(_ value: Double, into output: inout [Int16]) {
        if !value.isFinite { refused += 1; output.append(0); return }
        let scaled = value * Double(Int16.max)
        if scaled > Double(Int16.max) || scaled < Double(Int16.min) { clipping += 1 }
        output.append(Int16(clamping: Int64(scaled.rounded())))
    }
}

func property<T>(_ device: AudioDeviceID, selector: AudioObjectPropertySelector, scope: AudioObjectPropertyScope, element: AudioObjectPropertyElement, default value: T) -> T {
    var address = AudioObjectPropertyAddress(mSelector: selector, mScope: scope, mElement: element)
    var result = value
    var size = UInt32(MemoryLayout<T>.size)
    withUnsafeMutablePointer(to: &result) { pointer in
        _ = AudioObjectGetPropertyData(device, &address, 0, nil, &size, pointer)
    }
    return result
}

func deviceName(_ device: AudioDeviceID) -> String {
    var address = AudioObjectPropertyAddress(mSelector: kAudioObjectPropertyName, mScope: kAudioObjectPropertyScopeGlobal, mElement: kAudioObjectPropertyElementMain)
    var name: Unmanaged<CFString>?
    var size = UInt32(MemoryLayout<Unmanaged<CFString>?>.size)
    let status = withUnsafeMutablePointer(to: &name) { AudioObjectGetPropertyData(device, &address, 0, nil, &size, $0) }
    guard status == noErr, let name else { return "<unnamed>" }
    return name.takeUnretainedValue() as String
}

func deviceUID(_ device: AudioDeviceID) -> String? {
    var address = AudioObjectPropertyAddress(mSelector: kAudioDevicePropertyDeviceUID, mScope: kAudioObjectPropertyScopeGlobal, mElement: kAudioObjectPropertyElementMain)
    var uid: Unmanaged<CFString>?
    var size = UInt32(MemoryLayout<Unmanaged<CFString>?>.size)
    let status = withUnsafeMutablePointer(to: &uid) { AudioObjectGetPropertyData(device, &address, 0, nil, &size, $0) }
    guard status == noErr, let uid else { return nil }
    return uid.takeUnretainedValue() as String
}

func listDevices() throws -> [DeviceDescription] {
    var address = AudioObjectPropertyAddress(mSelector: kAudioHardwarePropertyDevices, mScope: kAudioObjectPropertyScopeGlobal, mElement: kAudioObjectPropertyElementMain)
    var size: UInt32 = 0
    var status = AudioObjectGetPropertyDataSize(AudioObjectID(kAudioObjectSystemObject), &address, 0, nil, &size)
    guard status == noErr else { throw AudioToolError.coreAudio("device list size failed: \(status)") }
    let count = Int(size) / MemoryLayout<AudioDeviceID>.size
    var ids = Array(repeating: AudioDeviceID(0), count: count)
    status = AudioObjectGetPropertyData(AudioObjectID(kAudioObjectSystemObject), &address, 0, nil, &size, &ids)
    guard status == noErr else { throw AudioToolError.coreAudio("device list failed: \(status)") }
    let defaultIn = property(AudioObjectID(kAudioObjectSystemObject), selector: kAudioHardwarePropertyDefaultInputDevice, scope: kAudioObjectPropertyScopeGlobal, element: kAudioObjectPropertyElementMain, default: AudioDeviceID(0))
    let defaultOut = property(AudioObjectID(kAudioObjectSystemObject), selector: kAudioHardwarePropertyDefaultOutputDevice, scope: kAudioObjectPropertyScopeGlobal, element: kAudioObjectPropertyElementMain, default: AudioDeviceID(0))
    return ids.map { id in
        let inputs = property(id, selector: kAudioDevicePropertyStreamConfiguration, scope: kAudioObjectPropertyScopeInput, element: kAudioObjectPropertyElementMain, default: AudioBufferList(mNumberBuffers: 0, mBuffers: AudioBuffer(mNumberChannels: 0, mDataByteSize: 0, mData: nil))).mNumberBuffers
        let outputs = property(id, selector: kAudioDevicePropertyStreamConfiguration, scope: kAudioObjectPropertyScopeOutput, element: kAudioObjectPropertyElementMain, default: AudioBufferList(mNumberBuffers: 0, mBuffers: AudioBuffer(mNumberChannels: 0, mDataByteSize: 0, mData: nil))).mNumberBuffers
        return DeviceDescription(id: id, name: deviceName(id), inputChannels: inputs, outputChannels: outputs, isDefaultInput: id == defaultIn, isDefaultOutput: id == defaultOut)
    }
}

func writeWav(_ samples: [Int16], sampleRate: Int, path: String) throws {
    guard sampleRate > 0 else { throw AudioToolError.codec("sample rate must be positive") }
    guard samples.count <= (Int(UInt32.max) - 36) / 2 else { throw AudioToolError.codec("PCM16 WAV exceeds RIFF's 32-bit data extent") }
    var data = Data()
    func appendLE<T: FixedWidthInteger>(_ value: T) { var x = value.littleEndian; withUnsafeBytes(of: &x) { data.append(contentsOf: $0) } }
    let bytes = UInt32(samples.count * 2)
    data.append(contentsOf: Array("RIFF".utf8)); appendLE(UInt32(36) + bytes); data.append(contentsOf: Array("WAVEfmt ".utf8)); appendLE(UInt32(16)); appendLE(UInt16(1)); appendLE(UInt16(1)); appendLE(UInt32(sampleRate)); appendLE(UInt32(sampleRate * 2)); appendLE(UInt16(2)); appendLE(UInt16(16)); data.append(contentsOf: Array("data".utf8)); appendLE(bytes)
    for sample in samples { appendLE(sample) }
    try data.write(to: URL(fileURLWithPath: path), options: .withoutOverwriting)
}

func jsonData<T: Encodable>(_ value: T) throws -> Data { try JSONEncoder.pretty().encode(value) }
extension JSONEncoder { static func pretty() -> JSONEncoder { let e = JSONEncoder(); e.outputFormatting = [.prettyPrinted, .sortedKeys]; return e } }

func refuseExistingOutput(_ path: String, label: String) throws {
    guard !FileManager.default.fileExists(atPath: path) else {
        throw AudioToolError.usage("\(label) already exists; choose a new output path: \(path)")
    }
}

func usage() {
    print("holonics-audio — bounded macOS audio apparatus\n\nUsage:\n  holonics-audio devices\n  holonics-audio self-test-wav\n  holonics-audio capture --seconds N --wav OUT.wav --receipt OUT.json [--max-memory-mib M]\n  holonics-audio playback --wav IN.wav --receipt OUT.json\n\nCapture is finite and explicit. SIGINT/SIGTERM and AVAudioEngine route changes stop cleanly with a partial WAV and completed=false receipt. No learner, VAD, segmentation, template, or native current is created.")
}

final class AudioStopController {
    private let lock = NSLock()
    private let semaphore = DispatchSemaphore(value: 0)
    private(set) var reason: String?

    func request(_ reason: String) {
        lock.lock()
        guard self.reason == nil else { lock.unlock(); return }
        self.reason = reason
        lock.unlock()
        semaphore.signal()
    }

    @discardableResult
    func wait(timeout: DispatchTime) -> Bool { semaphore.wait(timeout: timeout) == .success }
}

func installAudioStops(_ controller: AudioStopController) -> (NSObjectProtocol, [DispatchSourceSignal]) {
    let notification = NotificationCenter.default.addObserver(
        forName: .AVAudioEngineConfigurationChange,
        object: nil,
        queue: nil
    ) { _ in controller.request("AVAudioEngineConfigurationChange: route/device configuration changed; capture stopped") }
    signal(SIGINT, SIG_IGN)
    signal(SIGTERM, SIG_IGN)
    let sources = [SIGINT, SIGTERM].map { signalNumber in
        let source = DispatchSource.makeSignalSource(signal: signalNumber, queue: .global(qos: .userInitiated))
        source.setEventHandler { controller.request(signalNumber == SIGINT ? "SIGINT: operator requested audio stop" : "SIGTERM: process termination requested") }
        source.resume()
        return source
    }
    return (notification, sources)
}

func removeAudioStops(_ token: (NSObjectProtocol, [DispatchSourceSignal])) {
    NotificationCenter.default.removeObserver(token.0)
    for source in token.1 { source.cancel() }
    signal(SIGINT, SIG_DFL)
    signal(SIGTERM, SIG_DFL)
}

func capture(seconds: Double, wav: String, receiptPath: String, maxMemoryMiB: Double) throws {
    guard seconds > 0, seconds.isFinite else { throw AudioToolError.usage("--seconds must be finite and positive") }
    guard maxMemoryMiB > 0, maxMemoryMiB.isFinite else { throw AudioToolError.usage("--max-memory-mib must be finite and positive") }
    try refuseExistingOutput(wav, label: "capture WAV output")
    try refuseExistingOutput(receiptPath, label: "capture receipt output")
    let engine = AVAudioEngine()
    let input = engine.inputNode
    let format = input.inputFormat(forBus: 0)
    let inputDevice = property(AudioObjectID(kAudioObjectSystemObject), selector: kAudioHardwarePropertyDefaultInputDevice, scope: kAudioObjectPropertyScopeGlobal, element: kAudioObjectPropertyElementMain, default: AudioDeviceID(0))
    guard format.sampleRate > 0, format.channelCount > 0 else { throw AudioToolError.capture("no input format; grant microphone access and select an input device") }
    let projectedBytes = seconds * format.sampleRate * 2.0
    // The collector and final RIFF Data coexist during publication; reserve a conservative
    // threefold working-set estimate rather than bounding only the final sample vector.
    guard projectedBytes * 3.0 <= maxMemoryMiB * 1024.0 * 1024.0 else {
        throw AudioToolError.capture("capture refused before device start: projected PCM/receipt/RIFF working set exceeds the explicit \(maxMemoryMiB) MiB in-memory budget")
    }
    let collector = CaptureCollector()
    let stop = AudioStopController()
    let stopToken = installAudioStops(stop)
    input.installTap(onBus: 0, bufferSize: 1024, format: format) { buffer, time in collector.append(buffer, time: time) }
    do {
        try engine.start()
    } catch {
        input.removeTap(onBus: 0)
        let failure = AudioReceipt(schema: "holonics.audio.exterior-receipt.v1", operation: "capture", deviceName: deviceName(inputDevice), deviceUID: deviceUID(inputDevice), sampleRate: format.sampleRate, channelCount: format.channelCount, hardwareFormat: format.commonFormat == .pcmFormatFloat32 ? "float32" : format.commonFormat == .pcmFormatInt16 ? "int16" : "native-\(format.commonFormat.rawValue)", outputFormat: "mono-signed-pcm16-wav", hostClock: "mach_absolute_time", buffers: [], totalFrames: 0, droppedFrames: 0, lateBuffers: nil, overflowBuffers: nil, gapFrames: 0, clippingSamples: 0, refusedSamples: 0, timestampRefusedFrames: 0, conversionLoss: "no PCM conversion occurred", permission: "capture refused: \(error)", captureStartHostTime: nil, captureEndHostTime: nil, playbackStartHostTime: nil, playbackEndHostTime: nil, playbackScheduledFileFrames: nil, playbackScheduledSampleRate: nil, playbackScheduledSampleStart: nil, playbackScheduledSampleEnd: nil, playbackPlayedFrames: nil, completed: false, terminationReason: "capture start refused")
        try? jsonData(failure).write(to: URL(fileURLWithPath: receiptPath), options: .withoutOverwriting)
        removeAudioStops(stopToken)
        throw AudioToolError.permission("audio input could not start (microphone permission or device unavailable): \(error)")
    }
    DispatchQueue.global(qos: .utility).asyncAfter(deadline: .now() + seconds) { stop.request("finite capture duration elapsed") }
    stop.wait(timeout: .now() + seconds + 1)
    engine.stop(); input.removeTap(onBus: 0)
    removeAudioStops(stopToken)
    try writeWav(collector.pcm, sampleRate: Int(format.sampleRate.rounded()), path: wav)
    let hardwareFormat = format.commonFormat == .pcmFormatFloat32 ? "float32" : format.commonFormat == .pcmFormatInt16 ? "int16" : "native-\(format.commonFormat.rawValue)"
    let reason = stop.reason ?? "capture ended without a terminal reason"
    let receipt = AudioReceipt(schema: "holonics.audio.exterior-receipt.v1", operation: "capture", deviceName: deviceName(inputDevice), deviceUID: deviceUID(inputDevice), sampleRate: format.sampleRate, channelCount: format.channelCount, hardwareFormat: hardwareFormat, outputFormat: "mono-signed-pcm16-wav", hostClock: "mach_absolute_time", buffers: collector.buffers, totalFrames: collector.totalFrames, droppedFrames: collector.droppedFrames, lateBuffers: nil, overflowBuffers: nil, gapFrames: collector.gapFrames, clippingSamples: collector.clipping, refusedSamples: collector.refused, timestampRefusedFrames: collector.timestampRefusedFrames, conversionLoss: "channel averaging and PCM16 quantization are cold exterior conversion; clipping/refusal counts are retained", permission: "capture started successfully", captureStartHostTime: collector.startHost, captureEndHostTime: collector.endHost, playbackStartHostTime: nil, playbackEndHostTime: nil, playbackScheduledFileFrames: nil, playbackScheduledSampleRate: nil, playbackScheduledSampleStart: nil, playbackScheduledSampleEnd: nil, playbackPlayedFrames: nil, completed: reason == "finite capture duration elapsed", terminationReason: reason)
    try jsonData(receipt).write(to: URL(fileURLWithPath: receiptPath), options: .withoutOverwriting)
}

func formatDescription(_ format: AVAudioFormat) -> String {
    let kind: String
    switch format.commonFormat {
    case .pcmFormatFloat32: kind = "float32"
    case .pcmFormatFloat64: kind = "float64"
    case .pcmFormatInt16: kind = "int16"
    case .pcmFormatInt32: kind = "int32"
    default: kind = "native-\(format.commonFormat.rawValue)"
    }
    return "\(kind) \(format.sampleRate)Hz \(format.channelCount)ch \(format.isInterleaved ? "interleaved" : "noninterleaved")"
}

func optionalDeviceName(_ device: AudioDeviceID) -> String? { device == 0 ? nil : deviceName(device) }
func optionalDeviceUID(_ device: AudioDeviceID) -> String? { device == 0 ? nil : deviceUID(device) }

func playback(wav: String, receiptPath: String) throws {
    try refuseExistingOutput(receiptPath, label: "playback receipt output")
    let file = try AVAudioFile(forReading: URL(fileURLWithPath: wav))
    let outputDevice = property(AudioObjectID(kAudioObjectSystemObject), selector: kAudioHardwarePropertyDefaultOutputDevice, scope: kAudioObjectPropertyScopeGlobal, element: kAudioObjectPropertyElementMain, default: AudioDeviceID(0))
    let engine = AVAudioEngine()
    let player = AVAudioPlayerNode()
    engine.attach(player)
    let outputFormat = engine.outputNode.outputFormat(forBus: 0)
    engine.connect(player, to: engine.mainMixerNode, format: file.processingFormat)
    let stop = AudioStopController()
    let stopToken = installAudioStops(stop)
    player.scheduleFile(file, at: nil, completionCallbackType: .dataPlayedBack) { _ in
        stop.request("finite playback player completion (dataPlayedBack)")
    }
    var playbackStart: UInt64?
    do {
        try engine.start()
        player.play()
        playbackStart = mach_absolute_time()
    } catch {
        player.stop(); engine.stop(); removeAudioStops(stopToken)
        let failure = AudioReceipt(schema: "holonics.audio.exterior-receipt.v1", operation: "playback", deviceName: optionalDeviceName(outputDevice), deviceUID: optionalDeviceUID(outputDevice), sampleRate: file.fileFormat.sampleRate, channelCount: file.fileFormat.channelCount, hardwareFormat: formatDescription(file.processingFormat), outputFormat: formatDescription(outputFormat), hostClock: "mach_absolute_time", buffers: [], totalFrames: UInt64(file.length), droppedFrames: nil, lateBuffers: nil, overflowBuffers: nil, gapFrames: nil, clippingSamples: nil, refusedSamples: nil, timestampRefusedFrames: nil, conversionLoss: "AVAudioFile/device conversion is exterior; source WAV remains unchanged", permission: "playback refused: \(error)", captureStartHostTime: nil, captureEndHostTime: nil, playbackStartHostTime: nil, playbackEndHostTime: nil, playbackScheduledFileFrames: UInt64(file.length), playbackScheduledSampleRate: file.fileFormat.sampleRate, playbackScheduledSampleStart: 0, playbackScheduledSampleEnd: Double(file.length), playbackPlayedFrames: nil, completed: false, terminationReason: "playback start refused")
        try? jsonData(failure).write(to: URL(fileURLWithPath: receiptPath), options: .withoutOverwriting)
        throw AudioToolError.capture("playback could not start: \(error)")
    }
    let playbackSeconds = Double(file.length) / file.fileFormat.sampleRate
    if stop.wait(timeout: .now() + playbackSeconds + 30) == false {
        stop.request("finite playback timeout; output stopped")
    }
    player.stop(); engine.stop(); removeAudioStops(stopToken)
    let reason = stop.reason ?? "playback stopped without a terminal reason"
    let completed = reason == "finite playback player completion (dataPlayedBack)"
    let receipt = AudioReceipt(schema: "holonics.audio.exterior-receipt.v1", operation: "playback", deviceName: optionalDeviceName(outputDevice), deviceUID: optionalDeviceUID(outputDevice), sampleRate: file.fileFormat.sampleRate, channelCount: file.fileFormat.channelCount, hardwareFormat: formatDescription(file.processingFormat), outputFormat: formatDescription(outputFormat), hostClock: "mach_absolute_time", buffers: [], totalFrames: UInt64(file.length), droppedFrames: nil, lateBuffers: nil, overflowBuffers: nil, gapFrames: nil, clippingSamples: nil, refusedSamples: nil, timestampRefusedFrames: nil, conversionLoss: "AVAudioFile/device conversion is exterior; source WAV remains unchanged", permission: "playback started successfully", captureStartHostTime: nil, captureEndHostTime: nil, playbackStartHostTime: playbackStart, playbackEndHostTime: mach_absolute_time(), playbackScheduledFileFrames: UInt64(file.length), playbackScheduledSampleRate: file.fileFormat.sampleRate, playbackScheduledSampleStart: 0, playbackScheduledSampleEnd: Double(file.length), playbackPlayedFrames: completed ? UInt64(file.length) : nil, completed: completed, terminationReason: reason + (completed ? "; dataPlayedBack callback confirms player playback completion, DAC output timestamp unavailable" : "; played frame count unknown after interruption/timeout"))
    try jsonData(receipt).write(to: URL(fileURLWithPath: receiptPath), options: .withoutOverwriting)
}

func selfTestWav() throws {
    let path = FileManager.default.temporaryDirectory.appendingPathComponent("holonics-audio-self-test-\(UUID().uuidString).wav")
    defer { try? FileManager.default.removeItem(at: path) }
    let expected: [Int16] = [Int16.min, -1, 0, 1, Int16.max]
    try writeWav(expected, sampleRate: 16_000, path: path.path)
    let bytes = try Data(contentsOf: path)
    guard bytes.count == 44 + expected.count * 2,
          String(decoding: bytes[0..<4], as: UTF8.self) == "RIFF",
          String(decoding: bytes[8..<12], as: UTF8.self) == "WAVE",
          String(decoding: bytes[36..<40], as: UTF8.self) == "data" else {
        throw AudioToolError.codec("synthetic WAV container metadata did not round-trip")
    }
    for index in expected.indices {
        let at = 44 + index * 2
        let word = UInt16(bytes[at]) | (UInt16(bytes[at + 1]) << 8)
        guard Int16(bitPattern: word) == expected[index] else { throw AudioToolError.codec("synthetic WAV sample mismatch at \(index)") }
    }
    print("synthetic WAV round-trip passed: \(expected.count) mono PCM16 samples at 16000 Hz")
}

@main
struct HolonicsAudioMain {
    static func main() {
        do {
            let args = Array(CommandLine.arguments.dropFirst())
            guard let command = args.first else { usage(); return }
            switch command {
            case "--help", "help": usage()
            case "devices":
                for device in try listDevices() { print(try String(data: jsonData(device), encoding: .utf8)!) }
            case "self-test-wav":
                try selfTestWav()
            case "capture":
                guard let secondsAt = args.firstIndex(of: "--seconds"), secondsAt + 1 < args.count, let seconds = Double(args[secondsAt + 1]), let wavAt = args.firstIndex(of: "--wav"), wavAt + 1 < args.count, let receiptAt = args.firstIndex(of: "--receipt"), receiptAt + 1 < args.count else { throw AudioToolError.usage("capture requires --seconds N --wav OUT.wav --receipt OUT.json") }
                let maxMemoryMiB: Double
                if let memoryAt = args.firstIndex(of: "--max-memory-mib") {
                    guard memoryAt + 1 < args.count, let value = Double(args[memoryAt + 1]) else { throw AudioToolError.usage("--max-memory-mib requires a finite positive number") }
                    maxMemoryMiB = value
                } else {
                    maxMemoryMiB = 512
                }
                try capture(seconds: seconds, wav: args[wavAt + 1], receiptPath: args[receiptAt + 1], maxMemoryMiB: maxMemoryMiB)
            case "playback":
                guard let wavAt = args.firstIndex(of: "--wav"), wavAt + 1 < args.count, let receiptAt = args.firstIndex(of: "--receipt"), receiptAt + 1 < args.count else { throw AudioToolError.usage("playback requires --wav IN.wav --receipt OUT.json") }
                try playback(wav: args[wavAt + 1], receiptPath: args[receiptAt + 1])
            default: throw AudioToolError.usage("unknown command \(command)")
            }
        } catch { fputs("holonics-audio: \(error)\n", stderr); exit(1) }
    }
}
