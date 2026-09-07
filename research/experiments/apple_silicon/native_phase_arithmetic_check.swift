import Foundation
import Metal

let device = MTLCreateSystemDefaultDevice()!
let queue = device.makeCommandQueue()!
let libraryPath = CommandLine.arguments.dropFirst().first ?? "/tmp/native_phase.metallib"
let library = try device.makeLibrary(URL: URL(fileURLWithPath: libraryPath))
let fn = library.makeFunction(name: "native_phase_arithmetic_probe")!
let pipeline = try device.makeComputePipelineState(function: fn)

func run(_ a: [Int64], _ b: [Int64]) -> ([Int64], UInt32) {
    let ab = device.makeBuffer(bytes: a, length: a.count * MemoryLayout<Int64>.stride)!
    let bb = device.makeBuffer(bytes: b, length: b.count * MemoryLayout<Int64>.stride)!
    let ob = device.makeBuffer(length: 5 * MemoryLayout<Int64>.stride)!
    let rb = device.makeBuffer(length: MemoryLayout<UInt32>.stride)!
    rb.contents().assumingMemoryBound(to: UInt32.self).pointee = 0
    let command = queue.makeCommandBuffer()!
    let encoder = command.makeComputeCommandEncoder()!
    encoder.setComputePipelineState(pipeline)
    encoder.setBuffer(ab, offset: 0, index: 0)
    encoder.setBuffer(bb, offset: 0, index: 1)
    encoder.setBuffer(ob, offset: 0, index: 2)
    encoder.setBuffer(rb, offset: 0, index: 3)
    encoder.dispatchThreads(MTLSize(width: 1, height: 1, depth: 1), threadsPerThreadgroup: MTLSize(width: 1, height: 1, depth: 1))
    encoder.endEncoding(); command.commit(); command.waitUntilCompleted()
    precondition(command.status == .completed, "probe command failed: \(command.status) \(command.error as Any)")
    let p = ob.contents().assumingMemoryBound(to: Int64.self)
    return ((0..<5).map { p[$0] }, rb.contents().assumingMemoryBound(to: UInt32.self).pointee)
}

let normal = run([12, 6, 84, 126, 0], [5, 7, 126, 7, 1])
precondition(normal.0[0] == 17 && normal.0[1] == 42 && normal.0[2] == 42 && normal.0[3] == 18 && normal.1 == 0, "normal arithmetic mismatch: \(normal)")
let overflow = run([Int64.max, Int64.max, 0, 1, 0], [1, 2, 1, 0, 1])
precondition(overflow.1 & 1 != 0 && overflow.1 & 2 != 0, "overflow/division refusal missing: \(overflow)")
let minCase = run([0, 1, 84, 7, Int64.min], [0, 1, 126, 2, 1])
precondition(minCase.1 & 1 != 0, "signed minimum carrier refusal missing: \(minCase)")
let minAdd = run([Int64.min, 1, 84, 7, 0], [0, 1, 126, 2, 1])
precondition(minAdd.0[0] == Int64.min && minAdd.1 == 0, "signed minimum add mismatch: \(minAdd)")
let minMul = run([0, Int64.min, 84, 7, 0], [0, 1, 126, 1, 1])
precondition(minMul.0[1] == Int64.min && minMul.1 == 0, "signed minimum multiply mismatch: \(minMul)")
let minDiv = run([0, 1, 84, Int64.min, 0], [0, 1, 126, 1, 1])
precondition(minDiv.0[3] == Int64.min && minDiv.1 == 0, "signed minimum division mismatch: \(minDiv)")

func runWide(_ a: [UInt32], _ b: [UInt32]) -> ([UInt32], UInt32) {
    let ab = device.makeBuffer(bytes: a, length: 4 * MemoryLayout<UInt32>.stride)!
    let bb = device.makeBuffer(bytes: b, length: 4 * MemoryLayout<UInt32>.stride)!
    let ob = device.makeBuffer(length: 12 * MemoryLayout<UInt32>.stride)!
    let rb = device.makeBuffer(length: MemoryLayout<UInt32>.stride)!
    rb.contents().assumingMemoryBound(to: UInt32.self).pointee = 0
    let command = queue.makeCommandBuffer()!
    let encoder = command.makeComputeCommandEncoder()!
    encoder.setComputePipelineState(try! device.makeComputePipelineState(function: library.makeFunction(name: "native_phase_wide_probe")!))
    encoder.setBuffer(ab, offset: 0, index: 0); encoder.setBuffer(bb, offset: 0, index: 1)
    encoder.setBuffer(ob, offset: 0, index: 2); encoder.setBuffer(rb, offset: 0, index: 3)
    encoder.dispatchThreads(MTLSize(width: 1, height: 1, depth: 1), threadsPerThreadgroup: MTLSize(width: 1, height: 1, depth: 1))
    encoder.endEncoding(); command.commit(); command.waitUntilCompleted()
    precondition(command.status == .completed, "wide probe command failed: \(command.status) \(command.error as Any)")
    let p = ob.contents().assumingMemoryBound(to: UInt32.self)
    return ((0..<12).map { p[$0] }, rb.contents().assumingMemoryBound(to: UInt32.self).pointee)
}

let wide = runWide([0, 0, 0, 0x40000000], [2, 0, 0, 0])
precondition(wide.1 & 1 != 0, "2^126 * 2 did not refuse at 2^127: \(wide)")
let earlyShift = runWide([0, 0, 0, 0x40000000], [8, 0, 0, 0])
precondition(earlyShift.1 == 1, "2^126 * 8 did not refuse only carrier overflow: \(earlyShift)")
let boundary = runWide([0xffff_ffff, 0xffff_ffff, 0xffff_ffff, 0x7fff_ffff], [1, 0, 0, 0])
precondition(boundary.1 == 0 && boundary.0[0] == 0xffff_ffff && boundary.0[1] == 0xffff_ffff && boundary.0[2] == 0xffff_ffff && boundary.0[3] == 0x7fff_ffff, "127-bit boundary mismatch: \(boundary)")
let limbCarry = runWide([0xffff_ffff, 0, 0, 0], [0xffff_ffff, 0, 0, 0])
precondition(limbCarry.1 == 0 && limbCarry.0[0] == 1 && limbCarry.0[1] == 0xffff_fffe, "limb carry mismatch: \(limbCarry)")
let maxLimbs = runWide([0xffff_ffff, 0xffff_ffff, 0, 0], [0xffff_ffff, 0xffff_ffff, 0, 0])
precondition(maxLimbs.1 & 1 != 0, "wide max-limb overflow missing: \(maxLimbs)")
let wideExact = runWide([0, 0x80000000, 0, 0], [0, 0x80000000, 0, 0])
precondition(wideExact.1 == 0 && wideExact.0[0] == 0 && wideExact.0[1] == 0 && wideExact.0[2] == 0 && wideExact.0[3] == 0x40000000, "2^63 square mismatch: \(wideExact)")
let wideGcdDiv = runWide([0, 0, 3, 0], [0, 3, 0, 0])
precondition(wideGcdDiv.1 == 0 && wideGcdDiv.0[4] == 0 && wideGcdDiv.0[5] == 3 && wideGcdDiv.0[6] == 0 && wideGcdDiv.0[7] == 0 && wideGcdDiv.0[8] == 0 && wideGcdDiv.0[9] == 1 && wideGcdDiv.0[10] == 0 && wideGcdDiv.0[11] == 0, "wide gcd/division mismatch: \(wideGcdDiv)")

struct WideCase: Codable {
    let a: [UInt32]; let b: [UInt32]; let flags: UInt32
    let product: [UInt32]; let gcd: [UInt32]; let quotient: [UInt32]
}
let casesPath = CommandLine.arguments.dropFirst(2).first ?? "research/experiments/apple_silicon/wide_cases.json"
let cases = try JSONDecoder().decode([WideCase].self, from: Data(contentsOf: URL(fileURLWithPath: casesPath)))
precondition(cases.count == 248, "expected 248 generated wide and carrier-boundary cases")
for (index, test) in cases.enumerated() {
    let result = runWide(test.a, test.b)
    precondition(result.1 == test.flags, "wide case \(index) refusal mismatch: \(result.1) vs \(test.flags)")
    if test.flags == 0 {
        precondition(Array(result.0[0..<4]) == test.product && Array(result.0[4..<8]) == test.gcd && Array(result.0[8..<12]) == test.quotient, "wide case \(index) result mismatch: \(result)")
    }
}
print("native phase arithmetic probe passed: normal=\(normal.0), overflowFlags=\(overflow.1), minFlags=\(minCase.1), wideFlags=\(wide.1), earlyShiftFlags=\(earlyShift.1), boundaryFlags=\(boundary.1)")
print("exact generated cases checked: \(cases.count)")
