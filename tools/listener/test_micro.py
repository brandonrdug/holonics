"""Synthetic boundary controls only; no public dataset or learner is opened."""

import contextlib
import copy
import importlib.util
import io
import json
from pathlib import Path
import struct
import tempfile
import unittest
import wave
from unittest.mock import patch


SPEC = importlib.util.spec_from_file_location("micro", Path(__file__).with_name("micro.py"))
micro = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(micro)


def wav_bytes(samples, channels=1, width=2):
    output = io.BytesIO()
    with wave.open(output, "wb") as handle:
        handle.setnchannels(channels)
        handle.setsampwidth(width)
        handle.setframerate(16000)
        handle.writeframes(struct.pack(f"<{len(samples)}h", *samples))
    return output.getvalue()


def fixtures(root):
    def store(path, data, dataset, split):
        path = root / path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        return {"path": str(path.relative_to(root)), "dataset": dataset, "split": split, "sha256": micro.digest(data)}
    config = {
        "gsm8k": store("gsm8k/train.jsonl", b"\n".join(json.dumps({"answer": f"prefix <<{i}+2={i + 2}>> suffix <<9=9>>"}).encode() for i in range(4)), "GSM8K", "train"),
        "mnist_images": store("mnist/train-images-idx3-ubyte", struct.pack(">4I", 2051, 3, 3, 3) + bytes([255] * 27), "MNIST", "train"),
        "mnist_labels": store("mnist/train-labels-idx1-ubyte", struct.pack(">2I", 2049, 3) + bytes([7, 2, 9]), "MNIST", "train"),
        "librispeech": [],
    }
    for i in range(3):
        utterance = f"19-198-{i:04d}"
        # A complete long first half-cycle exercises length carries in maximal H.
        samples = [7] * 255 + [-8, 9, -10, 11, -12, 13, -14, 15]
        entry = store(f"LibriSpeech/train-clean-100/19/198/{utterance}.wav", wav_bytes(samples), "LibriSpeech", "train-clean-100")
        entry["utterance_id"] = utterance
        config["librispeech"].append(entry)
    return config


def read_frames(raw):
    """Independent reader for the exact existing raw HLSN1 contract."""
    assert raw.startswith(micro.MAGIC)
    at, sections = len(micro.MAGIC), []
    def take(n):
        nonlocal at
        result = raw[at:at + n]
        assert len(result) == n
        at += n
        return result
    def integer():
        return struct.unpack(">I", take(4))[0]
    while at < len(raw):
        assert integer() == 1
        kind = take(1)[0]
        if kind == 0:
            passage = take(integer())
        elif kind == 1:
            width, height = struct.unpack(">HH", take(4))
            passage = width, height, take(width * height)
        else:
            assert kind == 2
            rate, count = integer(), integer()
            passage = rate, list(struct.unpack(f">{count}h", take(2 * count)))
        target = take(integer())
        sections.append((kind, passage, target))
    return sections


class MicroControls(unittest.TestCase):
    def test_first_annotation_contents_split_at_its_equals_and_preserve_octets(self):
        self.assertEqual(micro.split_first_span("prefix << 7 / 2 = 3.5 >> tail <<8=8>>"), (b" 7 / 2 =", b" 3.5 "))
        for answer in ("no span", "<<1+2>> <<2=2>>", "<<1=2=3>>", "<<=2>>", "<<1=>>", "<<bad <<1=2>>"):
            with self.assertRaises(micro.Refusal):
                micro.split_first_span(answer)

    def test_stroke_matches_rust_signed_jump_and_fibre_witnesses(self):
        pixels = bytearray(15)
        for index, value in ((0, 1), (6, 2), (12, 3), (4, 4)):
            pixels[index] = value
        chart, fibre = micro.stroke(5, 3, pixels)
        self.assertEqual(chart, bytes([0x80, 0, 0, 0x11, 0x01, 0x82, 254, 2]))
        self.assertEqual(fibre, {"width": 5, "height": 3, "jumps": 2, "remainders": [0, 0, 1, 0]})
        self.assertEqual(micro.decode_stroke(chart, fibre), bytes(pixels))
        self.assertEqual(micro.cells(chart), 2 * 4 + 4 * 2 + 2)
        self.assertEqual(micro.stroke(2, 2, b"\0" * 4)[0], b"")
        with self.assertRaisesRegex(micro.Refusal, "overflow"):
            micro.stroke(129, 1, bytes(128) + b"\1")
        for value in range(1, 256):
            self.assertEqual(micro.decode_stroke(*micro.stroke(1, 1, bytes([value]))), bytes([value]))
        with self.assertRaises(micro.Refusal):
            micro.decode_stroke(chart, {**fibre, "remainders": []})

    def test_pcm_matches_rust_run_witnesses_and_reconstructs_exact_samples(self):
        samples = [0, 0, 3, 0, 2, -4, 0, -1, 5, 0]
        chart, fibre = micro.half_cycles(16000, samples)
        self.assertEqual(chart, bytes([2, 0x20, 3, 0x01, 3, 0x12, 2, 0x02]))
        self.assertEqual(micro.decode_half_cycles(chart, fibre), samples)
        for samples in ([], [0] * 255, [-32768], [32767], [1] * 255, [-1] * 256, [2] * 510):
            encoded = micro.half_cycles(16000, samples)
            self.assertEqual(micro.decode_half_cycles(*encoded), samples)
        self.assertEqual(micro.half_cycles(16000, [7] * 255)[0], b"\xff\0\2")
        self.assertEqual(micro.half_cycles(16000, [-32768])[0], b"\1\x1f")

    def test_fragment_chooses_largest_H_with_carries_and_both_end_letters(self):
        samples = [7] * 255 + [-8, 9, -10, 11, -12, 13]
        source, target, meta = micro.fragment(16000, samples, 24)
        self.assertEqual(meta["H"], 2)
        self.assertEqual(meta["source_sample_range"], [0, 256])
        self.assertEqual(meta["target_sample_range"], [256, 258])
        self.assertEqual(meta["combined_cells"], 22)
        self.assertEqual(meta["candidate_costs"], [{"H": 1, "combined_cells": 14}, {"H": 2, "combined_cells": 22}, {"H": 3, "combined_cells": 30}])
        self.assertEqual(micro.half_cycles(16000, samples[:258])[0], micro.half_cycles(16000, source)[0] + target)
        runs = micro.runs_of(samples)
        self.assertNotEqual(runs[1][2], runs[2][2])
        self.assertNotEqual(runs[3][2], runs[4][2])
        with self.assertRaises(micro.Refusal):
            micro.fragment(16000, samples, 13)

    def test_eof_is_not_a_sign_change_and_silence_is_heard_beside_H_signed_runs(self):
        with self.assertRaises(micro.Refusal):
            micro.fragment(16000, [1, -1], 100)
        source, target, metadata = micro.fragment(16000, [0, 1, -1, 2, -2, 3], 100)
        self.assertEqual(metadata["H"], 2)
        self.assertEqual(metadata["H_counts"], "signed_runs_only")
        self.assertEqual(metadata["leading_silence"], "heard_with_source")
        self.assertEqual(metadata["source_sample_range"], [0, 3])
        self.assertEqual(source, [0, 1, -1])
        self.assertEqual(len(metadata["source_fibre"]["runs"]), 3)
        self.assertEqual(len(metadata["target_fibre"]["runs"]), 2)
        self.assertEqual(micro.decode_half_cycles(target, metadata["target_fibre"]), [2, -2])
        _, _, bounded = micro.fragment(16000, [0, 1, -1, 2, -2, 3], 20)
        self.assertEqual((bounded["H"], bounded["combined_cells"]), (1, 16))
        for samples in ([], [0] * 12):
            with self.assertRaisesRegex(micro.Refusal, "no signed run"):
                micro.fragment(16000, samples, 100)

    def test_canonical_fibre_bytes_are_cross_language_golden_values(self):
        domain = b"holonics.listener.fibre.v1\0"
        self.assertEqual(micro.canonical_fibre(0, None), domain + b"\0")
        chart, fibre = micro.stroke(1, 1, b"\3")
        expected_raster = bytes.fromhex("01 0001 0001 0000000000000001 0000000000000001 01")
        self.assertEqual(micro.canonical_fibre(1, fibre), domain + expected_raster)
        chart, fibre = micro.half_cycles(16000, [-32768, 0])
        expected_pcm = bytes.fromhex("02 00003e80 0000000000000001 0000 0000000000000002 00000000 00008000")
        self.assertEqual(micro.canonical_fibre(2, fibre), domain + expected_pcm)
        summary = micro.chart_summary(0, b"abc", None)
        self.assertEqual(summary["chart_sha256"], "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")

    def test_binary_manifest_binds_every_repeated_source_chart_and_target(self):
        item = {"source_chart_summary": micro.chart_summary(0, b"abc", None), "target_octets": 1, "target_sha256": micro.digest(b"7")}
        raw = micro.chart_manifest([item])
        self.assertEqual(raw[:14], b"HLCM1\n" + bytes.fromhex("0000000000000003"))
        self.assertEqual(len(raw), 14 + 3 * 133)
        for index in range(3):
            start = 14 + index * 133
            self.assertEqual(raw[start:start + 8], index.to_bytes(8, "big"))
            self.assertEqual(raw[start + 8:start + 13], b"\0\0\0\1\0")
            self.assertEqual(raw[start + 13:start + 21], bytes.fromhex("0000000000000003"))
            self.assertEqual(raw[start + 21:start + 53], bytes.fromhex(item["source_chart_summary"]["chart_sha256"]))
            self.assertEqual(raw[start + 93:start + 101], bytes.fromhex("0000000000000001"))
            self.assertEqual(raw[start + 101:start + 133], bytes.fromhex(item["target_sha256"]))

    def test_stream_has_one_header_thirty_sections_and_three_identical_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            config = fixtures(root)
            with patch.object(micro.subprocess, "run", side_effect=AssertionError("synthetic WAV controls need no process")):
                stream, manifest = micro.build(config, root)
            decoded = read_frames(stream)
            self.assertEqual(len(decoded), 30)
            self.assertEqual([row[0] for row in decoded], [0, 1, 2, 0, 1, 2, 0, 1, 2, 0] * 3)
            self.assertEqual(decoded[:10], decoded[10:20])
            self.assertEqual(decoded[:10], decoded[20:])
            self.assertEqual(decoded[0], (0, b"0+2=", b"2"))
            self.assertEqual(decoded[1], (1, (3, 3, bytes([255] * 9)), b"7"))
            block_length = manifest["pass_block_bytes"]
            blocks = [stream[6 + i * block_length:6 + (i + 1) * block_length] for i in range(3)]
            self.assertEqual(len(stream), 6 + 3 * block_length)
            self.assertEqual([micro.digest(block) for block in blocks], manifest["pass_block_sha256"])
            self.assertEqual(micro.digest(stream), manifest["stream_sha256"])
            binary = micro.chart_manifest(manifest["items_per_pass"])
            self.assertEqual(micro.digest(binary), manifest["chart_manifest"]["sha256"])
            self.assertEqual(len(binary), manifest["chart_manifest"]["bytes"])
            self.assertNotIn("request_rough_ordinal_estimate", manifest)
            self.assertEqual(manifest["jumps_per_pass"], 3)
            self.assertEqual(manifest["delivered_cells_three_passes"], 3 * sum(item["source_cells"] + item["target_cells"] for item in manifest["items_per_pass"]))
            for i, item in enumerate(manifest["items_per_pass"]):
                if item["chart"] == "sound":
                    source = decoded[i][1][1]
                    self.assertEqual(micro.decode_half_cycles(micro.half_cycles(16000, source)[0], item["source_fibre"]), source)
                    self.assertEqual(len(micro.decode_half_cycles(decoded[i][2], item["target_fibre"])), 2)

    def test_pins_train_metadata_identity_paths_and_unique_utterances_are_enforced(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            original = fixtures(root)
            alterations = [
                ("gsm8k", "sha256", "0" * 64),
                ("gsm8k", "split", "test"),
                ("mnist_images", "dataset", "QMNIST"),
            ]
            for entry, key, value in alterations:
                config = copy.deepcopy(original)
                config[entry][key] = value
                with self.assertRaises(micro.Refusal):
                    micro.build(config, root)
            for key, value in [("split", "test-clean"), ("utterance_id", "19-198-9999")]:
                config = copy.deepcopy(original)
                config["librispeech"][0][key] = value
                with self.assertRaises(micro.Refusal):
                    micro.build(config, root)
            config = copy.deepcopy(original)
            config["librispeech"][1] = copy.deepcopy(config["librispeech"][0])
            with self.assertRaisesRegex(micro.Refusal, "distinct"):
                micro.build(config, root)
            path = root / original["librispeech"][0]["path"]
            with self.assertRaises(micro.Refusal):
                micro.sound_identity(original["librispeech"][0], path.parent.parent / path.name)

    def test_missing_flac_decoder_refuses_without_install_or_subprocess(self):
        with patch.object(micro.shutil, "which", return_value=None), patch.object(micro.subprocess, "run", side_effect=AssertionError("no install/decode")):
            with self.assertRaisesRegex(micro.Refusal, "decoder missing"):
                micro.audio_input(Path("19-198-0000.flac"), b"not decoded")
        with self.assertRaises(micro.Refusal):
            micro.wav_pcm(wav_bytes([1, -1], channels=2))

    def test_existing_flac_decoder_reads_pinned_bytes_without_conversion(self):
        samples = [-32768, 0, 32767]
        decoded = wav_bytes(samples)
        responses = [micro.subprocess.CompletedProcess([], 0, "flac synthetic version\n", ""), micro.subprocess.CompletedProcess([], 0, decoded, b"")]
        with patch.object(micro.shutil, "which", return_value="/synthetic/flac"), patch.object(micro.subprocess, "run", side_effect=responses) as run:
            rate, actual, decoder = micro.audio_input(Path("19-198-0000.flac"), b"synthetic-pinned-flac")
        self.assertEqual((rate, actual), (16000, samples))
        self.assertEqual(run.call_args_list[1].kwargs["input"], b"synthetic-pinned-flac")
        self.assertEqual(run.call_args_list[1].args[0], ["/synthetic/flac", "--decode", "--stdout", "--silent", "-"])
        self.assertEqual(decoder["decoded_wav_sha256"], micro.digest(decoded))

    def test_cli_keeps_artifacts_in_local_and_refuses_replacement(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            config = fixtures(root)
            inputs = root / "inputs.json"
            inputs.write_text(json.dumps(config))
            output = root / ".local" / "micro"
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(micro.main(["--inputs", str(inputs), "--out-dir", str(output)]), 0)
                original = (output / "micro.hlsn").read_bytes()
                self.assertEqual(micro.main(["--inputs", str(inputs), "--out-dir", str(output)]), 2)
                self.assertEqual(micro.main(["--inputs", str(inputs), "--out-dir", str(root / "public")]), 2)
            self.assertEqual((output / "micro.hlsn").read_bytes(), original)
            manifest = json.loads((output / "manifest.json").read_text())
            self.assertEqual(manifest["inputs_manifest_sha256"], micro.digest(inputs.read_bytes()))
            self.assertEqual(micro.digest((output / "micro.charts").read_bytes()), manifest["chart_manifest"]["sha256"])


if __name__ == "__main__":
    unittest.main()
