"""Toy checks for the F5 exterior situated-context extractor."""

import io
import json
import tempfile
import unittest
from pathlib import Path

from f5_context import (ContextRefusal, _refusal_packet, extract_one, load_incidence,
                        parse_coordinates)


def occurrence(index, cells, parent=None, state="earlier", port="human", channel="human"):
    relations = [] if parent is None else [{
        "kind": "provider-parent", "state": state,
        **({"occurrence": parent} if state == "earlier" else {"event": 9000 + index}),
    }]
    return {
        "occurrence": index,
        "conversation": 7,
        "port": port,
        "parts": [{"channel": channel, "letter": "turn", "cells": list(cells)}],
        "relations": relations,
    }


class TrackingReader(io.BytesIO):
    def __init__(self, data):
        super().__init__(data)
        self.read_ranges = []

    def read(self, size=-1):
        start = self.tell() // 2
        raw = super().read(size)
        self.read_ranges.append((start, start + len(raw) // 2))
        return raw


def u16_cells(cells):
    return b"".join(int(cell).to_bytes(2, "little") for cell in cells)


class F5ContextTests(unittest.TestCase):
    def test_parent_branch_keeps_only_request_ancestry_and_exact_coordinates(self):
        # Section letters occupy cells 4, 9 and 13. 0 is the shared
        # ancestor; 2 -> 0 and 3 -> 0 are distinct branches; request 4 follows
        # branch 2. The future response at 5 must not be read.
        rows = [
            occurrence(0, (0, 4), port="agent", channel="agent"),
            occurrence(1, (0, 1)),
            occurrence(2, (5, 9), parent=0, port="agent", channel="agent"),
            occurrence(3, (5, 9), parent=0),
            occurrence(4, (10, 13), parent=2),
            occurrence(5, (14, 20), parent=4, port="agent", channel="agent"),
        ]
        cells = list(b"root") + [256] + list(b"bran") + [256] + list(b"ask") + [256] + list(b"reply!")
        reader = TrackingReader(u16_cells(cells))
        packet = extract_one(rows, reader, request_occurrence=4,
                             source_cell_extent=21, context_cell_ceiling=14)
        self.assertEqual([row["occurrence"] for row in packet["causal_occurrences"]], [0, 2, 4])
        self.assertNotIn(3, [row["occurrence"] for row in packet["causal_occurrences"]])
        self.assertNotIn(5, packet)
        parts = [part for row in packet["causal_occurrences"] for part in row["parts"]]
        self.assertEqual([(part["occurrence"], part["port"], part["channel"], part["section"], part["cells"])
                          for part in parts], [
            (0, "agent", "agent", "turn", [0, 4]),
            (2, "agent", "agent", "turn", [5, 9]),
            (4, "human", "human", "turn", [10, 13]),
        ])
        self.assertEqual([part["text"] for part in parts], ["root", "bran", "ask"])
        self.assertEqual(reader.read_ranges, [(0, 4), (5, 9), (10, 13)])
        self.assertEqual(packet["context_cells"], 14)
        self.assertEqual(packet["status"], "context")

    def test_unresolved_parent_is_refused(self):
        rows = [occurrence(0, (0, 2), parent=None), occurrence(1, (2, 4), parent=0)]
        rows[1]["relations"] = [{"kind": "provider-parent", "state": "outside", "event": 44}]
        with self.assertRaisesRegex(ContextRefusal, "unresolved"):
            extract_one(rows, TrackingReader(u16_cells(b"abcd")), 1, 4, 5)

    def test_refusal_is_a_request_local_typed_packet(self):
        packet = _refusal_packet(12, ContextRefusal("causal parent chain exceeds ceiling"))
        self.assertEqual(packet, {
            "schema": "holonics.f5-request-context.v1",
            "status": "refused",
            "request_occurrence": 12,
            "refusal": {"type": "context-refusal", "reason": "causal parent chain exceeds ceiling"},
        })

    def test_cycle_and_context_over_ceiling_are_refused(self):
        cyclic = [occurrence(0, (0, 1), parent=1), occurrence(1, (1, 2), parent=0)]
        with self.assertRaisesRegex(ContextRefusal, "cyclic"):
            extract_one(cyclic, TrackingReader(u16_cells(b"ab")), 1, 2, 4)
        rows = [occurrence(0, (0, 2)), occurrence(1, (2, 4), parent=0)]
        reader = TrackingReader(u16_cells(b"abcd"))
        with self.assertRaisesRegex(ContextRefusal, "ceiling"):
            extract_one(rows, reader, 1, source_cell_extent=4, context_cell_ceiling=4)
        self.assertEqual(reader.read_ranges, [])

    def test_selector_coordinates_and_incidence_read_stop_before_response(self):
        response, request = parse_coordinates("5:4")
        self.assertEqual((response, request), (5, 4))
        self.assertEqual(parse_coordinates("3:1"), (3, 1))
        self.assertRaises(ContextRefusal, parse_coordinates, "4:5")
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "incidence.jsonl"
            rows = [occurrence(i, (i, i + 1)) for i in range(5)]
            # A selected response can precede another selected request. Its
            # row must be skipped before JSON decoding; line 5 is beyond the
            # greatest request ordinal and must not be parsed either.
            path.write_bytes(b"".join(json.dumps(row).encode() + b"\n" for row in rows[:3])
                             + b"selected response row must not be parsed\n"
                             + json.dumps(rows[4]).encode() + b"\n"
                             + b"line after greatest request must not be parsed\n")
            loaded = load_incidence(path, max_occurrence=request, excluded_occurrences={3})
            self.assertEqual(len(loaded), request + 1)
            self.assertIsNone(loaded[3])
            self.assertEqual(loaded[4]["occurrence"], 4)


if __name__ == "__main__":
    unittest.main()
