#!/usr/bin/env python3
"""Exterior capture of the bounded synthetic contextual control's typed stdout.

Usage: python3 tools/capture_contextual_receipts.py CONTROL_LOG NEW_OUTPUT_DIRECTORY
No model, dataset, observation or machinery execution occurs here.
"""
import argparse
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('log', type=Path)
p.add_argument('output', type=Path)
a = p.parse_args()
text = a.log.read_text()
packets = {}
for marker, name in [
    ('ORIGINAL', 'ORIGINAL_PRODUCING_AND_ACTUAL_PENDING.state'),
    ('LEARNED', 'LEARNED_MATERIAL.state'),
    ('NATIVE', 'INSPECTABLE_NATIVE_FUTURE.txt'),
    ('MEASUREMENT', 'MEASURED_SCOPE.json'),
]:
    begin = 'CONTEXTUAL_PACKET_' + marker + '_BEGIN\n'
    end = 'CONTEXTUAL_PACKET_' + marker + '_END'
    if text.count(begin) != 1 or text.count(end) != 1:
        p.error('Expected exactly one complete ' + marker + ' packet')
    at = text.index(begin) + len(begin)
    packets[name] = text[at:text.index(end, at)]
a.output.mkdir(parents=True, exist_ok=False)
for name, content in packets.items():
    with (a.output / name).open('x') as target:
        target.write(content)
print('Captured ' + str(len(packets)) + ' synthetic CODE packets')
