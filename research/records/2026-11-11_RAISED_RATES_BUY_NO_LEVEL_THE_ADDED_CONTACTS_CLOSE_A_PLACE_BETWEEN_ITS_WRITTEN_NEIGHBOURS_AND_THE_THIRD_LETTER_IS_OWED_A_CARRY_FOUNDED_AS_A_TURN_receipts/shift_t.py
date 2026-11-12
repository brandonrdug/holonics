"""shift_t.py OUT HEAD SIXTEENTHS: a ruler on the host (never machinery; integers only) for G108, the circles' reach. OUT is HEAD with every carry
circle's leak bias moved by SIXTEENTHS/16 on the leak's log chart: the bias l_b, the second half of carry_bias (C entries on the face's grain
2^-16, after the C turn biases), gains SIXTEENTHS * 2^12, so that every site's leak read l = L r + l_b moves by SIXTEENTHS/16 and its friction
d = d0 2^l is multiplied by 2^(SIXTEENTHS/16) at every site of every circle (the field's carry_friction). Every other entry and every other line
is HEAD's. OUT is a ruler's state: it is read, and no lap trains from it. The layout is read through tools/state_travel.py (the directory in
HOLONICS_TOOLS, default tools). One thread; writes OUT only, and refuses an existing OUT."""
import os
import sys

sys.path.insert(0, os.environ.get("HOLONICS_TOOLS", "tools"))
import state_travel

out, head, sixteenths = sys.argv[1], sys.argv[2], int(sys.argv[3])
lines = open(head).read().split("\n")
assert lines[0].split(" ")[0] == "hnn-field-learner-v3" and lines[0].split(" ")[4] == "-", "a learner's text with no held step"
d, theta = state_travel.state(head)
fam, total = state_travel.layout(d)
assert total == len(theta), "a state of its declaration"
c = d["carry"]
assert c > 0, "a field with no carry circles has no leak to move"
at = {name: start for name, start, shape, grain in fam}
start = at["carry_bias"] + c  # the leak half: after the C turn biases
step = sixteenths << 12  # SIXTEENTHS/16 of one on the face's grain 2^-16
before = [int(x) for x in theta[start:start + c]]
after = [x + step for x in before]
assert all(-(1 << 31) <= x < (1 << 31) for x in after), "the material's 32-bit carrier"
words = lines[2].split(" ")
assert len(words) == total
for k in range(c):
    words[start + k] = str(after[k])
lines[2] = " ".join(words)
with open(out, "x") as f:
    f.write("\n".join(lines))
print(f"STATE_SHIFT family=carry_bias/leak entries={c} start={start} step={step} (2^-16; the friction times 2^({sixteenths}/16)) "
      f"leak_bias_before={min(before)}..{max(before)} after={min(after)}..{max(after)} of={total}")
