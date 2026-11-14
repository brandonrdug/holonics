"""strip_mark: a marked field's state with its mark removed (plumbing; the inverse of Field::with_mark on the state file).

usage: python3 -I strip_mark.py SRC DST
The fine field's head v14m becomes v14g (its mark and junction words dropped; refused unless junction is 0 and mark 1), the three
strengths at the end of the fine material are dropped from the material and from both moment lines, and the mark part's rate (the
parts line's last entry) is dropped. Every other line is kept byte for byte. Checked by reading: the stripped state's read-cavity
equals read 1's (the marked state with its strengths zeroed) on every row.
"""
import sys

src, dst = sys.argv[1], sys.argv[2]
lines = open(src).read().split('\n')
assert lines[0].startswith('hnn-field-learner-v3 ')
head = lines[1].split(' ')
assert head[0] == 'hnn-field-v14m' and len(head) == 17 and head[15] == '0' and head[16] == '1', head
fine = int(0)
theta = lines[2].split(' ')
fine = len(theta)
assert lines[3].startswith('level ') and lines[4].startswith('hnn-field-v14 ')
lines[1] = ' '.join(['hnn-field-v14g'] + head[1:15])
lines[2] = ' '.join(theta[:-3])
for k in (7, 8):
    m = lines[k].split(' ')
    assert len(m) == fine + len(lines[5].split(' ')) + len(lines[6].split(' ')), (k, len(m))
    lines[k] = ' '.join(m[:fine - 3] + m[fine:])
parts = lines[9].split(' ')
assert parts[0] == 'parts' and len(parts) == 26, len(parts)
lines[9] = ' '.join(parts[:-1])
open(dst, 'w').write('\n'.join(lines))
print('stripped', src, '->', dst, 'fine', fine, '->', fine - 3)
