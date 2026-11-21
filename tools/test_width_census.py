#!/usr/bin/env python3
"""Controls of tools/width_census.py: each refusal is planted on a small tree and must be found, and the clean tree must pass.

A gate's pass means something only if the same check finds a planted violation (the guide's method rule 11).
"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
HOST = """pub const FACE_BITS: u32 = 16;
pub const MOVE_BITS: u32 = 30;
pub const LOCK_BITS: u32 = 2 * FACE_BITS + 1;
pub fn f(x: i128) -> i128 { (x << 20) >> 3 }
"""
KERNEL = """#define FACE_BITS 16
#define MOVE_BITS 30
"""
TABLE = """# ceiling picked 1
# ceiling carrier 1
# ceiling literal 0
# ceiling dead 0
# ceiling shifts engine 1
# ceiling shifts engine-cuda 0
# ceiling shifts athena 0
# ceiling tolerances engine 0
# ceiling tolerances engine-cuda 0
# ceiling tolerances athena 0
name\towner\tvalue\tclass\tneed
FACE_BITS\tcrates/engine/src/width.rs\t16\tpicked\tthe root
MOVE_BITS\tcrates/engine/src/width.rs\t30\tcarrier\tfits 32 bits
LOCK_BITS\tcrates/engine/src/width.rs\t33\tderived\ttwo faces and a place
FACE_BITS\tcrates/engine-cuda/kernels/field.cu\t16\ttwin\t= FACE_BITS @ crates/engine/src/width.rs
MOVE_BITS\tcrates/engine-cuda/kernels/field.cu\t30\ttwin\t= MOVE_BITS @ crates/engine/src/width.rs
"""


def tree(root, host=HOST, kernel=KERNEL, table=TABLE):
    for path, text in (('crates/engine/src/width.rs', host), ('crates/engine-cuda/kernels/field.cu', kernel),
                       ('crates/engine/WIDTHS.tsv', table), ('crates/athena/src/main.rs', 'fn main() {}\n')):
        full = os.path.join(root, path)
        os.makedirs(os.path.dirname(full), exist_ok=True)
        with open(full, 'w', encoding='utf-8') as f:
            f.write(text)


def run(**parts):
    with tempfile.TemporaryDirectory() as root:
        tree(root, **parts)
        done = subprocess.run([sys.executable, os.path.join(HERE, 'width_census.py'), '--root', root],
                              capture_output=True, text=True)
        return done.returncode, done.stdout


def main():
    failures = []

    def expect(name, code, out, want_code, want_text):
        if code != want_code or want_text not in out:
            failures.append(f'{name}: exit {code}, wanted {want_code} with `{want_text}`\n{out}')

    code, out = run()
    expect('the clean tree passes', code, out, 0, 'the table holds')
    code, out = run(host=HOST + 'pub const NEW_BITS: u32 = 12;\n')
    expect('a width with no row', code, out, 1, 'NEW_BITS = 12 sets a width and has no row')
    code, out = run(host=HOST.replace('= 16', '= 18'), kernel=KERNEL)
    expect('a width moved in its source alone', code, out, 1, 'the table says 16')
    code, out = run(kernel=KERNEL.replace('30', '31'), table=TABLE.replace('field.cu\t30', 'field.cu\t31'))
    expect("a kernel's twin off its host", code, out, 1, 'the two are one width')
    code, out = run(host=HOST.replace('2 * FACE_BITS + 1', '33'))
    expect('a derived width written as a bare number', code, out, 1, 'writes the bare literal')
    code, out = run(table=TABLE.replace('16\tpicked', '16\tguessed'))
    expect('an unknown class', code, out, 1, 'class `guessed`')
    code, out = run(table=TABLE.replace('30\tcarrier', '30\tpicked'))
    expect('a ceiling passed', code, out, 1, 'the ceilings only fall')
    code, out = run(table=TABLE.replace('ceiling picked 1', 'ceiling picked 2'))
    expect('a ceiling left above its count', code, out, 1, 'lower the ceiling to 1')
    code, out = run(host=HOST + 'pub fn g(x: i128) -> i128 { x << 34 }\n')
    expect('a new literal shift', code, out, 1, 'literal shifts of 8 places or more')
    code, out = run(table=TABLE + 'GONE_BITS\tcrates/engine/src/width.rs\t4\tpicked\tgone\n'.replace('picked', 'ruler'))
    expect('a row with no declaration', code, out, 1, 'no such declaration')
    code, out = run(table=TABLE.replace('the root', ''))
    expect('an empty need', code, out, 1, 'the need is empty')
    code, out = run(host=HOST + 'pub fn lattice(eps_bits: u32) -> u32 { eps_bits + 1 }\n')
    expect('a tolerance handed in by number', code, out, 1, 'hand a tolerance in by number')
    code, out = run(host=HOST + '/// a place counted for `2^(-eps_bits)` is a gauge\n')
    expect('a tolerance named in a comment alone', code, out, 0, 'the table holds')
    code, out = run(table=TABLE.replace('16\tpicked\tthe root', '16\treceiver\tthe store\'s spread').replace('ceiling picked 1', 'ceiling picked 0'))
    expect('a located width with no unit named', code, out, 1, 'names no unit')
    code, out = run(table=TABLE.replace('16\tpicked\tthe root', '16\treceiver\tunit:Lattice.places, the store\'s spread').replace('ceiling picked 1', 'ceiling picked 0'))
    expect('a located width with its unit named', code, out, 0, 'the table holds')
    for f in failures:
        print(f'width-census controls: {f}')
    print(f'width-census controls: {15 - len(failures)} of 15 hold')
    return 1 if failures else 0


if __name__ == '__main__':
    sys.exit(main())
