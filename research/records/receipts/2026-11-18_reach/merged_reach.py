#!/usr/bin/env -S python3 -I
"""The engine's items that no command of athena reaches, by the compiler's own dead-code reading (November 18).

  merged_reach.py REPO OUT    lay crates/engine, crates/engine-cuda and crates/athena out as one binary crate under OUT, with athena's
                              main as its root and every `pub` item made `pub(crate)`, so rustc's dead_code lint reads reach from main.

Then, from OUT: `cargo check --offline --all-features --message-format=json` (reach from the commands) and the same with `--tests`
(reach from the tests too). An item dead in the first and alive in the second is called by tests alone; dead in both, by nothing. The
card's kernel image is replaced by an empty slice, so nothing is linked or run. A host ruler: it reads the source and writes OUT only.
"""
import os, re, shutil, sys

repo, out = sys.argv[1], sys.argv[2]
src = os.path.join(out, "src")
shutil.rmtree(out, ignore_errors=True)
for crate, name in (("engine", "holonics_engine"), ("engine-cuda", "holonics_engine_cuda"), ("athena", "athena")):
    shutil.copytree(os.path.join(repo, "crates", crate, "src"), os.path.join(src, name))
    os.rename(os.path.join(src, name, "lib.rs"), os.path.join(src, name, "mod.rs"))
os.rename(os.path.join(src, "athena", "main.rs"), os.path.join(src, "main.rs"))
VIS = re.compile(r'\bpub(\s+)(?=(?:unsafe\s+|const\s+|async\s+|extern\s+"C"\s+)*(?:fn|struct|enum|const|static|type|trait|mod|use|union)\b)')
for d, _, files in os.walk(src):
    for f in files:
        if not f.endswith(".rs"):
            continue
        p = os.path.join(d, f)
        rel = os.path.relpath(p, src)
        crate = rel.split(os.sep)[0] if os.sep in rel else None
        s = open(p, encoding="utf-8").read()
        if crate:
            s = re.sub(r"\bcrate::", f"crate::{crate}::", s)
        for name in ("holonics_engine_cuda", "holonics_engine", "athena"):
            s = re.sub(rf"(?<![\w:]){name}::", f"crate::{name}::", s)
        s = re.sub(r"\buse holonics_engine(_cuda)?\b", r"use crate::holonics_engine\1", s)
        s = VIS.sub(r"pub(crate)\1", s)
        s = s.replace("#![allow(dead_code, ", "#![allow(")
        s = s.replace('include_bytes!(concat!(env!("OUT_DIR"), "/field.ptx"))', 'b""')
        open(p, "w", encoding="utf-8").write(s)
m = open(os.path.join(src, "main.rs"), encoding="utf-8").read()
open(os.path.join(src, "main.rs"), "w", encoding="utf-8").write(m.replace("\nuse ", "\nmod holonics_engine;\nmod holonics_engine_cuda;\nmod athena;\nuse ", 1))
open(os.path.join(out, "Cargo.toml"), "w").write(f"""[package]
name = "merged"
version = "0.0.0"
edition = "2024"
publish = false
[workspace]
[dependencies]
num-bigint = "0.4"
num-rational = "0.4"
num-traits = "0.2"
num-integer = "0.1"
thiserror = "2"
rayon = "1.12"
[features]
ruler-rows-reads = []
ruler-bits = []
certificate-check = []
[patch.crates-io]
num-bigint = {{ path = "{os.path.join(repo, 'vendor', 'num-bigint')}" }}
""")
