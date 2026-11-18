#!/usr/bin/env -S python3 -I
"""Controls for records_index.py: a file name's words read as a title, a directory of known entries indexed by month with its receipts
directories counted, an index on disk told current or behind, and the committed research/records/INDEX.md read against the tree."""
import io
import os
import sys
import tempfile
from contextlib import redirect_stdout

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import records_index  # noqa: E402

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FILES = (
    "README.md",
    "notes.txt",
    "2026-07-10_ALIGN-R0.md",
    "2026-10-05_THE_HNN_READS_A_PASSAGE.md",
    "2026-10-05_ATHENAS_HELD_SUMS_ON_GSM8K.md",
    "2026-10-24_E_IS_A_CHART_AND_THE_RHS_IS_A_FACE.md",
    "2026-11-02_A_VALUE_IS_READ_AT_A_PLACE.md",
    "2026-10-24_A_RECEIPT.json",
    "2026-10-24_A_RECORD_receipts/log.txt",
    "2026-09-07_conditional_phase/read.tsv",
    "receipts/2026-11-14_engine-lift/README.md",
    "receipts/2026-10-05-bank-boundary/out/a.txt",
    "receipts/pair-output-learning-20261006/a.txt",
    "receipts/no-date-here/a.txt",
    "receipts/2026-10-05-lane.txt",
    "stray/x.txt",
)
EMPTY = ("2026-11-03_NOTHING_receipts", "receipts/2026-11-04_nothing")


def quiet(call, *args):
    buf = io.StringIO()
    with redirect_stdout(buf):
        got = call(*args)
    return got, buf.getvalue()


def main():
    passed = 0
    for words, want in (
        ("THE_LINE_FLAILS", "The line flails"),
        ("ALIGN-R0", "Align-R0"),
        ("ATHENAS_HELD_SUMS_AND_THE_HNN_ON_GSM8K", "Athenas held sums and the HNN on GSM8K"),
        ("E_IS_A_CHART_AND_THE_RHS_IS_A_FACE", "E is a chart and the rhs is a face"),
        ("A_VALUE_IS_READ_BY_A_RECEIVER", "A value is read by a receiver"),
        ("THE_DE_BRUIJN_NEWMAN_BOUND_AND_RH", "The de Bruijn Newman bound and RH"),
        ("YANG_MILLS__AND_THE_GPUS", "Yang Mills and the GPUs"),
    ):
        assert records_index.title(words) == want, (words, records_index.title(words))
    passed += 1
    assert records_index.month_of("2026-10-05-bank") == (2026, 10) and records_index.month_of("pair-20261006") == (2026, 10)
    assert records_index.month_of("no-date-here") is None and records_index.month_of("2026-10-05x") is None
    passed += 1

    with tempfile.TemporaryDirectory() as tmp:
        base = os.path.join(tmp, records_index.RECORDS)
        for rel in FILES:
            os.makedirs(os.path.dirname(os.path.join(base, rel)), exist_ok=True)
            open(os.path.join(base, rel), "w", encoding="utf-8").write("x\n")
        for rel in EMPTY:
            os.makedirs(os.path.join(base, rel))

        records, beside, under, alone, unread = records_index.survey(tmp)
        assert [name for _, name in records] == sorted(f for f in FILES if f[:2] == "20" and f.endswith(".md") and "/" not in f), records
        assert beside == {(2026, 10): 1, (2026, 9): 1} and under == {(2026, 11): 1, (2026, 10): 2, None: 1}, (beside, under)
        assert alone == ["2026-10-24_A_RECEIPT.json", "receipts/2026-10-05-lane.txt"] and unread == ["notes.txt", "stray/"], (alone, unread)
        passed += 1

        text, counts, _ = records_index.index(tmp)
        assert counts == {"records": 5, "months": 3, "receipts_dirs": 6, "alone": 2, "unread": 2}, counts
        lines = text.split("\n")
        assert lines[0] == "# Records by date" and text.endswith(")\n"), lines[0]
        assert ("5 records from July 2026 to November 2026. 6 receipts directories: 2 beside the records and 4 under "
                "[`receipts/`](receipts/). Receipt files that stand alone: 2.") in lines, text
        table = [line for line in lines if line.startswith("| ")]
        assert table == [
            "| Month | Records | Receipts directories |",
            "| [November 2026](#november-2026) | 1 | 1 |",
            "| [October 2026](#october-2026) | 3 | 3 |",
            "| September 2026 | 0 | 1 |",
            "| [July 2026](#july-2026) | 1 | 0 |",
            "| No date | 0 | 1 |",
        ], table
        passed += 1
        body = lines[lines.index("## November 2026"):]
        assert body == [
            "## November 2026",
            "",
            "- 2026-11-02 [A value is read at a place](2026-11-02_A_VALUE_IS_READ_AT_A_PLACE.md)",
            "",
            "## October 2026",
            "",
            "- 2026-10-24 [E is a chart and the rhs is a face](2026-10-24_E_IS_A_CHART_AND_THE_RHS_IS_A_FACE.md)",
            "- 2026-10-05 [Athenas held sums on GSM8K](2026-10-05_ATHENAS_HELD_SUMS_ON_GSM8K.md)",
            "- 2026-10-05 [The HNN reads a passage](2026-10-05_THE_HNN_READS_A_PASSAGE.md)",
            "",
            "## July 2026",
            "",
            "- 2026-07-10 [Align-R0](2026-07-10_ALIGN-R0.md)",
            "",
        ], body
        passed += 1

        current, out = quiet(records_index.check, tmp)
        assert not current and "STALE research/records/INDEX.md:1 holds ``" in out, out
        _, out = quiet(records_index.write, tmp)
        assert "RECORDS_INDEX records=5 months=3 receipts_dirs=6 alone=2 unread=2" in out and "UNREAD research/records/stray/" in out, out
        current, out = quiet(records_index.check, tmp)
        assert current and "STALE" not in out, out
        assert open(os.path.join(base, records_index.INDEX), encoding="utf-8").read() == text
        passed += 1
        open(os.path.join(base, "2026-11-18_A_NEW_RECORD.md"), "w", encoding="utf-8").write("x\n")
        current, out = quiet(records_index.check, tmp)
        assert not current and "INDEX.md:11 holds `5 records from July" in out and "the file names give `6 records from July" in out, out
        passed += 1

    current, out = quiet(records_index.check, REPO)
    assert current, "research/records/INDEX.md is behind the file names: run `python3 tools/records_index.py write`\n" + out
    passed += 1
    print(f"records_index controls: {passed} passed")


if __name__ == "__main__":
    main()
