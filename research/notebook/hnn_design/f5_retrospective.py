"""Pin F5's development-only retrospective requests and retrieval control.

The selector reads the pinned F5 validation requests and choosing responses, never a selected
validation response. Its result remains owner-only. See `f4_retrospective.py` for the shared
exterior selection law. F5's diagnostic split is spent and holds the development reserve, so it runs
only with the logged flag `--read-reserve` (`development_families.py`).

    HOLONICS_ROOT=<checkout with private cuts> python3 f5_retrospective.py --read-reserve
"""

import sys

from f4_retrospective import main


if __name__ == "__main__":
    if sys.argv[1:] not in ([], ["--read-reserve"]):
        sys.exit(__doc__)
    main("F5")
