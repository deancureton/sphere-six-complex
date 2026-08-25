#!/usr/bin/env python3
"""Fail if a proof placeholder appears outside the two declared boundaries.

Project policy (#11) is that no `sorry`, `admit`, or `native_decide` survives except:

* the single paper-specific gluing `sorry` in `SphereSixComplex/Final.lean`, and
* the trusted Comparator challenge statements in `Challenge.lean`.

Both are listed in ALLOWED below, with the exact number of occurrences expected, so that a new
placeholder anywhere — including a second one in `Final.lean` — is a failure rather than a silent
regression. Comments and docstrings are ignored, so prose like "germs admit a comparison" does not
trip the check.
"""

from __future__ import annotations

import os
import re
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir)

#: file -> number of placeholder occurrences that are expected and accepted.
ALLOWED = {
    "SphereSixComplex/Final.lean": 1,
    "Challenge.lean": 2,
}

TOKEN_RE = re.compile(r"(?<![\w.])(sorry|admit|native_decide)(?![\w'])")
LINE_COMMENT_RE = re.compile(r"--.*$")


def strip_comments(source: str) -> str:
    """Remove block comments and line comments, keeping line structure."""
    out: list[str] = []
    depth = 0
    i = 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            i += 2
        elif source.startswith("-/", i) and depth > 0:
            depth -= 1
            i += 2
        else:
            out.append(" " if depth > 0 and source[i] != "\n" else source[i])
            i += 1
    return LINE_COMMENT_RE.sub("", "".join(out)) if depth == 0 else "".join(out)


def sources() -> list[str]:
    found = ["Challenge.lean", "Solution.lean"]
    for dirpath, _, filenames in os.walk(os.path.join(ROOT, "SphereSixComplex")):
        for name in sorted(filenames):
            if name.endswith(".lean"):
                found.append(os.path.relpath(os.path.join(dirpath, name), ROOT))
    return sorted(found)


def main() -> int:
    failures: list[str] = []
    for path in sources():
        with open(os.path.join(ROOT, path), encoding="utf-8") as handle:
            text = strip_comments(handle.read())
        hits = [
            (number, match.group(1))
            for number, line in enumerate(text.splitlines(), start=1)
            for match in TOKEN_RE.finditer(LINE_COMMENT_RE.sub("", line))
        ]
        budget = ALLOWED.get(path, 0)
        if len(hits) > budget:
            for number, token in hits[budget:]:
                failures.append(f"  {path}:{number}: {token}")
        elif len(hits) < budget:
            failures.append(
                f"  {path}: expected {budget} declared placeholder(s), found {len(hits)}"
                " — update ALLOWED in scripts/check-sorries.py"
            )

    if failures:
        print("Placeholder check FAILED:")
        print("\n".join(failures))
        return 1

    total = sum(ALLOWED.values())
    print(f"Placeholder check passed: {total} declared placeholder(s), none elsewhere.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
