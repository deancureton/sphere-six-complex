#!/usr/bin/env python3
"""Fail if a proof placeholder appears outside the three declared boundaries.

Project policy (#11) is that no `sorry`, `admit`, or `native_decide` survives except:

* `SphereSixComplex.exists_paperGluingData` in `SphereSixComplex/Final.lean`, and
* the two trusted Comparator challenge declarations in `Challenge.lean`.

Each allowed `(file, declaration, token)` is listed below with its exact count, so relocating or
substituting a placeholder fails even when the total in that file is unchanged. Comments and
docstrings are ignored, so prose like "germs admit a comparison" does not trip the check.
"""

from __future__ import annotations

import os
import re
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir)

#: Exact (file, enclosing declaration, token) identities accepted once each.
ALLOWED = {
    ("SphereSixComplex/Final.lean", "exists_paperGluingData", "sorry"),
    ("Challenge.lean", "sphere_six_admits_complex_structure", "sorry"),
    ("Challenge.lean", "mathoverflow_1973", "sorry"),
}

TOKEN_RE = re.compile(r"(?<![\w.])(sorry|admit|native_decide)(?![\w'])")
LINE_COMMENT_RE = re.compile(r"--.*$", re.MULTILINE)
DECL_RE = re.compile(
    r"^(?:@\[[^\n]*\][ \t]*)?"
    r"(?:(?:public|private|protected|noncomputable|unsafe)[ \t]+)*"
    r"(?:(?:theorem|lemma|def|abbrev|instance|axiom|opaque|structure|class|inductive)"
    r"[ \t]+(?P<name>[A-Za-z_][\w'.]*)|example\b)",
    re.MULTILINE,
)


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


def check_source(path: str, source: str) -> list[str]:
    """Compare one source against its exact declaration-level allowance."""
    text = strip_comments(source)
    headers = iter(DECL_RE.finditer(text))
    next_header = next(headers, None)
    declaration = "<outside declaration>"
    seen: set[tuple[str, str, str]] = set()
    failures: list[str] = []
    for match in TOKEN_RE.finditer(text):
        while next_header is not None and next_header.start() < match.start():
            declaration = next_header.group("name") or "<anonymous example>"
            next_header = next(headers, None)
        key = (path, declaration, match.group(1))
        if key not in ALLOWED or key in seen:
            line = text.count("\n", 0, match.start()) + 1
            failures.append(f"  {path}:{line}: {key[2]} in {declaration}")
        seen.add(key)
    for expected in sorted(key for key in ALLOWED if key[0] == path):
        if expected not in seen:
            failures.append(f"  {path}: expected {expected[2]} in {expected[1]}, found none")
    return failures


def main() -> int:
    failures: list[str] = []
    for path in sources():
        with open(os.path.join(ROOT, path), encoding="utf-8") as handle:
            failures.extend(check_source(path, handle.read()))

    if failures:
        print("Placeholder check FAILED:")
        print("\n".join(failures))
        return 1

    total = len(ALLOWED)
    print(f"Placeholder check passed: {total} declared placeholder(s), none elsewhere.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
