#!/usr/bin/env python3
"""Inventory every `axiom` declaration in SphereSixComplex and locate it in the import graph.

Emits a Markdown table on stdout.  Statuses:

* `final`  - reachable from `SphereSixComplex.Final`, so the headline theorem may depend on it;
* `main`   - reachable from `SphereSixComplex.Main` only;
* `unused` - in neither cone (dead code, or a module not yet wired into `Main`).

The `#print axioms` audit in `scripts/check-axioms.sh` is the authoritative statement of what the
final theorem actually depends on; this script is the static counterpart, covering axioms that a
future proof could start depending on.
"""

from __future__ import annotations

import collections
import os
import re
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir)
LIB = "SphereSixComplex"

IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+(?:all\s+)?([\w.]+)")
AXIOM_RE = re.compile(
    r"^\s*(?:public\s+|private\s+|protected\s+|noncomputable\s+)*axiom\s+([\w'₀-₉]+)"
)


def modules() -> list[tuple[str, str]]:
    out = []
    for dirpath, _, filenames in os.walk(os.path.join(ROOT, LIB)):
        for name in sorted(filenames):
            if name.endswith(".lean"):
                path = os.path.relpath(os.path.join(dirpath, name), ROOT)
                out.append((path[: -len(".lean")].replace(os.sep, "."), path))
    return sorted(out)


def imports_of(path: str) -> set[str]:
    found = set()
    with open(os.path.join(ROOT, path), encoding="utf-8") as handle:
        for line in handle:
            match = IMPORT_RE.match(line)
            if match and match.group(1).startswith(LIB):
                found.add(match.group(1))
    return found


def axioms_of(path: str) -> list[tuple[int, str]]:
    found = []
    with open(os.path.join(ROOT, path), encoding="utf-8") as handle:
        for number, line in enumerate(handle, start=1):
            match = AXIOM_RE.match(line)
            if match:
                found.append((number, match.group(1)))
    return found


def cone(graph: dict[str, set[str]], start: str) -> set[str]:
    seen: set[str] = set()
    stack = [start]
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        stack.extend(graph.get(module, ()))
    return seen


def main() -> int:
    all_modules = modules()
    graph = {module: imports_of(path) for module, path in all_modules}
    final_cone = cone(graph, f"{LIB}.Final")
    main_cone = cone(graph, f"{LIB}.Main")

    rows = []
    for module, path in all_modules:
        for line, name in axioms_of(path):
            if module in final_cone:
                status = "final"
            elif module in main_cone:
                status = "main"
            else:
                status = "unused"
            rows.append((status, path, line, name))

    order = {"final": 0, "main": 1, "unused": 2}
    rows.sort(key=lambda row: (order[row[0]], row[1], row[2]))

    print("| status | axiom | source |")
    print("| --- | --- | --- |")
    for status, path, line, name in rows:
        print(f"| `{status}` | `{name}` | `{path}:{line}` |")
    print()
    counts = collections.Counter(status for status, _, _, _ in rows)
    print(
        f"{len(rows)} axioms: {counts['final']} in the `Final` cone, "
        f"{counts['main']} further in the `Main` cone, {counts['unused']} in neither."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
