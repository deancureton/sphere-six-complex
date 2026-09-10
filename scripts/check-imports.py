#!/usr/bin/env python3
"""Check build coverage, project imports, and the prerequisite/paper boundary.

A module outside every build target is checked by nothing: `lake build` never elaborates it, and
its axioms are invisible to `#print axioms`. This guards against that regressing.
"""

from __future__ import annotations

import collections
import os
import re
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir)
LIB = "SphereSixComplex"
ROOT_MODULE = f"{LIB}.Main"

IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+(?:all\s+)?([\w.]+)")


def main() -> int:
    imports: dict[str, set[str]] = collections.defaultdict(set)
    modules: set[str] = set()
    for dirpath, _, filenames in os.walk(os.path.join(ROOT, LIB)):
        for name in sorted(filenames):
            if not name.endswith(".lean"):
                continue
            path = os.path.relpath(os.path.join(dirpath, name), ROOT)
            module = path[: -len(".lean")].replace(os.sep, ".")
            modules.add(module)
            with open(os.path.join(ROOT, path), encoding="utf-8") as handle:
                for line in handle:
                    match = IMPORT_RE.match(line)
                    if match and match.group(1).startswith(LIB):
                        imports[module].add(match.group(1))

    seen: set[str] = set()
    stack = [ROOT_MODULE]
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        stack.extend(imports.get(module, ()))

    orphans = sorted(modules - seen)
    if orphans:
        print(f"Import check FAILED: {len(orphans)} module(s) unreachable from {ROOT_MODULE}:")
        for module in orphans:
            print(f"  {module}")
        print()
        print(f"Nothing checks these modules. Import them from {LIB}/Main.lean, or delete them.")
        return 1

    missing = sorted((module, dependency) for module, dependencies in imports.items()
                     for dependency in dependencies if dependency not in modules)
    if missing:
        print("Import check FAILED: missing project modules:")
        for module, dependency in missing:
            print(f"  {module} imports {dependency}")
        return 1

    prerequisite_prefix = f"{LIB}.Prerequisites."
    violations = sorted((module, dependency) for module, dependencies in imports.items()
                        if module.startswith(prerequisite_prefix)
                        for dependency in dependencies
                        if not dependency.startswith(prerequisite_prefix))
    if violations:
        print("Import check FAILED: prerequisites depend on the paper or an aggregate:")
        for module, dependency in violations:
            print(f"  {module} imports {dependency}")
        return 1

    print(f"Import check passed: all {len(modules)} modules are reachable from {ROOT_MODULE}.")
    print("Layer check passed: prerequisites have no project dependencies outside their layer.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
