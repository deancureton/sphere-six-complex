#!/usr/bin/env python3
"""Rewrite a declared axiom list from a computed closure, preserving the file's structure.

Entries already present keep their position and their section comment; entries no longer in the
closure are dropped; entries new to the closure are appended under a marker so that they can be
moved into the section they belong to.

Usage: rewrite_axiom_list.py LIST_FILE CLOSURE_FILE
"""

import sys

NEW_SECTION = "# Newly computed; move into the section it belongs to."


def main(list_path: str, closure_path: str) -> None:
    with open(closure_path) as handle:
        closure = [line.strip() for line in handle if line.strip()]
    closure_set = set(closure)

    with open(list_path) as handle:
        lines = [line.rstrip("\n") for line in handle]

    kept: list[str] = []
    present: set[str] = set()
    for line in lines:
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            if stripped == NEW_SECTION:
                continue
            kept.append(line)
            continue
        if stripped in closure_set:
            kept.append(line)
            present.add(stripped)

    # Drop section headers left without entries, and any blank runs they leave behind.
    pruned: list[str] = []
    for index, line in enumerate(kept):
        if line.strip().startswith("#"):
            has_entry = False
            for later in kept[index + 1:]:
                if later.strip().startswith("#"):
                    break
                if later.strip():
                    has_entry = True
                    break
            # The leading header block describes the file itself, so it always stays.
            if not has_entry and any(entry.strip() and not entry.strip().startswith("#")
                                     for entry in kept[:index]):
                continue
        pruned.append(line)

    while pruned and not pruned[-1].strip():
        pruned.pop()

    added = [entry for entry in closure if entry not in present]
    if added:
        pruned.append("")
        pruned.append(NEW_SECTION)
        pruned.extend(added)

    with open(list_path, "w") as handle:
        handle.write("\n".join(pruned) + "\n")

    removed = sum(1 for line in lines
                  if line.strip() and not line.strip().startswith("#")
                  and line.strip() not in closure_set)
    print(f"  {list_path}: {len(present) + len(added)} constants "
          f"({len(added)} added, {removed} removed)")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    main(sys.argv[1], sys.argv[2])
