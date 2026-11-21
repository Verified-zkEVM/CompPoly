#!/usr/bin/env -S uv run --no-project --python 3.12 python
"""Report which declaration statements a change alters.

Usage: statement_diff.py BASE.json HEAD.json

Both files come from `lake exe axiomsweep --statements FILE`. The output is Markdown for a
pull request: declarations the change removes, theorems whose statement changed, and other
declarations whose type or value changed. Exits 0 whenever both files parse; it reports,
it does not gate.
"""

import json
import sys

# Rows shown per section; the rest are counted.
LIMIT = 50


def load(path):
    with open(path, encoding="utf-8") as handle:
        data = json.load(handle)
    return data, {entry["name"]: entry for entry in data["declarations"]}


def section(title, names, by_name, lines):
    if not names:
        return
    lines.append(f"**{title}** ({len(names)})")
    lines.append("")
    for name in names[:LIMIT]:
        entry = by_name[name]
        lines.append(f"- `{name}` ({entry['kind']}, `{entry['module']}`)")
    if len(names) > LIMIT:
        lines.append(f"- … and {len(names) - LIMIT} more")
    lines.append("")


def main(argv):
    if len(argv) != 3:
        print(__doc__.strip(), file=sys.stderr)
        return 2
    base_data, base = load(argv[1])
    head_data, head = load(argv[2])
    lines = ["### Statement changes against the base revision", ""]
    lines.append(
        "Report only. It lists declarations whose statement (type and universe parameters) "
        "or, for anything but a theorem, value changed, by digest. It does not judge whether "
        "a change weakens a theorem, does not compare proofs, and cannot see `example`s. "
        "Binder names are ignored; the binder info (explicit, implicit, instance) of each "
        "leading argument is not."
    )
    lines.append("")
    if base_data.get("toolchain") != head_data.get("toolchain"):
        lines.append(
            f"Not compared: the base was exported under Lean `{base_data.get('toolchain')}` "
            f"and this revision under `{head_data.get('toolchain')}`, so every digest may "
            "differ."
        )
        print("\n".join(lines))
        return 0
    if base_data.get("roots") != head_data.get("roots"):
        lines.append(
            f"Note: the base export covers roots {base_data.get('roots')} and this one "
            f"{head_data.get('roots')}; declarations under only one of them show as added "
            "or removed."
        )
        lines.append("")

    removed = sorted(n for n in base if n not in head)
    added = [n for n in head if n not in base]
    statement_changed = []
    type_changed = []
    value_changed = []
    for name in sorted(n for n in head if n in base):
        b, h = base[name], head[name]
        signature_changed = (
            b["type"] != h["type"]
            or b["levelParams"] != h["levelParams"]
            or b["kind"] != h["kind"]
        )
        if signature_changed:
            (statement_changed if h["kind"] == "theorem" else type_changed).append(name)
        elif b.get("value") != h.get("value"):
            value_changed.append(name)

    if not (removed or statement_changed or type_changed or value_changed):
        lines.append(f"No existing declaration changed; {len(added)} added.")
        print("\n".join(lines))
        return 0
    section("Removed declarations", removed, base, lines)
    section("Theorems whose statement changed", statement_changed, head, lines)
    section("Other declarations whose type changed", type_changed, head, lines)
    section("Definitions whose value changed", value_changed, head, lines)
    lines.append(f"{len(added)} declarations added.")
    print("\n".join(lines))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
