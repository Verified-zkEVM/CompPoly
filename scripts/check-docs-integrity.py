#!/usr/bin/env python3
"""Check CompPoly documentation integrity.

Checks:
1. `CLAUDE.md` exists and is a symlink to `AGENTS.md`
2. Local markdown links in tracked repo docs resolve
3. Backticked source paths in those docs (`CompPoly/Foo/Bar.lean`) point at files
   that exist

Check 3 exists because the docs cite far more paths in backticks than in markdown
links, and those are the ones that rot silently when a module is split or renamed.

Exit code 0 if all checks pass, 1 otherwise.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CLAUDE_PATH = REPO_ROOT / "CLAUDE.md"
AGENTS_PATH = REPO_ROOT / "AGENTS.md"

MARKDOWN_LINK_RE = re.compile(r"(?<!!)\[[^\]]+\]\(([^)]+)\)")
IGNORED_DIRS = {".git", ".lake"}

# Backticked source paths, e.g. `CompPoly/Univariate/Basic.lean`.
BACKTICK_PATH_RE = re.compile(r"`([A-Za-z0-9_./\-]+\.(?:lean|py|sh|yml|bib))`")

# Docs routinely cite paths relative to a subtree rather than to the repo root
# (`field-extensions.md` writes `KoalaBear/Ext4.lean`, `coding-theory.md` writes
# `Interpolation/Basic.lean`). A backticked path counts as resolved if it exists
# under any of these roots, or under the directory of the file citing it.
#
# Add a prefix only for a subtree that a doc page is genuinely written *about*, so
# its prose can name files relatively. Every added prefix weakens the check, so
# keep the list short and prefer fixing the doc.
PATH_PREFIXES = (
    "",
    "CompPoly",
    "CompPoly/Fields",
    "CompPoly/Fields/Binary",
    "CompPoly/Fields/KoalaBear",
    "CompPoly/Univariate",
    "CompPoly/Bivariate",
    "CompPoly/Bivariate/GuruswamiSudan",
    "CompPoly/LinearAlgebra",
    "CompPoly/LinearAlgebra/PolynomialMatrix",
    "tests",
    "bench",
)

# Paths that are illustrative rather than real: glob patterns, and the `Foo/*`
# shorthand the wiki uses for "everything in this directory".
def _is_illustrative(path: str) -> bool:
    return "*" in path or path.endswith("/")


def markdown_files() -> list[Path]:
    files: list[Path] = []
    for path in REPO_ROOT.rglob("*.md"):
        try:
            rel = path.relative_to(REPO_ROOT)
        except ValueError:
            continue
        if rel.parts and rel.parts[0] in IGNORED_DIRS:
            continue
        files.append(path)
    return sorted(files)


def check_claude_symlink() -> list[str]:
    errors: list[str] = []
    if not AGENTS_PATH.exists():
        errors.append("Missing AGENTS.md")
        return errors
    if not CLAUDE_PATH.exists() and not CLAUDE_PATH.is_symlink():
        errors.append("Missing CLAUDE.md")
        return errors
    if not CLAUDE_PATH.is_symlink():
        errors.append("CLAUDE.md must be a symlink to AGENTS.md")
        return errors

    target = Path(CLAUDE_PATH.readlink())
    if target != Path("AGENTS.md"):
        errors.append(f"CLAUDE.md must point to AGENTS.md, found {target}")
    elif not CLAUDE_PATH.resolve().samefile(AGENTS_PATH):
        errors.append("CLAUDE.md symlink does not resolve to AGENTS.md")
    return errors


def resolve_link(source_file: Path, raw_target: str) -> Path | None:
    target = raw_target.strip().strip("`")
    if (
        not target
        or "://" in target
        or target.startswith("mailto:")
        or target.startswith("tel:")
    ):
        return None

    path_part = target.split("#", 1)[0].strip()
    if not path_part:
        return None

    if path_part.startswith("/"):
        return (REPO_ROOT / path_part.lstrip("/")).resolve()
    return (source_file.parent / path_part).resolve()


def check_markdown_links() -> list[str]:
    errors: list[str] = []
    for doc_file in markdown_files():
        text = doc_file.read_text(encoding="utf-8")
        for raw_target in MARKDOWN_LINK_RE.findall(text):
            resolved = resolve_link(doc_file, raw_target)
            if resolved is None:
                continue
            if not resolved.exists():
                rel_doc = doc_file.relative_to(REPO_ROOT)
                errors.append(f"Broken link in {rel_doc}: {raw_target}")
    return errors


def check_backtick_paths() -> list[str]:
    errors: list[str] = []
    for doc_file in markdown_files():
        text = doc_file.read_text(encoding="utf-8")
        for raw_target in BACKTICK_PATH_RE.findall(text):
            # A bare filename with no directory is almost always prose
            # ("regenerate `update-lib.sh`"), not a path claim.
            if "/" not in raw_target or _is_illustrative(raw_target):
                continue
            candidates = [REPO_ROOT / prefix / raw_target for prefix in PATH_PREFIXES]
            candidates.append(doc_file.parent / raw_target)
            if not any(candidate.exists() for candidate in candidates):
                rel_doc = doc_file.relative_to(REPO_ROOT)
                errors.append(f"Broken path in {rel_doc}: `{raw_target}`")
    return errors


def main() -> int:
    all_errors: list[str] = []

    print("Checking CLAUDE.md symlink...")
    all_errors.extend(check_claude_symlink())

    print("Checking markdown links...")
    all_errors.extend(check_markdown_links())

    print("Checking backticked source paths...")
    all_errors.extend(check_backtick_paths())

    if all_errors:
        print(f"\n{len(all_errors)} issue(s) found:\n")
        for err in all_errors:
            print(f"  - {err}")
        return 1

    print("\nAll documentation integrity checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
