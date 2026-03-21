# CompPoly Wiki

This directory is the deeper companion to [`AGENTS.md`](../../AGENTS.md).
Use `AGENTS.md` for the one-screen AI-agent overview and this wiki for details that
are too specific or too changeable to keep at the repo root.

## Start Here

- [`quickstart.md`](quickstart.md) - canonical local validation commands and CI
  mapping.
- [`repo-map.md`](repo-map.md) - where to edit and how the main subtrees relate.
- [`generated-files.md`](generated-files.md) - derived outputs and their sources of
  truth.
- [`representations-and-bridges.md`](representations-and-bridges.md) - the main
  polynomial representations and Mathlib bridge layers.
- [`typeclass-minimization.md`](typeclass-minimization.md) - declaration-level
  typeclass discipline and minimal-assumption examples.
- [`binary-fields-and-ntt.md`](binary-fields-and-ntt.md) - the binary-field stack,
  GHASH model, and additive-NTT architecture.

## Maintenance Contract

- `AGENTS.md` is the canonical root guide for AI agents. `CLAUDE.md` is only a
  symlink.
- Keep one primary owner topic per page. The current pages are:
  - `quickstart.md` for commands, validation, and CI expectations.
  - `repo-map.md` for repo structure and work-area routing.
  - `generated-files.md` for derived outputs and source-of-truth rules.
  - `representations-and-bridges.md` for representation choice and Mathlib bridges.
  - `typeclass-minimization.md` for minimal typeclass assumptions and avoiding
    blanket instance scopes.
  - `binary-fields-and-ntt.md` for the specialized field and NTT stack.
- Add new pages when a recurring topic no longer fits cleanly in an existing page.
- If a PR changes commands, repo structure, generated-file behavior, or recurring
  architecture guidance, update the matching page in the same PR.
- Keep these files committed so worktrees and delegated agents see the same
  guidance.
- Prefer linking to canonical docs over copying them.

## Canonical Project Docs

- [`../../README.md`](../../README.md) - public repo overview and primary exported
  surfaces.
- [`../../CONTRIBUTING.md`](../../CONTRIBUTING.md) - contribution process, naming,
  style, docstrings, and citations.
- [`../../ROADMAP.md`](../../ROADMAP.md) - roadmap and current priorities.
- [`../../tests/README.md`](../../tests/README.md) - test layout and commands.
- [`../../scripts/README.md`](../../scripts/README.md) - script inventory and
  operator notes.
