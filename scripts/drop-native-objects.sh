#!/bin/bash

# Delete the build outputs compiled with `-march=native`, and the executables linking them, so
# the next `lake build` recompiles them for this host. CI restores `.lake/build` from runs on
# other runner CPUs, whose host-tuned objects can hold instructions this one lacks (SIGILL).

set -euo pipefail

[ -d .lake/build ] || exit 0
{ grep -rlF --include='*.trace' -e '-march=native' .lake/build || true; } | while read -r trace; do
  rm -f "${trace%.trace}" "${trace%.trace}".*
done
rm -rf .lake/build/bin
