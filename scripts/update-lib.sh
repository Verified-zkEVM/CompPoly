#!/bin/bash

# Update CompPoly.lean with all imports
# This script generates the main library file by scanning all .lean files

set -e  # Exit on any error

echo "Updating CompPoly.lean with all imports..."

# Generate imports for CompPoly.
# The library uses the Lean 4 module system, so the root file is a `module` whose
# imports are all `public import`.
{
  echo "module"
  echo ""
  git ls-files 'CompPoly/*.lean' | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/public import /'
} > CompPoly.lean

echo "✓ CompPoly.lean updated with $(grep -c '^public import ' CompPoly.lean) imports"

# Uncomment if you have Examples
# git ls-files 'Examples/*.lean' | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > Examples.lean
