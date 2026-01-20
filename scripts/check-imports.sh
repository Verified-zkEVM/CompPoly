#!/bin/bash

# Check if all imports are up to date
# This script updates CompPoly.lean and checks if there are any differences

set -e  # Exit on any error

echo "Checking if all imports are up to date..."

# Save current CompPoly.lean
cp CompPoly.lean CompPoly.lean.backup

# Update imports
./scripts/update-lib.sh

# Check for differences
if git diff --exit-code CompPoly.lean > /dev/null; then
    echo "✓ All imports are up to date!"
    rm CompPoly.lean.backup
    exit 0
else
    echo "❌ Import file is out of date!"
    echo "Differences found:"
    git diff CompPoly.lean
    echo ""
    echo "To fix this, run: ./scripts/update-lib.sh"

    # Restore original file
    mv CompPoly.lean.backup CompPoly.lean
    exit 1
fi
