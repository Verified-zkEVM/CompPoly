#!/bin/bash

echo "Running lake build (quiet mode, errors only)..."

# Run lake build with --quiet, capture output and exit code
OUTPUT=$(lake exe cache get && lake build --quiet 2>&1)
EXIT_CODE=$?

# Count errors and warnings
ERROR_COUNT=$(echo "$OUTPUT" | grep -c "^error:" || true)
WARNING_COUNT=$(echo "$OUTPUT" | grep -c "^warning:" || true)

echo "════════════════════════════════════════════════"
echo "Build Summary:"
echo "  Warnings: $WARNING_COUNT (suppressed in output below)"
echo "  Errors:   $ERROR_COUNT"
echo "  Exit code: $EXIT_CODE"
echo "════════════════════════════════════════════════"

if [ $EXIT_CODE -ne 0 ]; then
    echo ""
    echo "❌ BUILD FAILED - Showing errors only:"
    echo ""
    echo "$OUTPUT" | grep -A 3 "^error:"
else
    echo "✅ BUILD SUCCEEDED"
fi

exit $EXIT_CODE
