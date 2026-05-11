#!/bin/bash
set -euo pipefail

# File paths
README="README.md"
EXPECTED="expected.txt"
ACTUAL="output.txt"
ACTUAL_CLEAN="actual_cleaned.txt"

# Extract the expected output from README.md.
# We use the first fenced code block after the expected-output heading.
awk '
  /^Expected output:$/ || /^Expected `make check` output:$/ {seen = 1; next}
  seen && /^```/ && !inblock {inblock = 1; next}
  seen && /^```$/ && inblock {exit}
  seen && inblock {print}
' "$README" > "$EXPECTED"

if [ ! -s "$EXPECTED" ]; then
    echo "Failed to extract expected output block from README.md"
    exit 1
fi

# Run make check and capture output
echo "Re-running make check..."
if make check > "$ACTUAL" 2>&1; then
    EXIT_CODE=0
else
    EXIT_CODE=$?
fi

# Print the full output for debugging/logs
cat "$ACTUAL"

# Extract the stable summary block from actual output:
# - start at the success line
# - include "All axioms used:" and consecutive "- ..." lines
awk '
  /^✅ / {capture = 1; print; next}
  capture && /^All axioms used:$/ {print; in_list = 1; next}
  capture && in_list && /^- / {print; next}
  capture && in_list && !/^- / {exit}
' "$ACTUAL" > "$ACTUAL_CLEAN"

if [ ! -s "$ACTUAL_CLEAN" ]; then
    echo "Failed to extract actual summary block from make check output."
    echo "make check exit code: $EXIT_CODE"
    rm -f "$EXPECTED" "$ACTUAL" "$ACTUAL_CLEAN"
    exit 1
fi

# Compare
if diff -w "$EXPECTED" "$ACTUAL_CLEAN"; then
    echo "Verification successful: Output matches README."
    rm -f "$EXPECTED" "$ACTUAL" "$ACTUAL_CLEAN"
    exit 0
else
    echo "Verification failed: Output differs from README."
    echo "make check exit code: $EXIT_CODE"
    echo "Expected:"
    cat "$EXPECTED"
    echo "Actual:"
    cat "$ACTUAL_CLEAN"
    rm -f "$EXPECTED" "$ACTUAL" "$ACTUAL_CLEAN"
    exit 1
fi
