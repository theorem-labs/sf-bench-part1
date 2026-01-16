#!/bin/bash

# Count lines of code in solution.lean files and theories/Isomorphisms files

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(dirname "$SCRIPT_DIR")"

echo "=== Line Count Summary ==="
echo

# Count solution.lean files
echo "solution.lean files:"
solution_count=$(find "$ROOT_DIR/results" -name "solution.lean" | wc -l)
solution_lines=$(find "$ROOT_DIR/results" -name "solution.lean" -exec cat {} + 2>/dev/null | wc -l)
echo "  Files: $solution_count"
echo "  Total lines: $solution_lines"
echo

# Count theories/Isomorphisms files (inside each result directory) using coqwc
echo "theories/Isomorphisms files:"
iso_count=$(find "$ROOT_DIR/results"/result-*/theories/Isomorphisms -type f -name "*.v" 2>/dev/null | wc -l)
echo "  Files: $iso_count"

# Use coqwc to get spec/proof/comment breakdown
# coqwc output: spec proof comments filename
totals=$(find "$ROOT_DIR/results"/result-*/theories/Isomorphisms -type f -name "*.v" 2>/dev/null | xargs coqwc 2>/dev/null | grep "total$")
spec_lines=$(echo "$totals" | awk '{sum += $1} END {print sum}')
proof_lines=$(echo "$totals" | awk '{sum += $2} END {print sum}')
comment_lines=$(echo "$totals" | awk '{sum += $3} END {print sum}')

echo "  Spec lines: $spec_lines"
echo "  Proof lines: $proof_lines"
echo "  Comment lines: $comment_lines"
echo "  Total lines: $((spec_lines + proof_lines + comment_lines))"
