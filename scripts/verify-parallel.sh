#!/bin/bash
# Parallel verification script for sf-bench-part1 translations
# Usage: ./scripts/verify-parallel.sh [--jobs N]
#
# Runs all verifications in parallel using multiple Docker containers.
# Default: 8 parallel jobs (adjust with --jobs)

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
RESULTS_DIR="$PROJECT_DIR/results"
JOBS=8

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --jobs|-j)
            JOBS="$2"
            shift 2
            ;;
        *)
            echo "Unknown option: $1"
            echo "Usage: $0 [--jobs N]"
            exit 1
            ;;
    esac
done

# Find all result directories
RESULTS=$(find "$RESULTS_DIR" -maxdepth 1 -type d -name 'result-*' -printf '%f\n' | sort -V)
TOTAL=$(echo "$RESULTS" | wc -l)

echo "Verifying $TOTAL results with $JOBS parallel workers..."
echo ""

# Create temp file for collecting results
OUTPUT_FILE=$(mktemp)
trap "rm -f $OUTPUT_FILE" EXIT

# Function to verify a single result (runs in subshell)
verify_one() {
    local result_name="$1"
    local project_dir="$2"
    local output_file="$3"

    # Run docker container for this single result, capture only success/failure
    if docker run --rm -v "$project_dir:/host" sf-bench-part1 verify "$result_name" >/dev/null 2>&1; then
        echo "$result_name success" | tee -a "$output_file"
    else
        echo "$result_name FAILED" | tee -a "$output_file"
    fi
}

export -f verify_one

# Run verifications in parallel using xargs
echo "$RESULTS" | xargs -P "$JOBS" -I {} bash -c "verify_one {} '$PROJECT_DIR' '$OUTPUT_FILE'"

# Count results
PASSED=$(grep -c "success$" "$OUTPUT_FILE" 2>/dev/null || echo 0)
FAILED=$(grep -c "FAILED$" "$OUTPUT_FILE" 2>/dev/null || echo 0)

echo ""
echo "=========================================="
echo "SUMMARY: $PASSED passed, $FAILED failed (out of $TOTAL)"
echo "=========================================="

if [ "$FAILED" -gt 0 ]; then
    echo ""
    echo "Failed:"
    grep "FAILED$" "$OUTPUT_FILE" | sed 's/ FAILED$//'
    exit 1
fi
