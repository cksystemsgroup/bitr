#!/bin/bash
# Unified benchmark runner: bitr on all suites with comparison against references
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(dirname "$SCRIPT_DIR")"
BITR="${ROOT_DIR}/target/release/bitr"
TIMEOUT=${TIMEOUT:-300}
RESULTS_DIR="${ROOT_DIR}/results"
BITR_OPTS="${BITR_OPTS:---no-oracle}"

mkdir -p "$RESULTS_DIR"

# Build if needed
if [ ! -f "$BITR" ] || [ "$BITR" -ot "${ROOT_DIR}/bitr/src/main.rs" ]; then
    echo "Building bitr (release)..."
    cargo build --release --manifest-path "${ROOT_DIR}/Cargo.toml" 2>&1 | tail -1
fi

run_suite() {
    local suite_name="$1"
    local suite_dir="$2"
    local output="${RESULTS_DIR}/${suite_name}.csv"

    echo "name,status,time_s" > "$output"

    local count=0
    local solved=0
    local total_time=0

    for f in "$suite_dir"/*.btor2; do
        [ -f "$f" ] || continue
        local name=$(basename "$f" .btor2)
        count=$((count + 1))

        local start=$(date +%s.%N)
        local result
        result=$(timeout "${TIMEOUT}s" "$BITR" $BITR_OPTS --timeout "$TIMEOUT" "$f" 2>/dev/null | tail -1) || result="TIMEOUT"
        local end=$(date +%s.%N)
        local elapsed=$(echo "$end - $start" | bc)

        local status="unknown"
        case "$result" in
            *"sat"*)
                if echo "$result" | grep -q "^unsat"; then
                    status="unsat"
                else
                    status="sat"
                fi
                solved=$((solved + 1))
                total_time=$(echo "$total_time + $elapsed" | bc)
                ;;
            *"TIMEOUT"*) status="timeout" ;;
        esac

        echo "${name},${status},${elapsed}" >> "$output"
        printf "\r  [%d] %-40s %s (%.1fs)" "$count" "$name" "$status" "$elapsed"
    done

    echo ""
    echo "  ${suite_name}: solved ${solved}/${count}, time ${total_time}s (results: ${output})"
}

echo "=== BITR Benchmark Suite ==="
echo "Timeout: ${TIMEOUT}s | Options: ${BITR_OPTS}"
echo ""

# Tiny benchmarks
if [ -d "${ROOT_DIR}/benchmarks/tiny" ]; then
    echo "--- tiny ---"
    run_suite "tiny" "${ROOT_DIR}/benchmarks/tiny"
fi

# Perf benchmarks
if [ -d "${ROOT_DIR}/benchmarks/perf" ]; then
    echo "--- perf ---"
    run_suite "perf" "${ROOT_DIR}/benchmarks/perf"
fi

# HWMCC'24 BV
if [ -d "${ROOT_DIR}/benchmarks/bv" ] && [ "$(ls -A "${ROOT_DIR}/benchmarks/bv" 2>/dev/null)" ]; then
    echo "--- HWMCC'24 BV ---"
    run_suite "bv" "${ROOT_DIR}/benchmarks/bv"

    # Auto-compare against rIC3 if reference exists
    if [ -f "${ROOT_DIR}/benchmarks/hwmcc24-results-bv.csv" ]; then
        echo ""
        echo "--- Comparison vs rIC3 ---"
        python3 "${SCRIPT_DIR}/compare_ric3.py" \
            "${RESULTS_DIR}/bv.csv" \
            "${ROOT_DIR}/benchmarks/hwmcc24-results-bv.csv" \
            ric3
    fi
fi

# HWMCC'24 Array
if [ -d "${ROOT_DIR}/benchmarks/array" ] && [ "$(ls -A "${ROOT_DIR}/benchmarks/array" 2>/dev/null)" ]; then
    echo "--- HWMCC'24 Array ---"
    run_suite "array" "${ROOT_DIR}/benchmarks/array"

    if [ -f "${ROOT_DIR}/benchmarks/hwmcc24-results-array.csv" ]; then
        echo ""
        echo "--- Comparison vs rIC3 (Array) ---"
        python3 "${SCRIPT_DIR}/compare_ric3.py" \
            "${RESULTS_DIR}/array.csv" \
            "${ROOT_DIR}/benchmarks/hwmcc24-results-array.csv" \
            ric3
    fi
fi

echo ""
echo "=== Done ==="
