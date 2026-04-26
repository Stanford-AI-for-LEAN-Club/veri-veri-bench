#!/usr/bin/env bash
# ============================================================
# run_diff_test.sh
# ============================================================
# End-to-end differential test driver.
#
# For each tests/*.py:
#   1. Run with CPython, capture stdout (newline-separated ints).
#   2. Use parse.py to convert the file into a Maude AST under
#      a fresh Pgm constant.
#   3. Run Maude on the pythonlite big-step semantics + the
#      auto-generated AST module + a `rewrite < <Pgm> > .`
#      driver, capture the final Out buffer.
#   4. Normalise the Maude Out buffer into newline-separated
#      ints and diff against the CPython output.
#   5. Print PASS / FAIL per test; exit nonzero if any FAIL.
#
# The corpus is the test directory `tests/`.  Add new programs by
# dropping a fresh `NN_name.py` file there; no other change needed.
# ============================================================

set -u

cd "$(dirname "$0")"

PASS=0
FAIL=0
TOTAL=0
RESULTS=()

extract_out() {
    python3 "$(dirname "$0")/extract_out.py"
}

run_one() {
    local pyfile="$1"
    local name; name=$(basename "$pyfile" .py)
    local const_name="autoPgm_$(echo "$name" | tr -d -c 'A-Za-z0-9')"
    TOTAL=$((TOTAL + 1))

    # 1. CPython
    local cpy_out
    if ! cpy_out=$(python3 "$pyfile" 2>&1); then
        echo "FAIL  $name  (CPython itself errored: $cpy_out)"
        FAIL=$((FAIL + 1))
        RESULTS+=("FAIL|$name|cpython-error")
        return
    fi

    # 2. parse.py -> Maude module fragment
    local generated="/tmp/${const_name}.maude"
    if ! python3 parse.py "$pyfile" "$const_name" > "$generated" 2>/tmp/parse_err; then
        echo "FAIL  $name  (parse.py errored: $(cat /tmp/parse_err))"
        FAIL=$((FAIL + 1))
        RESULTS+=("FAIL|$name|parser-error")
        return
    fi

    # 3. Run Maude
    local maude_input="/tmp/${const_name}_run.maude"
    cat > "$maude_input" <<EOF
in $(pwd)/builtins.maude
in $(pwd)/pl-string.maude
in $(pwd)/pythonlite-values.maude
in $(pwd)/pythonlite-syntax.maude
in $(pwd)/pythonlite-state.maude
in $(pwd)/pythonlite-bigstep.maude
in $generated

mod RUN is
  including PYTHONLITE-SEMANTICS-BIGSTEP + ${const_name^^}-PROG .
endm

rewrite < $const_name > .
quit
EOF
    local maude_out
    maude_out=$(maude -no-prelude -no-banner "$maude_input" 2>&1)

    # 4. Normalize Maude Out buffer
    local maude_norm
    maude_norm=$(echo "$maude_out" | extract_out)

    # 5. Diff
    if [ "$cpy_out" = "$maude_norm" ]; then
        echo "PASS  $name"
        PASS=$((PASS + 1))
        RESULTS+=("PASS|$name|")
    else
        echo "FAIL  $name"
        echo "  CPython output:"
        echo "$cpy_out" | sed 's/^/    /'
        echo "  Maude output:"
        echo "$maude_norm" | sed 's/^/    /'
        FAIL=$((FAIL + 1))
        RESULTS+=("FAIL|$name|output-mismatch")
    fi
}

echo "=========================================="
echo "pythonlite differential test: CPython vs Maude big-step"
echo "=========================================="
for f in tests/*.py; do
    run_one "$f"
done
echo "------------------------------------------"
echo "Summary: $PASS / $TOTAL passed, $FAIL failed."

# Emit machine-readable JSON for the results summary doc to ingest.
{
    echo "{"
    echo "  \"total\": $TOTAL,"
    echo "  \"pass\":  $PASS,"
    echo "  \"fail\":  $FAIL,"
    echo "  \"per_test\": ["
    first=1
    for r in "${RESULTS[@]}"; do
        IFS='|' read -r status name reason <<< "$r"
        if [ $first -eq 1 ]; then
            first=0
        else
            echo ","
        fi
        printf '    {"name": "%s", "status": "%s", "reason": "%s"}' "$name" "$status" "$reason"
    done
    echo
    echo "  ]"
    echo "}"
} > results/last_run.json

if [ $FAIL -gt 0 ]; then exit 1; fi
exit 0
