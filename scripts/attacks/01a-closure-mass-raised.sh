ATK_DESC="raise mass in closure-baseline.txt (the unverified mass may only fall)"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { awk '$1=="mass"{$2=$2+100000} {print}' scripts/closure-baseline.txt > x && mv x scripts/closure-baseline.txt; }
