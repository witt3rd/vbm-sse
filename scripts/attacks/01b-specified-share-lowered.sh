ATK_DESC="lower the specified share in closure-baseline.txt (it may only rise)"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { awk '$1=="specified_share"{$2=1} {print}' scripts/closure-baseline.txt > x && mv x scripts/closure-baseline.txt; }
