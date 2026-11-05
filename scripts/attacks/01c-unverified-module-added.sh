ATK_DESC="add an unverified module line to closure-baseline.txt (an unknown key is a raise)"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { echo 'LeanSse.Atk 12' >> scripts/closure-baseline.txt; }
