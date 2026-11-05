ATK_DESC="drop a test's line from scripts/tests-map.txt (its dependencies no longer select it)"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { sed -i '/^scripts\/test_githook.sh:/d' scripts/tests-map.txt; }
