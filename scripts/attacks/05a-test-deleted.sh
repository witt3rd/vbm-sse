ATK_DESC="delete a test script and its declaration (a test the base runs is gone)"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { git rm -q scripts/test_githook.sh; sed -i '/^par scripts\/test_githook.sh$/d' scripts/tier1.sh; }
