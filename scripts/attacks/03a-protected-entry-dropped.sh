ATK_DESC="drop an entry (LeanSse/) from scripts/protected-paths.txt"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { sed -i '/^LeanSse\/$/d' scripts/protected-paths.txt; }
