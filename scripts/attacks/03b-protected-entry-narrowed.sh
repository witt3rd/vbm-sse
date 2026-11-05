ATK_DESC="narrow an entry (LeanSse/ to one file) in scripts/protected-paths.txt"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { sed -i 's|^LeanSse/$|LeanSse/Value.lean|' scripts/protected-paths.txt; }
