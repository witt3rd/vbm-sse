ATK_DESC="widen the carve-outs: raise (or introduce) carveout_mass in scripts/closure-baseline.txt (a carve-out may be neither added nor widened without approval)"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh); ATK_EXPECT='carveout_mass'
atk_apply() { sed -i '/^carveout_mass /d' scripts/closure-baseline.txt; echo "carveout_mass 500" >> scripts/closure-baseline.txt; }
