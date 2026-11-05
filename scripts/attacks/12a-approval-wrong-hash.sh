ATK_DESC="remove a tier1.sh line with an approval list that names scripts/tier1.sh but carries the hash of ANOTHER diff (an approval is the exact diff)"
ATK_GATES=('l=$(mktemp); echo "scripts/tier1.sh 0000000000000000000000000000000000000000000000000000000000000000" > "$l"; LAND_GATE_APPROVED_FILE=$l scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh); ATK_EXPECT='removed/changed'
atk_apply() { n=$(first_line_matching scripts/tier1.sh 'cannot'); sed -i "${n}d" scripts/tier1.sh; }
