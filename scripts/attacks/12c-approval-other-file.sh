ATK_DESC="drop a line of scripts/tests-map.txt with an approval list that names that file with the TRUE hash of its diff (an approval relaxes scripts/tier1.sh only)"
ATK_GATES=('h=$(bash -c ". scripts/land/lib/approvals.sh; ga_hash . \"$ATK_BASE\" HEAD scripts/tests-map.txt"); l=$(mktemp); echo "scripts/tests-map.txt $h" > "$l"; LAND_GATE_APPROVED_FILE=$l scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh); ATK_EXPECT='tests-map'
atk_apply() { sed -i '/^scripts\/test_abi.sh:/d' scripts/tests-map.txt; }
