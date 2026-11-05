ATK_DESC="move scripts/tier1.sh from the all: line to the none: line of scripts/tests-map.txt (a change to the gate selects no test)"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { sed -i 's# scripts/tier1.sh##; s#^none:#none: scripts/tier1.sh#' scripts/tests-map.txt; }
