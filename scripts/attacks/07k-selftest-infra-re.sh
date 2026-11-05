ATK_DESC="neuter the pinned infra classifier scripts/land/lib/infra-re.sh (a sourced classifier that exits ends the lander with success): scripts/test_land_direct.sh must FAIL (the vendored copy no longer matches its pin)"
ATK_GATES=('scripts/test_land_direct.sh'); ATK_GATE_FILES=(scripts/test_land_direct.sh)
atk_apply() { neuter scripts/land/lib/infra-re.sh; }
