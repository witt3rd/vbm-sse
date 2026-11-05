ATK_DESC="neuter scripts/land-direct (a stub that always succeeds): its self-test scripts/test_land_direct.sh must FAIL (a gate whose self-test cannot fail)"
ATK_GATES=('scripts/test_land_direct.sh'); ATK_GATE_FILES=(scripts/test_land_direct.sh)
atk_apply() { neuter scripts/land-direct; }
