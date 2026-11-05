ATK_DESC="neuter the drift check scripts/land/bin/land-check (a stub that always succeeds): scripts/test_land_direct.sh must FAIL (a check whose self-test cannot fail)"
ATK_GATES=('scripts/test_land_direct.sh'); ATK_GATE_FILES=(scripts/test_land_direct.sh)
atk_apply() { neuter scripts/land/bin/land-check; }
