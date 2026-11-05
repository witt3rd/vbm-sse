ATK_DESC="neuter scripts/select-tests.py (a stub that always succeeds): its self-test scripts/test_select_tests.sh must FAIL (a gate whose self-test cannot fail)"
ATK_GATES=('scripts/test_select_tests.sh'); ATK_GATE_FILES=(scripts/test_select_tests.sh)
atk_apply() { neuter scripts/select-tests.py; }
