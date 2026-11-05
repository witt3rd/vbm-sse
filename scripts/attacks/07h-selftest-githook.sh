ATK_DESC="neuter scripts/githooks/pre-commit (a stub that always succeeds): its self-test scripts/test_githook.sh must FAIL"
ATK_GATES=('CI=1 scripts/test_githook.sh'); ATK_GATE_FILES=(scripts/test_githook.sh)
atk_apply() { neuter scripts/githooks/pre-commit; }
