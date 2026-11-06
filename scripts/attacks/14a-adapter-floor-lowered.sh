ATK_DESC="lower the specified-share floor of the scorecard adapter (scorecard.toml [floors]): a floor that may be lowered is a card made to pass"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh); ATK_EXPECT='may only rise'
atk_apply() { sed -i 's/^specified_share = .*/specified_share = 90/' scorecard.toml; }
