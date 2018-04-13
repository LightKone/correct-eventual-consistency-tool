@type datatype
@name EnableWinsFlag


@content

type EnWinsFlagSelector;
const unique EnWinsFlagEnable: EnWinsFlagSelector;
const unique EnWinsFlagDisable: EnWinsFlagSelector;
axiom(forall s:EnWinsFlagSelector :: s == EnWinsFlagEnable || s == EnWinsFlagDisable);

type EnWinsFlagElement = bool;
type EnableWinsFlag = [EnWinsFlagSelector]EnWinsFlagElement;

function enable(flag: EnableWinsFlag, oldFlag: EnableWinsFlag) returns(bool)
{
    (flag[EnWinsFlagEnable] == true) && (flag[EnWinsFlagDisable] == oldFlag[EnWinsFlagDisable])
}

function disable(flag: EnableWinsFlag, oldFlag: EnableWinsFlag) returns(bool)
{
    (flag[EnWinsFlagDisable] == true) && (flag[EnWinsFlagEnable] == oldFlag[EnWinsFlagEnable])
}

function status(flag: EnableWinsFlag) returns(bool)
{
    (flag[EnWinsFlagEnable])
}

function initialiseFlag(flag: EnableWinsFlag) returns(bool)
{
    (flag[EnWinsFlagEnable] == false) && (flag[EnWinsFlagDisable] == false)
}

function flagequals(one:EnableWinsFlag, two:EnableWinsFlag) returns(bool)
{
    (one[EnWinsFlagEnable] == two[EnWinsFlagEnable]) && (one[EnWinsFlagDisable] == two[EnWinsFlagDisable])
}		

@equals forall s: EnWinsFlagSelector :: @this[s] == @other[s];
