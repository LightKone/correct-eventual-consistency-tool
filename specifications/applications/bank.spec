@init
type Client;

@variables
var balances : [Client]int;

@equals [Client]int @as forall c: Client :: @this[c] == @other[c];

@invariant
forall c: Client :: balances[c] >= 0;

@operations

procedure deposit(c1: Client, a1: int)
    modifies balances;
    requires a1 >= 0;
    ensures
        forall c: Client ::
        ((c != c1) ==> (balances[c] == old(balances)[c])) &&
        ((c == c1) ==> (balances[c1] == old(balances)[c1] + a1));

procedure withdraw(c1: Client, a1: int)
    modifies balances;
    requires balances[c1] - a1 >= 0;
    ensures
        forall c: Client ::
        ((c != c1) ==> (balances[c] == old(balances)[c])) &&
        ((c == c1) ==> (balances[c1] == old(balances)[c1] - a1));

