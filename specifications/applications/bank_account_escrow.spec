@import;

@init
type Credit = int;
type ReplicaID;
type AccountID;

@variables
var localCredit:[AccountID][ReplicaID]Credit;
var globalCredit:[AccountID]Credit;

@equals [AccountID][ReplicaID]Credit @as forall a:AccountID, r:ReplicaID :: @this[a][r] == @other[a][r];
@equals [AccountID]Credit @as forall a:AccountID :: @this[a] == @other[a];

@invariant
(forall a:AccountID, r:ReplicaID :: localCredit[a][r] >= 0 && globalCredit[a] >= 0);


@operations

procedure acquireCredit(account:AccountID, replica:ReplicaID, k:Credit)
modifies globalCredit, localCredit;
requires k > 0 && globalCredit[account] >= k;
ensures (forall a:AccountID, r:ReplicaID :: (localCredit[account][replica] == old(localCredit)[account][replica] + k) && ((a != account || r != replica) ==> (localCredit[a][r] == old(localCredit)[a][r])) && (globalCredit[account] == old(globalCredit)[account] - k)) && (forall a:AccountID :: (a != account ==> (globalCredit[a] == old(globalCredit)[a])));

procedure releaseCredit(account:AccountID, replica:ReplicaID, k:Credit)
modifies globalCredit, localCredit;
requires k > 0 && localCredit[account][replica] >= k;
ensures (forall a:AccountID, r:ReplicaID :: (localCredit[account][replica] == old(localCredit)[account][replica] - k) && ((a != account || r != replica) ==> (localCredit[a][r] == old(localCredit)[a][r])) && (globalCredit[account] == old(globalCredit)[account] + k)) && (forall a:AccountID :: (a != account ==> (globalCredit[a] == old(globalCredit)[a])));

procedure deposit(account:AccountID, replica:ReplicaID, k:Credit)
modifies localCredit;
requires k > 0;
ensures (forall a:AccountID, r:ReplicaID :: ((a == account && r == replica) ==> localCredit[a][r] == old(localCredit)[a][r] + k) && ((a != account || r != replica) ==> localCredit[a][r] == old(localCredit)[a][r]));

procedure withdraw(account:AccountID, replica:ReplicaID, k:Credit)
modifies localCredit;
requires k > 0 && localCredit[account][replica] >= k;
ensures (forall a:AccountID, r:ReplicaID :: ((a == account && r == replica) ==> localCredit[a][r] == old(localCredit)[a][r] - k) && ((a != account || r != replica) ==> localCredit[a][r] == old(localCredit)[a][r]));
