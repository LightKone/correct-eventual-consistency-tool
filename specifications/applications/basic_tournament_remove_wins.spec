@import RemWinsSet;

@init
type Player;
type Tournament;

@variables
var enrollments : [Player, Tournament]bool;
var tournaments : RemWinsSet;
var players : RemWinsSet;

@equals [Player, Tournament]bool @as forall p: Player, t: Tournament :: @this[p,t] == @other[p,t];

@invariant
forall p: Player, t: Tournament :: enrollments[p, t] ==> remWinsSetIn(p, players) && remWinsSetIn(t, tournaments);


@operations

procedure addTournament(t1: Tournament)
    modifies tournaments;
    ensures remWinsSetAdd(t1, tournaments, old(tournaments));


procedure remTournament(t1: Tournament)
    modifies tournaments;
    requires !(exists p: Player :: enrollments[p, t1]);
    ensures remWinsSetRemove(t1, tournaments, old(tournaments));

procedure enroll(p1: Player, t1: Tournament)
    modifies enrollments;
    requires
        remWinsSetIn(t1, tournaments) == true &&
        remWinsSetIn(p1, players) == true;
    ensures
        forall t: Tournament, p: Player ::
        ((p != p1 || t != t1) ==> (enrollments[p, t] == old(enrollments)[p, t])) &&
        ((p == p1 && t == t1) ==> (enrollments[p1, t1] == true));
