@import AddWinsSet;

@init
type Player;
type Tournament;

@variables
var enrollments : [Player, Tournament]bool;
var tournaments : AddWinsSet;
var players : AddWinsSet;

@equals [Player, Tournament]bool @as forall p: Player, t: Tournament :: @this[p,t] == @other[p,t];

@invariant
forall p: Player, t: Tournament :: enrollments[p, t] ==> inSet(p, players) && inSet(t, tournaments);


@operations

procedure addTournament(t1: Tournament)
    modifies tournaments;
    ensures add(t1, tournaments, old(tournaments));


procedure remTournament(t1: Tournament)
    modifies tournaments;
    requires !(exists p: Player :: enrollments[p, t1]);
    ensures remove(t1, tournaments, old(tournaments));

procedure enroll(p1: Player, t1: Tournament)
    modifies enrollments;
    requires
        inSet(t1, tournaments) == true &&
        inSet(p1, players) == true;
    ensures
        forall t: Tournament, p: Player ::
        ((p != p1 || t != t1) ==> (enrollments[p, t] == old(enrollments)[p, t])) &&
        ((p == p1 && t == t1) ==> (enrollments[p1, t1] == true));
