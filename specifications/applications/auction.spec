@import;

@init
type Auction = [Aref]<a>[Afield a]a;
type Aref;
type Afield a;
type Item;
const unique created:Afield bool;
const unique open:Afield bool;
const unique closed:Afield bool;
const unique deleted:Afield bool;
const unique lots:Afield [Item]int;
const unique seller:Afield Uref;
const unique winner:Afield Bref;

type Bid = [Bref]<b>[Bfield b]b;
type Bref;
type Bfield b;
const unique user:Bfield Uref;
const unique auction:Bfield Aref;
const unique amount:Bfield int;
const unique placed:Bfield bool;
const unique removed:Bfield bool;

const unique NOBID:Bref;
axiom(forall Bids:Bid :: Bids[NOBID][user] == NULL && !Bids[NOBID][placed] && !Bids[NOBID][removed]);

type Uref;
const unique NULL:Uref;
axiom (forall U:[Uref]bool :: U[NULL] == false);

@variables
var Auctions:Auction;
var Bids:Bid;
var Users:[Uref]bool;

@equals Auction @as (forall a:Aref :: @this[a][created] == @other[a][created] && @this[a][open] == @other[a][open] && @this[a][closed] == @other[a][closed] && @this[a][deleted] == @other[a][deleted] && @this[a][seller] == @other[a][seller] && @this[a][winner] == @other[a][winner] && (forall i:Item :: @this[a][lots][i] == @other[a][lots][i]));
@equals Bid @as (forall b:Bref :: @this[b][user] == @other[b][user] && @this[b][auction] == @other[b][auction] && @this[b][amount] == @other[b][amount] && @this[b][placed] == @other[b][placed] && @this[b][removed] == @other[b][removed]);
@equals [Uref]bool @as (forall u:Uref :: @this[u] == @other[u]);

@invariant
(forall a:Aref :: Auctions[a][created] ==> Users[Auctions[a][seller]])
&& (forall a:Aref :: Auctions[a][deleted] ==> Auctions[a][created] && !Auctions[a][open] && !Auctions[a][closed])
&& (forall a:Aref :: Auctions[a][open] ==> (Auctions[a][created] && !Auctions[a][deleted]))
&& (forall a:Aref :: Auctions[a][closed] ==> (Auctions[a][created] && Auctions[a][open] && !Auctions[a][deleted] && Auctions[a][winner] != NOBID))
&& (forall a:Aref :: (exists i:Item :: Auctions[a][lots][i] > 0) ==> Auctions[a][created] && !Auctions[a][deleted])
&& (forall b:Bref :: Bids[b][placed] ==> (Auctions[Bids[b][auction]][created] && !Auctions[Bids[b][auction]][deleted] && Auctions[Bids[b][auction]][open] && Users[Bids[b][user]]))
&& (forall b:Bref :: Bids[b][removed] ==> (Auctions[Bids[b][auction]][created] && !Auctions[Bids[b][auction]][deleted] && Auctions[Bids[b][auction]][open] && Bids[b][placed]))
&& (forall a:Aref :: Auctions[a][winner] != NOBID ==> Auctions[a][created] && !Auctions[a][deleted] && Auctions[a][open] && Auctions[a][closed])
&& (forall a:Aref, wb:Bref :: wb != NOBID && Auctions[a][winner] == wb ==> (Bids[wb][auction] == a && Users[Bids[wb][user]] && Bids[wb][placed] && !Bids[wb][removed] && !(exists b:Bref :: Bids[b][auction] == a && Bids[b][amount] > Bids[wb][amount] && Bids[b][placed] && !Bids[b][removed])));

@operations
procedure createAuction(auctionid:Aref, userid:Uref)
modifies Auctions;
requires !Auctions[auctionid][created] && Auctions[auctionid][seller] == userid && Users[userid];
ensures (forall a:Aref :: (a == auctionid ==> (Auctions[a][created] == true && Auctions[a][open] == false && Auctions[a][closed] == false && Auctions[a][deleted] == false && Auctions[a][seller] == userid && Auctions[a][winner] == NOBID && (forall i:Item :: Auctions[a][lots][i] == 0))) && (a != auctionid ==> (Auctions[a][created] == old(Auctions)[a][created] && Auctions[a][open] == old(Auctions)[a][open] && Auctions[a][closed] == old(Auctions)[a][closed] && Auctions[a][deleted] == old(Auctions)[a][deleted] && Auctions[a][seller] == old(Auctions)[a][seller] && Auctions[a][winner] == old(Auctions)[a][winner] && (forall i:Item :: Auctions[a][lots][i] == old(Auctions)[a][lots][i]))));

procedure deleteAuction(auctionid:Aref, userid:Uref)
modifies Auctions;
requires Auctions[auctionid][created] && !Auctions[auctionid][open] && Auctions[auctionid][seller] == userid && !(exists i:Item :: Auctions[auctionid][lots][i] > 0);
ensures (forall a:Aref :: (a == auctionid ==> (Auctions[a][created] == old(Auctions)[a][created] && Auctions[a][open] == old(Auctions)[a][open] && Auctions[a][closed] == old(Auctions)[a][closed] && Auctions[a][deleted] == true && Auctions[a][seller] == userid && Auctions[a][winner] == old(Auctions)[a][winner] && (forall i:Item :: Auctions[a][lots][i] == old(Auctions)[a][lots][i]))) && (a != auctionid ==> (Auctions[a][created] == old(Auctions)[a][created] && Auctions[a][open] == old(Auctions)[a][open] && Auctions[a][closed] == old(Auctions)[a][closed] && Auctions[a][deleted] == old(Auctions)[a][deleted] && Auctions[a][seller] == old(Auctions)[a][seller] && Auctions[a][winner] == old(Auctions)[a][winner] && (forall i:Item :: Auctions[a][lots][i] == old(Auctions)[a][lots][i]))));

procedure startAuction(auctionid:Aref, userid:Uref)
modifies Auctions;
requires Auctions[auctionid][created] && !Auctions[auctionid][deleted] && Auctions[auctionid][seller] == userid && (exists i:Item :: Auctions[auctionid][lots][i] > 0);
ensures (forall a:Aref :: (a == auctionid ==> (Auctions[a][created] == old(Auctions)[a][created] && Auctions[a][open] == true && Auctions[a][closed] == old(Auctions)[a][closed] && Auctions[a][deleted] == old(Auctions)[a][deleted] && Auctions[a][seller] == userid && Auctions[a][winner] == old(Auctions)[a][winner] && (forall i:Item :: Auctions[a][lots][i] == old(Auctions)[a][lots][i]))) && (a != auctionid ==> (Auctions[a][created] == old(Auctions)[a][created] && Auctions[a][open] == old(Auctions)[a][open] && Auctions[a][closed] == old(Auctions)[a][closed] && Auctions[a][deleted] == old(Auctions)[a][deleted] && Auctions[a][seller] == old(Auctions)[a][seller] && Auctions[a][winner] == old(Auctions)[a][winner] && (forall i:Item :: Auctions[a][lots][i] == old(Auctions)[a][lots][i]))));

procedure closeAuction(auctionid:Aref, userid:Uref, winbid:Bref)
modifies Auctions;
requires Auctions[auctionid][open] && Auctions[auctionid][seller] == userid && Users[Bids[winbid][user]] && Bids[winbid][auction] == auctionid && Bids[winbid][placed] && !Bids[winbid][removed] && !(exists b:Bref :: Bids[b][auction] == auctionid && Bids[b][placed] && !Bids[b][removed] && Bids[b][amount] > Bids[winbid][amount]);
ensures (forall a:Aref :: (a == auctionid ==> (Auctions[a][created] == old(Auctions)[a][created] && Auctions[a][open] == old(Auctions)[a][open] && Auctions[a][closed] == true && Auctions[a][deleted] == old(Auctions)[a][deleted] && Auctions[a][seller] == userid && Auctions[a][winner] == winbid && (forall i:Item :: Auctions[a][lots][i] == old(Auctions)[a][lots][i]))) && (a != auctionid ==> (Auctions[a][created] == old(Auctions)[a][created] && Auctions[a][open] == old(Auctions)[a][open] && Auctions[a][closed] == old(Auctions)[a][closed] && Auctions[a][deleted] == old(Auctions)[a][deleted] && Auctions[a][seller] == old(Auctions)[a][seller] && Auctions[a][winner] == old(Auctions)[a][winner] && (forall i:Item :: Auctions[a][lots][i] == old(Auctions)[a][lots][i]))));

procedure addlot(auctionid:Aref, product:Item, qty:int, userid:Uref)
modifies Auctions;
requires Auctions[auctionid][created] && !Auctions[auctionid][open] && !Auctions[auctionid][deleted] && Auctions[auctionid][seller] == userid;
ensures (forall a:Aref :: (a == auctionid ==> (Auctions[a][created] == old(Auctions)[a][created] && Auctions[a][open] == old(Auctions)[a][open] && Auctions[a][closed] == old(Auctions)[a][closed] && Auctions[a][deleted] == old(Auctions)[a][deleted] && Auctions[a][seller] == old(Auctions)[a][seller] && Auctions[a][winner] == old(Auctions)[a][winner] && (forall i:Item :: (i == product ==> Auctions[a][lots][i] == qty) && (i != product ==> Auctions[a][lots][i] == old(Auctions)[a][lots][i])))) && (a != auctionid ==> (Auctions[a][created] == old(Auctions)[a][created] && Auctions[a][open] == old(Auctions)[a][open] && Auctions[a][closed] == old(Auctions)[a][closed] && Auctions[a][deleted] == old(Auctions)[a][deleted] && Auctions[a][seller] == old(Auctions)[a][seller] && Auctions[a][winner] == old(Auctions)[a][winner] && (forall i:Item :: Auctions[a][lots][i] == old(Auctions)[a][lots][i]))));

procedure removeLot(auctionid:Aref, product:Item, userid:Uref)
modifies Auctions;
requires Auctions[auctionid][created] && !Auctions[auctionid][open] && !Auctions[auctionid][deleted] && Auctions[auctionid][lots][product] > 0  && Auctions[auctionid][seller] == userid;
ensures  (forall a:Aref :: (a == auctionid ==> (Auctions[a][created] == old(Auctions)[a][created] && Auctions[a][open] == old(Auctions)[a][open] && Auctions[a][closed] == old(Auctions)[a][closed] && Auctions[a][deleted] == old(Auctions)[a][deleted] && Auctions[a][seller] == userid && Auctions[a][winner] == old(Auctions)[a][winner] && (forall i:Item :: (i == product ==> Auctions[a][lots][i] == 0) && (i != product ==> Auctions[a][lots][i] == old(Auctions)[a][lots][i])))) && (a != auctionid ==> (Auctions[a][created] == old(Auctions)[a][created] && Auctions[a][open] == old(Auctions)[a][open] && Auctions[a][closed] == old(Auctions)[a][closed] && Auctions[a][deleted] == old(Auctions)[a][deleted] && Auctions[a][seller] == old(Auctions)[a][seller] && Auctions[a][winner] == old(Auctions)[a][winner] && (forall i:Item :: Auctions[a][lots][i] == old(Auctions)[a][lots][i]))));

procedure placeBid(auctionid:Aref, bidid:Bref, userid:Uref, offer:int)
modifies Bids;
requires Auctions[auctionid][open] && !Auctions[auctionid][closed] && Bids[bidid][user] == userid && Bids[bidid][placed] == false && Users[userid];
ensures (forall b:Bref :: (b == bidid ==> Bids[b][user] == userid && Bids[b][auction] == auctionid && Bids[b][amount] == offer && Bids[b][placed] == true && Bids[b][removed] == false) && (b != bidid ==> Bids[b][user] == old(Bids)[b][user] && Bids[b][auction] == old(Bids)[b][auction] && Bids[b][amount] == old(Bids)[b][amount] && Bids[b][placed] == old(Bids)[b][placed] && Bids[b][removed] == old(Bids)[b][removed]));

procedure removeBid(bidid:Bref, userid:Uref)
modifies Bids;
requires Bids[bidid][user] == userid && Bids[bidid][placed] == true && Auctions[Bids[bidid][auction]][open] && !Auctions[Bids[bidid][auction]][closed];
ensures (forall b:Bref :: (b == bidid ==> Bids[b][user] == userid && Bids[b][auction] == old(Bids)[b][auction] && Bids[b][amount] == old(Bids)[b][amount] && Bids[b][placed] == old(Bids)[b][placed] && Bids[b][removed] == true) && (b != bidid ==> Bids[b][user] == old(Bids)[b][user] && Bids[b][auction] == old(Bids)[b][auction] && Bids[b][amount] == old(Bids)[b][amount] && Bids[b][placed] == old(Bids)[b][placed] && Bids[b][removed] == old(Bids)[b][removed]));

