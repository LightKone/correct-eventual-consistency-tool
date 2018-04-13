@init
type ISBN;
type UserId;
type OrderId;
type Field a;
type Order = [OrderId]<a>[Field a]a;
const unique user: Field UserId;
const unique items: Field [ISBN]int;
const unique created:Field bool;
const unique placed:Field bool;
const unique cancelled:Field bool;
const unique processed: Field bool;

axiom(forall orders:Order, o:OrderId :: orders[o][created] == false ==> (orders[o][placed] == false && orders[o][cancelled] == false && orders[o][processed] == false && (forall b:ISBN :: orders[o][items][b] == 0)));
function max(a:int, b:int) returns(int)
{
  (if a > b then a else b)
}

function positiveStock(BookStore:[ISBN]int) returns(bool)
{
  (forall b:ISBN :: BookStore[b] >= 0)
}
function oderCreationByRegCustomers(UserOrders:Order, Users:[UserId]bool) returns(bool)
{
  (forall o:OrderId :: UserOrders[o][created] ==> Users[UserOrders[o][user]])
}
function orderUpdateAfterCreation(UserOrders:Order) returns(bool)
{
  (forall o:OrderId :: (exists i:ISBN :: UserOrders[o][items][i] > 0) ==> UserOrders[o][created])
}
function ordersPlacedAfterUpdation(UserOrders:Order) returns(bool)
{
  (forall o:OrderId :: UserOrders[o][placed] ==> UserOrders[o][created] && (exists i:ISBN :: UserOrders[o][items][i] > 0))
}
function orderCancelledAfterPlaceNotProcessed(UserOrders:Order) returns(bool)
{
  (forall o:OrderId :: UserOrders[o][cancelled] ==> UserOrders[o][placed] && !UserOrders[o][processed])
}
function orderProcessedAfterPlaceNotCancelled(UserOrders:Order) returns(bool)
{
  (forall o:OrderId :: UserOrders[o][processed] ==> UserOrders[o][placed] && !UserOrders[o][cancelled])
}

@variables
var BookStore:[ISBN]int;
var UserOrders:Order;
var Users:[UserId]bool;

@equals [ISBN]int @as (forall i:ISBN :: @this[i] == @other[i]);
@equals Order @as (forall o:OrderId :: @this[o][user] == @other[o][user] && @this[o][created] == @other[o][created] && @this[o][placed] == @other[o][placed] && @this[o][cancelled] == @other[o][cancelled] && @this[o][processed] == @other[o][processed] && (forall i:ISBN :: @this[o][items][i] == @other[o][items][i]));
@equals [UserId]bool @as (forall u:UserId :: @this[u] == @other[u]);

@invariant
positiveStock(BookStore) && oderCreationByRegCustomers(UserOrders, Users) && orderUpdateAfterCreation(UserOrders) && ordersPlacedAfterUpdation(UserOrders) && orderCancelledAfterPlaceNotProcessed(UserOrders) && orderProcessedAfterPlaceNotCancelled(UserOrders);

@operations

procedure createOrder(id:OrderId, usr:UserId)
modifies UserOrders;
requires UserOrders[id][created] == false && UserOrders[id][user] == usr && Users[usr] == true;
ensures (forall o:OrderId :: (o == id ==> (UserOrders[o][created] == true && UserOrders[o][user] == usr && UserOrders[o][placed] == false && UserOrders[o][cancelled] == false && UserOrders[o][processed] == false && (forall b:ISBN :: UserOrders[o][items][b] == 0))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))));

procedure updateOrder(id:OrderId, usr:UserId, book:ISBN, qty:int)
modifies UserOrders;
requires qty >= 0 && UserOrders[id][created] == true && UserOrders[id][placed] == false && UserOrders[id][user] == usr;
ensures (forall o:OrderId :: (o == id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == false && UserOrders[o][cancelled] == false && UserOrders[o][processed] == false && (forall b:ISBN :: (b == book ==> UserOrders[o][items][b] == qty) && (b != book ==> UserOrders[o][items][b] == old(UserOrders)[o][items][b])))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))));

procedure placeOrder(id:OrderId, usr:UserId)
modifies UserOrders;
requires (exists b:ISBN :: UserOrders[id][items][b] > 0) && UserOrders[id][user] == usr;
ensures (forall o:OrderId :: (o == id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == true && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))));

procedure cancelOrder(id:OrderId, usr:UserId)
modifies UserOrders;
requires UserOrders[id][placed] == true && UserOrders[id][processed] == false && UserOrders[id][user] == usr;
ensures (forall o:OrderId :: (o == id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == true && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))));

procedure processOrder(id:OrderId)
modifies UserOrders, BookStore;
requires UserOrders[id][placed] == true && UserOrders[id][processed] == false && UserOrders[id][cancelled] == false && (forall b:ISBN :: BookStore[b] >= UserOrders[id][items][b]);
ensures (forall b:ISBN :: BookStore[b] == old(BookStore)[b] - UserOrders[id][items][b]) && (forall o:OrderId :: (o == id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == true && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))));

procedure purchaseStock(book:ISBN, qty:int)
modifies BookStore;
requires qty >= 0;
ensures (forall b:ISBN :: (b == book ==> (BookStore[b] == old(BookStore)[b] + qty)) && (b != book ==> (BookStore[b] == old(BookStore)[b])));

procedure registerUser(user:UserId)
modifies Users;
requires Users[user] == false;
ensures (forall u:UserId :: (u == user ==> Users[user] == true) && (u != user ==> Users[user] == old(Users)[user]));
