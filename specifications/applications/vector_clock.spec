@import;

@init
function max(a:int, b:int) returns(int)
{
  (if a > b then a else b)
}	
@variables
var clock:[int]int;

@equals [int]int @as forall i:int ::  @this[i] == @other[i];

@invariant
true;

@operations

procedure update(id:int, value:int)
modifies clock;
requires true;
ensures (forall r:int :: (r == id ==> clock[r] == max(value, old(clock)[r])) && ( r != id ==> clock[r] == old(clock)[r]));
