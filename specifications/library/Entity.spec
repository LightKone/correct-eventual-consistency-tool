@type datatype
@name Entity

@content

type Eref;
type Efield a;
type String;
type Entity = <a>[Eref][Efield a]a;
const unique name : Efield String;
const unique prescriptions : Efield Gset;
axiom(forall <a> f:Efield a :: f == name || f == prescriptions);

@equals (forall r:Eref :: @this[r][name] == @other[r][name] && (forall x:RxRef :: @this[r][prescriptions][x] == @other[r][prescriptions][x]));

