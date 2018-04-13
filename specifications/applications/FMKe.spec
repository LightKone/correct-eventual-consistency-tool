@import;

@init
type CrdtFlag = bool;
function setFlag(flag:CrdtFlag) returns(bool)
{
 flag
}
function resetFlag(flag:CrdtFlag, oldFlag:CrdtFlag) returns(bool)
{
 if (oldFlag) then flag else !flag
}	
type Gset = <a>[a]CrdtFlag;
type Gcounter = int;
function inc(ctr:Gcounter, oldCtr:Gcounter) returns(bool)
{
  ctr == oldCtr + 1
}

type String;
type Eref;
type EntityField a;
type RxRef;
type Medication;
type Field a;
type Rx = <a>[RxRef][Field a]a;
const unique doctor :Field Eref;
const unique patient : Field Eref;
const unique pharma : Field Eref;
const unique medications : Field Gset;
const unique isSealed : Field CrdtFlag;
const unique numProcessed : Field Gcounter;
axiom (forall <a> f:Field a :: f == doctor || f == patient || f == pharma || f == medications || f == isSealed || f == numProcessed);

type Entity = <a>[Eref][EntityField a]a;
const unique name :EntityField String;
const unique prescriptions : EntityField Gset;


@variables
var Prescriptions:Rx;
var flag:[RxRef]bool;
var Doctors:Entity;
var Pharmas:Entity;
var Patients:Entity;

@equals Rx @as (forall rx:RxRef :: (@this[rx][doctor] == @other[rx][doctor] && @this[rx][patient] == @other[rx][patient] && @this[rx][pharma] == @other[rx][pharma] && (forall m:Medication :: @this[rx][medications][m] ==  @other[rx][medications][m]) && @this[rx][isSealed] == @other[rx][isSealed] && @this[rx][numProcessed] == @other[rx][numProcessed]));
@equals [RxRef]bool @as (forall rx:RxRef :: (@this[rx] == @other[rx]));
@equals Entity @as (forall e:Eref:: @this[e][name] == @other[e][name] && (forall p:RxRef :: @this[e][prescriptions][p] == @other[e][prescriptions][p]));

@invariant
(forall pres:RxRef :: Doctors[Prescriptions[pres][doctor]][prescriptions][pres])
&& (forall pres:RxRef :: (Prescriptions[pres][isSealed] ==> (exists m:Medication :: Prescriptions[pres][medications][m])))
&& (forall pres:RxRef :: (Prescriptions[pres][isSealed] ==> Patients[Prescriptions[pres][patient]][prescriptions][pres]))
&& (forall pres:RxRef :: (Prescriptions[pres][isSealed] ==> Pharmas[Prescriptions[pres][pharma]][prescriptions][pres]))
&& (forall pres:RxRef :: (Prescriptions[pres][numProcessed] >= 0) && (Prescriptions[pres][numProcessed] <= 1))
&& (forall pres:RxRef :: (Prescriptions[pres][numProcessed] > 0) ==> Prescriptions[pres][isSealed]);

@operations

procedure createRx(dr:Eref, pt:Eref, ph:Eref, pres:RxRef)
modifies Prescriptions, Doctors, flag;
requires flag[pres] == false;
ensures (flag[pres] == true && (forall r:RxRef :: r != pres ==> (flag[r] == old(flag)[r])))

&& (Prescriptions[pres][doctor] == dr && Prescriptions[pres][patient] == pt && Prescriptions[pres][pharma] == ph && Prescriptions[pres][isSealed] == false && (forall m:Medication :: Prescriptions[pres][medications][m] == false) && Prescriptions[pres][numProcessed] == 0 && (forall r:RxRef :: r != pres ==> ((Prescriptions[r][doctor] == old(Prescriptions)[r][doctor]) && (Prescriptions[r][patient] == old(Prescriptions)[r][patient]) && (Prescriptions[r][pharma] == old(Prescriptions)[r][pharma]) && (Prescriptions[r][isSealed] == old(Prescriptions)[r][isSealed]) && (Prescriptions[r][numProcessed] == old(Prescriptions)[r][numProcessed]) && (forall m:Medication :: Prescriptions[r][medications][m] == old(Prescriptions)[r][medications][m]))))

&& ((forall d:Eref :: Doctors[d][name] == old(Doctors)[d][name]) && (forall d:Eref, p:RxRef :: ((d != dr || p != pres) ==> Doctors[d][prescriptions][p] == old(Doctors)[d][prescriptions][p])) && Doctors[dr][prescriptions][pres] == true);

procedure addMedication(pres:RxRef, medicine:Medication, dr:Eref)
modifies Prescriptions;
requires flag[pres] && !Prescriptions[pres][isSealed] && Prescriptions[pres][doctor] == dr;
ensures (Prescriptions[pres][medications][medicine] == true && (forall m:Medication :: m != medicine ==> Prescriptions[pres][medications][m] == old(Prescriptions)[pres][medications][m]) && Prescriptions[pres][doctor] == old(Prescriptions)[pres][doctor] && Prescriptions[pres][patient] == old(Prescriptions)[pres][patient]  && Prescriptions[pres][pharma] == old(Prescriptions)[pres][pharma]  && Prescriptions[pres][isSealed] == old(Prescriptions)[pres][isSealed]  && Prescriptions[pres][numProcessed] == old(Prescriptions)[pres][numProcessed] && (forall r:RxRef :: r != pres ==> ((Prescriptions[r][doctor] == old(Prescriptions)[r][doctor]) && (Prescriptions[r][patient] == old(Prescriptions)[r][patient]) && (Prescriptions[r][pharma] == old(Prescriptions)[r][pharma]) && (Prescriptions[r][isSealed] == old(Prescriptions)[r][isSealed]) && (Prescriptions[r][numProcessed] == old(Prescriptions)[r][numProcessed]) && (forall m:Medication :: Prescriptions[r][medications][m] == old(Prescriptions)[r][medications][m]))));

procedure sealRx(pres:RxRef, dr:Eref)
modifies Prescriptions, Patients, Pharmas;
requires flag[pres] && (exists m:Medication :: Prescriptions[pres][medications][m]) && Prescriptions[pres][doctor] == dr;
ensures (Prescriptions[pres][isSealed] == true && (forall r:RxRef :: r != pres ==> Prescriptions[r][isSealed] == old(Prescriptions)[r][isSealed]) && (forall r:RxRef :: (Prescriptions[r][doctor] == old(Prescriptions)[r][doctor]) && (Prescriptions[r][patient] == old(Prescriptions)[r][patient]) && (Prescriptions[r][pharma] == old(Prescriptions)[r][pharma]) && (Prescriptions[r][numProcessed] == old(Prescriptions)[r][numProcessed]) && (forall m:Medication :: Prescriptions[r][medications][m] == old(Prescriptions)[r][medications][m])))

&& ((forall p:Eref :: Patients[p][name] == old(Patients)[p][name]) && (forall p:Eref, r:RxRef :: ((p != Prescriptions[pres][patient] || r != pres) ==> Patients[p][prescriptions][r] == old(Patients)[p][prescriptions][r])) && Patients[Prescriptions[pres][patient]][prescriptions][pres] == true)

&& ((forall p:Eref :: Pharmas[p][name] == old(Pharmas)[p][name]) && (forall p:Eref, r:RxRef :: ((p != Prescriptions[pres][pharma] || r != pres) ==> Pharmas[p][prescriptions][r] == old(Pharmas)[p][prescriptions][r])) && Pharmas[Prescriptions[pres][pharma]][prescriptions][pres] == true);

procedure processRx(pres:RxRef, ph:Eref)
modifies Prescriptions;
requires flag[pres] && Prescriptions[pres][isSealed] && (exists m:Medication :: Prescriptions[pres][medications][m]) && Prescriptions[pres][numProcessed] == 0;
ensures (inc(Prescriptions[pres][numProcessed], old(Prescriptions)[pres][numProcessed]) && (forall r:RxRef :: r != pres ==> Prescriptions[r][numProcessed] == old(Prescriptions)[r][numProcessed]) && (forall r:RxRef :: ((Prescriptions[r][doctor] == old(Prescriptions)[r][doctor]) && (Prescriptions[r][patient] == old(Prescriptions)[r][patient]) && (Prescriptions[r][pharma] == old(Prescriptions)[r][pharma]) && (Prescriptions[r][isSealed] == old(Prescriptions)[r][isSealed]) && (forall m:Medication :: Prescriptions[r][medications][m] == old(Prescriptions)[r][medications][m]))));
