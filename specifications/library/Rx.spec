@type datatype
@name Rx

@content

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

function noChangePrescription(Prescriptions:Rx, oldPrescriptions:Rx, rx:RxRef) returns(bool)
{
  ((Prescriptions[rx][doctor] == oldPrescriptions[rx][doctor])
	&& (Prescriptions[rx][patient] == oldPrescriptions[rx][patient])
	&& (Prescriptions[rx][pharma] == oldPrescriptions[rx][pharma])
	&& (forall m:Medication :: Prescriptions[rx][medications][m] == oldPrescriptions[rx][medications][m])
	&& (Prescriptions[rx][isSealed] == oldPrescriptions[rx][isSealed])
	&& counterEquals(Prescriptions[rx][numProcessed], oldPrescriptions[rx][numProcessed]))
}	

@equals (forall rx:RxRef :: (@this[rx][doctor] == @other[rx][doctor]) && (@this[rx][patient] == @other[rx][patient]) && (@this[rx][pharma] == @other[rx][pharma]) && (@this[rx][isSealed] == @other[rx][isSealed]) && counterEquals(@this[rx][numProcessed], @other[rx][numProcessed]) && (forall m:Medication:: @this[rx][medications][m] == @other[rx][medications][m]));
