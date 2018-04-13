@type unit
@name invariantsFmke

@content

function doctorRxRelation(Doctors:Entity, Prescriptions:Rx) returns(bool)
{
  (forall pres:RxRef :: gsetContains(pres, Doctors[Prescriptions[pres][doctor]][prescriptions]))
}
// function patientRxRelation(Patients:Entity, Prescriptions:Rx) returns(bool)
// {
//   (forall pres:RxRef :: !gsetContains(pres, Patients[Prescriptions[pres][patient]][prescriptions])
// 	==> !status(Prescriptions[pres][isSealed]))
// }	
function rxPatientRelation(Patients:Entity, Prescriptions:Rx) returns(bool)
{
  (forall pres:RxRef :: status(Prescriptions[pres][isSealed])
	==> gsetContains(pres, Patients[Prescriptions[pres][patient]][prescriptions]))
}
// function pharmaRxRelation(Pharmas:Entity, Prescriptions:Rx) returns(bool)
// {
//   (forall pres:RxRef :: !gsetContains(pres, Pharmas[Prescriptions[pres][pharma]][prescriptions])
// 	==> !status(Prescriptions[pres][isSealed]))
// }
function rxPharmaRelation(Pharmas:Entity, Prescriptions:Rx) returns(bool)
{
	(forall pres:RxRef :: status(Prescriptions[pres][isSealed])
	==> gsetContains(pres, Pharmas[Prescriptions[pres][pharma]][prescriptions]))
}
function numprocessBound(Prescriptions:Rx) returns(bool)
{
  (forall pres:RxRef :: ((value(Prescriptions[pres][numProcessed]) >= 0) && (value(Prescriptions[pres][numProcessed])  <= 1)))
}	
function sealingCondition(Prescriptions:Rx) returns(bool)
{
  (forall pres:RxRef :: (status(Prescriptions[pres][isSealed]) ==> !gsetEmpty(Prescriptions[pres][medications])))
}
function processingCondition(Prescriptions:Rx) returns(bool)
{
  (forall pres:RxRef :: ((value(Prescriptions[pres][numProcessed]) > 0) ==> status(Prescriptions[pres][isSealed])))
}	
