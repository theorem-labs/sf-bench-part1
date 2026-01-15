From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_nat__pred__iso.
From IsomorphismChecker Require Isomorphisms.U_nat__pred__iso.
From IsomorphismChecker Require Checker.nat__iso.

Module Type Args <: Interface.U_nat__pred__iso.Args := Checker.nat__iso.Args <+ Checker.nat__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_nat__pred__iso.imported_Nat_pred Isomorphisms.U_nat__pred__iso.Nat_pred_iso ].

Module Checker (Import args : Args) <: Interface.U_nat__pred__iso.Interface args
  with Definition imported_Nat_pred := Imported.nat_pred.

Definition imported_Nat_pred := Isomorphisms.U_nat__pred__iso.imported_Nat_pred.
Definition Nat_pred_iso := Isomorphisms.U_nat__pred__iso.Nat_pred_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Nat_pred_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.