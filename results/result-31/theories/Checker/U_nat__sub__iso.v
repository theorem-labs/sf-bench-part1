From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_nat__sub__iso.
From IsomorphismChecker Require Isomorphisms.U_nat__sub__iso.
From IsomorphismChecker Require Checker.nat__iso.

Module Type Args <: Interface.U_nat__sub__iso.Args := Checker.nat__iso.Args <+ Checker.nat__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_nat__sub__iso.imported_Nat_sub Isomorphisms.U_nat__sub__iso.Nat_sub_iso ].

Module Checker (Import args : Args) <: Interface.U_nat__sub__iso.Interface args
  with Definition imported_Nat_sub := Imported.Nat_sub.

Definition imported_Nat_sub := Isomorphisms.U_nat__sub__iso.imported_Nat_sub.
Definition Nat_sub_iso := Isomorphisms.U_nat__sub__iso.Nat_sub_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Nat_sub_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.