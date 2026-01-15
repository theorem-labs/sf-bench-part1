From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_peanoU_nat__U_nat__leb__iso.
From IsomorphismChecker Require Isomorphisms.U_peanoU_nat__U_nat__leb__iso.
From IsomorphismChecker Require Checker.bool__iso Checker.nat__iso.

Module Type Args <: Interface.U_peanoU_nat__U_nat__leb__iso.Args := Checker.bool__iso.Checker <+ Checker.nat__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_peanoU_nat__U_nat__leb__iso.imported_PeanoNat_Nat_leb Isomorphisms.U_peanoU_nat__U_nat__leb__iso.PeanoNat_Nat_leb_iso ].

Module Checker (Import args : Args) <: Interface.U_peanoU_nat__U_nat__leb__iso.Interface args
  with Definition imported_PeanoNat_Nat_leb := Imported.nat_leb.

Definition imported_PeanoNat_Nat_leb := Isomorphisms.U_peanoU_nat__U_nat__leb__iso.imported_PeanoNat_Nat_leb.
Definition PeanoNat_Nat_leb_iso := Isomorphisms.U_peanoU_nat__U_nat__leb__iso.PeanoNat_Nat_leb_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions PeanoNat_Nat_leb_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.