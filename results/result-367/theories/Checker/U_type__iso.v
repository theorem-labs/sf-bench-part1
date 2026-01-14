From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_type__iso.
From IsomorphismChecker Require Isomorphisms.U_type__iso.

Module Type Args <: Interface.U_type__iso.Args. End Args.

Module Checker (Import args : Args) <: Interface.U_type__iso.Interface args
  with Definition imported_Type := Imported.Type.

Definition imported_Type := Isomorphisms.U_type__iso.imported_Type.
Definition Type_iso := Isomorphisms.U_type__iso.Type_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Type_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.