From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_none__iso.
From IsomorphismChecker Require Isomorphisms.U_none__iso.
From IsomorphismChecker Require Checker.option__iso.

Module Type Args <: Interface.U_none__iso.Args := Checker.option__iso.Args <+ Checker.option__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_none__iso.imported_None Isomorphisms.U_none__iso.None_iso ].

Module Checker (Import args : Args) <: Interface.U_none__iso.Interface args
  with Definition imported_None := (@Imported.None).

Definition imported_None := Isomorphisms.U_none__iso.imported_None.
Definition None_iso := Isomorphisms.U_none__iso.None_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions None_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.