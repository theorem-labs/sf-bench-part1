From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.gt__iso.
From IsomorphismChecker Require Isomorphisms.gt__iso.
From IsomorphismChecker Require Checker.nat__iso.

Module Type Args <: Interface.gt__iso.Args := Checker.nat__iso.Args <+ Checker.nat__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.gt__iso.imported_gt Isomorphisms.gt__iso.gt_iso ].

Module Checker (Import args : Args) <: Interface.gt__iso.Interface args
  with Definition imported_gt := Imported.gt.

Definition imported_gt := Isomorphisms.gt__iso.imported_gt.
Definition gt_iso := Isomorphisms.gt__iso.gt_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions gt_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.