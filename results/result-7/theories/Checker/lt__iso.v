From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.lt__iso.
From IsomorphismChecker Require Isomorphisms.lt__iso.
From IsomorphismChecker Require Checker.nat__iso.

Module Type Args <: Interface.lt__iso.Args := Checker.nat__iso.Args <+ Checker.nat__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.lt__iso.imported_lt Isomorphisms.lt__iso.lt_iso ].

Module Checker (Import args : Args) <: Interface.lt__iso.Interface args
  with Definition imported_lt := Imported.lt.

Definition imported_lt := Isomorphisms.lt__iso.imported_lt.
Definition lt_iso := Isomorphisms.lt__iso.lt_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions lt_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.