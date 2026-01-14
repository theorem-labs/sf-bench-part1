From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__and____assoc__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__and____assoc__iso.
From IsomorphismChecker Require Checker.and__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__and____assoc__iso.Args := Checker.and__iso.Args <+ Checker.and__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__and____assoc__iso.Interface args
  with Definition imported_Original_LF__DOT__Logic_LF_Logic_and__assoc := Imported.Original_LF__DOT__Logic_LF_Logic_and__assoc.

Definition imported_Original_LF__DOT__Logic_LF_Logic_and__assoc := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__and____assoc__iso.imported_Original_LF__DOT__Logic_LF_Logic_and__assoc.
Definition Original_LF__DOT__Logic_LF_Logic_and__assoc_iso := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__and____assoc__iso.Original_LF__DOT__Logic_LF_Logic_and__assoc_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Logic_LF_Logic_and__assoc_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.