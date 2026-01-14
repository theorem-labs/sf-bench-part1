From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__match____ex2SQUOTESQUOTE__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__match____ex2SQUOTESQUOTE__iso.
From IsomorphismChecker Require Checker.U_true__iso Checker.and__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__match____ex2SQUOTESQUOTE__iso.Args := Checker.U_true__iso.Checker <+ Checker.and__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__match____ex2SQUOTESQUOTE__iso.Interface args
  with Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2'' := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2''.

Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2'' := Isomorphisms.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__match____ex2SQUOTESQUOTE__iso.imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2''.
Definition Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2''_iso := Isomorphisms.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__match____ex2SQUOTESQUOTE__iso.Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2''_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2''_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.