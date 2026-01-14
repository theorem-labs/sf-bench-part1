From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__auto____example____4__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__auto____example____4__iso.
From IsomorphismChecker Require Checker.and__iso Checker.or__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__auto____example____4__iso.Args := Checker.and__iso.Checker <+ Checker.or__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__auto____example____4__iso.Interface args
  with Definition imported_Original_LF__DOT__Auto_LF_Auto_auto__example__4 := Imported.Original_LF__DOT__Auto_LF_Auto_auto__example__4.

Definition imported_Original_LF__DOT__Auto_LF_Auto_auto__example__4 := Isomorphisms.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__auto____example____4__iso.imported_Original_LF__DOT__Auto_LF_Auto_auto__example__4.
Definition Original_LF__DOT__Auto_LF_Auto_auto__example__4_iso := Isomorphisms.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__auto____example____4__iso.Original_LF__DOT__Auto_LF_Auto_auto__example__4_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Auto_LF_Auto_auto__example__4_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.