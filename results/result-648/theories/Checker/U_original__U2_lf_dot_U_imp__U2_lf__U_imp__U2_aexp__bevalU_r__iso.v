From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bevalU_r__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bevalU_r__iso.
From IsomorphismChecker Require Checker.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso Checker.bool__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bevalU_r__iso.Args := Checker.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso.Checker <+ Checker.bool__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bevalU_r__iso.Interface args
  with Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_bevalR := Imported.Original_LF__DOT__Imp_LF_Imp_AExp_bevalR.

Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_bevalR := Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bevalU_r__iso.imported_Original_LF__DOT__Imp_LF_Imp_AExp_bevalR.
Definition Original_LF__DOT__Imp_LF_Imp_AExp_bevalR_iso := Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bevalU_r__iso.Original_LF__DOT__Imp_LF_Imp_AExp_bevalR_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Imp_LF_Imp_AExp_bevalR_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.