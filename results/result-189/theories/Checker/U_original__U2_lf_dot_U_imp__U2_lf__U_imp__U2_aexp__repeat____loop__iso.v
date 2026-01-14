From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__repeat____loop__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__repeat____loop__iso.
From IsomorphismChecker Require Checker.U_true__iso Checker.U_corelib__U_init__U_logic__eq__iso Checker.nat__iso Checker.U_peanoU_nat__U_nat__add__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__repeat____loop__iso.Args := Checker.U_true__iso.Checker <+ Checker.U_corelib__U_init__U_logic__eq__iso.Checker <+ Checker.nat__iso.Checker <+ Checker.U_peanoU_nat__U_nat__add__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__repeat____loop__iso.Interface args
  with Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_repeat__loop := Imported.Original_LF__DOT__Imp_LF_Imp_AExp_repeat__loop.

Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_repeat__loop := Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__repeat____loop__iso.imported_Original_LF__DOT__Imp_LF_Imp_AExp_repeat__loop.
Definition Original_LF__DOT__Imp_LF_Imp_AExp_repeat__loop_iso := Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__repeat____loop__iso.Original_LF__DOT__Imp_LF_Imp_AExp_repeat__loop_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Imp_LF_Imp_AExp_repeat__loop_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.