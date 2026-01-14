From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.
From IsomorphismChecker Require Checker.nat__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.Args := Checker.nat__iso.Args <+ Checker.nat__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.Interface args
  with Definition imported_Original_LF__DOT__Induction_LF_Induction_double := Imported.Original_LF__DOT__Induction_LF_Induction_double.

Definition imported_Original_LF__DOT__Induction_LF_Induction_double := Isomorphisms.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.imported_Original_LF__DOT__Induction_LF_Induction_double.
Definition Original_LF__DOT__Induction_LF_Induction_double_iso := Isomorphisms.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.Original_LF__DOT__Induction_LF_Induction_double_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Induction_LF_Induction_double_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.