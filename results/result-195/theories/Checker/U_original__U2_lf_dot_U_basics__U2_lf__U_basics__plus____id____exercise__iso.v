From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__plus____id____exercise__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__plus____id____exercise__iso.
From IsomorphismChecker Require Checker.U_true__iso Checker.U_corelib__U_init__U_logic__eq__iso Checker.nat__iso Checker.U_nat__add__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__plus____id____exercise__iso.Args := Checker.U_true__iso.Checker <+ Checker.U_corelib__U_init__U_logic__eq__iso.Checker <+ Checker.nat__iso.Checker <+ Checker.U_nat__add__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__plus____id____exercise__iso.Interface args
  with Definition imported_Original_LF__DOT__Basics_LF_Basics_plus__id__exercise := Imported.Original_LF__DOT__Basics_LF_Basics_plus__id__exercise.

Definition imported_Original_LF__DOT__Basics_LF_Basics_plus__id__exercise := Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__plus____id____exercise__iso.imported_Original_LF__DOT__Basics_LF_Basics_plus__id__exercise.
Definition Original_LF__DOT__Basics_LF_Basics_plus__id__exercise_iso := Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__plus____id____exercise__iso.Original_LF__DOT__Basics_LF_Basics_plus__id__exercise_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Basics_LF_Basics_plus__id__exercise_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.