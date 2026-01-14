From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_b__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_b__iso.
From IsomorphismChecker Require Checker.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__letter__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_b__iso.Args := Checker.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__letter__iso.Args <+ Checker.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__letter__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_b__iso.Interface args
  with Definition imported_Original_LF__DOT__Basics_LF_Basics_B := Imported.Original_LF__DOT__Basics_LF_Basics_B.

Definition imported_Original_LF__DOT__Basics_LF_Basics_B := Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_b__iso.imported_Original_LF__DOT__Basics_LF_Basics_B.
Definition Original_LF__DOT__Basics_LF_Basics_B_iso := Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_b__iso.Original_LF__DOT__Basics_LF_Basics_B_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Basics_LF_Basics_B_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.