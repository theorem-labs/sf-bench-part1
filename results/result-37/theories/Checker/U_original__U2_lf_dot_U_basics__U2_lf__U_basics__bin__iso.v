From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bin__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bin__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bin__iso.Args. End Args.

#[global] Strategy -1 [ Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bin__iso.imported_Original_LF__DOT__Basics_LF_Basics_bin Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bin__iso.Original_LF__DOT__Basics_LF_Basics_bin_iso ].

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bin__iso.Interface args
  with Definition imported_Original_LF__DOT__Basics_LF_Basics_bin := Imported.Original_LF__DOT__Basics_LF_Basics_bin.

Definition imported_Original_LF__DOT__Basics_LF_Basics_bin := Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bin__iso.imported_Original_LF__DOT__Basics_LF_Basics_bin.
Definition Original_LF__DOT__Basics_LF_Basics_bin_iso := Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bin__iso.Original_LF__DOT__Basics_LF_Basics_bin_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Basics_LF_Basics_bin_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.