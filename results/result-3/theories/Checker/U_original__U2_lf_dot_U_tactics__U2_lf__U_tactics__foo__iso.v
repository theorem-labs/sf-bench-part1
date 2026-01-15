From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__foo__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__foo__iso.
From IsomorphismChecker Require Checker.nat__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__foo__iso.Args := Checker.nat__iso.Args <+ Checker.nat__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__foo__iso.imported_Original_LF__DOT__Tactics_LF_Tactics_foo Isomorphisms.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__foo__iso.Original_LF__DOT__Tactics_LF_Tactics_foo_iso ].

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__foo__iso.Interface args
  with Definition imported_Original_LF__DOT__Tactics_LF_Tactics_foo := Imported.Original_LF__DOT__Tactics_LF_Tactics_foo.

Definition imported_Original_LF__DOT__Tactics_LF_Tactics_foo := Isomorphisms.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__foo__iso.imported_Original_LF__DOT__Tactics_LF_Tactics_foo.
Definition Original_LF__DOT__Tactics_LF_Tactics_foo_iso := Isomorphisms.U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__foo__iso.Original_LF__DOT__Tactics_LF_Tactics_foo_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Tactics_LF_Tactics_foo_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.