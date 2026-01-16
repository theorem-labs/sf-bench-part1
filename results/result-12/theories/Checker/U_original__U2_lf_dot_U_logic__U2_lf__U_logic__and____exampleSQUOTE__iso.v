From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__and____exampleSQUOTE__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__and____exampleSQUOTE__iso.
From IsomorphismChecker Require Checker.U_true__iso Checker.U_corelib__U_init__U_logic__eq__iso Checker.and__iso Checker.nat__iso Checker.U_nat__add__iso Checker.U_nat__mul__iso Checker.U_s__iso Checker.__0__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__and____exampleSQUOTE__iso.Args := Checker.U_true__iso.Checker <+ Checker.U_corelib__U_init__U_logic__eq__iso.Checker <+ Checker.and__iso.Checker <+ Checker.nat__iso.Checker <+ Checker.U_nat__add__iso.Checker <+ Checker.U_nat__mul__iso.Checker <+ Checker.U_s__iso.Checker <+ Checker.__0__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__and____exampleSQUOTE__iso.imported_Original_LF__DOT__Logic_LF_Logic_and__example' Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__and____exampleSQUOTE__iso.Original_LF__DOT__Logic_LF_Logic_and__example'_iso ].

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__and____exampleSQUOTE__iso.Interface args
  with Definition imported_Original_LF__DOT__Logic_LF_Logic_and__example' := Imported.Original_LF__DOT__Logic_LF_Logic_and__example'.

Definition imported_Original_LF__DOT__Logic_LF_Logic_and__example' := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__and____exampleSQUOTE__iso.imported_Original_LF__DOT__Logic_LF_Logic_and__example'.
Definition Original_LF__DOT__Logic_LF_Logic_and__example'_iso := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__and____exampleSQUOTE__iso.Original_LF__DOT__Logic_LF_Logic_and__example'_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Logic_LF_Logic_and__example'_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.