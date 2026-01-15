From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__injective__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__injective__iso.
From IsomorphismChecker Require Checker.U_true__iso Checker.U_corelib__U_init__U_logic__eq__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__injective__iso.Args := Checker.U_true__iso.Checker <+ Checker.U_corelib__U_init__U_logic__eq__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__injective__iso.imported_Original_LF__DOT__Logic_LF_Logic_injective Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__injective__iso.Original_LF__DOT__Logic_LF_Logic_injective_iso ].

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__injective__iso.Interface args
  with Definition imported_Original_LF__DOT__Logic_LF_Logic_injective := (@Imported.Original_LF__DOT__Logic_LF_Logic_injective).

Definition imported_Original_LF__DOT__Logic_LF_Logic_injective := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__injective__iso.imported_Original_LF__DOT__Logic_LF_Logic_injective.
Definition Original_LF__DOT__Logic_LF_Logic_injective_iso := Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__injective__iso.Original_LF__DOT__Logic_LF_Logic_injective_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Logic_LF_Logic_injective_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.