From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update____permute__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update____permute__iso.
From IsomorphismChecker Require Checker.U_ascii__ascii__iso Checker.U_false__iso Checker.U_logic__not__iso Checker.U_string__string__iso Checker.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Checker.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso Checker.U_string__U_emptyU_string__iso Checker.U_string__U_string__iso Checker.U_true__iso Checker.U_corelib__U_init__U_logic__eq__iso Checker.bool__iso Checker.U_ascii__U_ascii__iso Checker.false__iso Checker.true__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update____permute__iso.Args := Checker.U_ascii__ascii__iso.Checker <+ Checker.U_false__iso.Checker <+ Checker.U_logic__not__iso.Checker <+ Checker.U_string__string__iso.Checker <+ Checker.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Checker <+ Checker.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.Checker <+ Checker.U_string__U_emptyU_string__iso.Checker <+ Checker.U_string__U_string__iso.Checker <+ Checker.U_true__iso.Checker <+ Checker.U_corelib__U_init__U_logic__eq__iso.Checker <+ Checker.bool__iso.Checker <+ Checker.U_ascii__U_ascii__iso.Checker <+ Checker.false__iso.Checker <+ Checker.true__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update____permute__iso.Interface args
  with Definition imported_Original_LF__DOT__Maps_LF_Maps_t__update__permute := Imported.Original_LF__DOT__Maps_LF_Maps_t__update__permute.

Definition imported_Original_LF__DOT__Maps_LF_Maps_t__update__permute := Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update____permute__iso.imported_Original_LF__DOT__Maps_LF_Maps_t__update__permute.
Definition Original_LF__DOT__Maps_LF_Maps_t__update__permute_iso := Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update____permute__iso.Original_LF__DOT__Maps_LF_Maps_t__update__permute_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Maps_LF_Maps_t__update__permute_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.