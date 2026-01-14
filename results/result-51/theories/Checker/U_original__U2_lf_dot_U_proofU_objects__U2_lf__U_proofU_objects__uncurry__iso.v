From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__uncurry__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__uncurry__iso.
From IsomorphismChecker Require Checker.and__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__uncurry__iso.Args := Checker.and__iso.Args <+ Checker.and__iso.Checker.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__uncurry__iso.Interface args
  with Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_uncurry := Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_uncurry.

Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_uncurry := Isomorphisms.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__uncurry__iso.imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_uncurry.
Definition Original_LF__DOT__ProofObjects_LF_ProofObjects_uncurry_iso := Isomorphisms.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__uncurry__iso.Original_LF__DOT__ProofObjects_LF_ProofObjects_uncurry_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__ProofObjects_LF_ProofObjects_uncurry_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.