From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.Args. End Args.

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.Interface args
  with Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq := (@Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_eq).

Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq := Isomorphisms.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq.
Definition Original_LF__DOT__ProofObjects_LF_ProofObjects_eq_iso := Isomorphisms.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.Original_LF__DOT__ProofObjects_LF_ProofObjects_eq_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__ProofObjects_LF_ProofObjects_eq_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.