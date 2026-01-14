From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__ex__iso Isomorphisms.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__ev__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__ev__Sn : imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex (fun H : imported_nat => imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (imported_S H)) := Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__ev__Sn.

(* The isomorphism between axioms - both ex_ev_Sn are axioms (Admitted), so rel_iso between them is trivial *)
(* We use the fact that both are inhabitants of isomorphic SProp types *)
Definition the_iso := Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_iso (fun n : nat => Original.LF_DOT_ProofObjects.LF.ProofObjects.ev (S n))
          (fun H : imported_nat => imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (imported_S H))
          (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) => Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_iso (S_iso hx)).

Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__ev__Sn_iso : rel_iso
    {|
      to := the_iso.(to);
      from := the_iso.(from);
      to_from := fun x => the_iso.(to_from) x;
      from_to := fun x => seq_p_of_t (the_iso.(from_to) x)
    |} Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex_ev_Sn imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__ev__Sn.
Proof.
  unfold rel_iso.
  simpl.
  (* We need: to the_iso (ex_ev_Sn) = imported_ex_ev_Sn *)
  (* Both are in SProp, so they're equal by proof irrelevance in SProp *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex_ev_Sn := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__ev__Sn := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex_ev_Sn Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__ev__Sn_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex_ev_Sn Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__ev__Sn Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__ev__Sn_iso := {}.