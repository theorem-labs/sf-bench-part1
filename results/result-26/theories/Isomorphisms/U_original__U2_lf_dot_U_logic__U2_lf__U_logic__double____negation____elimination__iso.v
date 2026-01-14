From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Helper definitions for the isomorphism *)
Definition False_to_sFalse : Logic.False -> Imported.False.
Proof. intro H. destruct H. Defined.

Definition sFalse_to_False : Imported.False -> Logic.False.
Proof. intro H. destruct H. Defined.

Definition original_def : Prop := Original.LF_DOT_Logic.LF.Logic.double_negation_elimination.
Definition imported_def : SProp := Imported.Original_LF__DOT__Logic_LF_Logic_double__negation__elimination.

(* Convert DNE for Prop to DNE for SProp *)
Definition DNE_Prop_to_SProp : original_def -> imported_def.
Proof.
  unfold original_def, imported_def.
  unfold Original.LF_DOT_Logic.LF.Logic.double_negation_elimination.
  unfold Imported.Original_LF__DOT__Logic_LF_Logic_double__negation__elimination.
  intro H.
  intro P_sprop.
  intro HNN.
  pose (P_prop := inhabited P_sprop).
  assert (HNN' : ~~P_prop).
  { unfold P_prop. intro Hnot.
    apply (sFalse_to_False (HNN (fun p => False_to_sFalse (Hnot (@inhabits P_sprop p))))). }
  pose proof (H P_prop HNN') as Hp.
  destruct Hp as [p].
  exact p.
Defined.

(* Convert DNE for SProp to DNE for Prop *)
Definition DNE_SProp_to_Prop : imported_def -> original_def.
Proof.
  unfold original_def, imported_def.
  unfold Original.LF_DOT_Logic.LF.Logic.double_negation_elimination.
  unfold Imported.Original_LF__DOT__Logic_LF_Logic_double__negation__elimination.
  intro H.
  intro P_prop.
  intro HNN.
  pose (P_sprop := SInhabited P_prop).
  assert (HNN' : (P_sprop -> Imported.False) -> Imported.False).
  { unfold P_sprop. intro Hnot.
    apply False_to_sFalse.
    apply HNN.
    intro p.
    apply sFalse_to_False.
    apply Hnot.
    exact (sinhabits p). }
  apply sinhabitant.
  exact (H P_sprop HNN').
Defined.

(* Build the isomorphism *)
Definition the_iso : Iso original_def imported_def.
Proof.
  refine (@Build_Iso original_def imported_def DNE_Prop_to_SProp DNE_SProp_to_Prop _ _).
  { intro x. exact IsomorphismDefinitions.eq_refl. }
  { intro x. 
    pose proof (ProofIrrelevance.proof_irrelevance original_def (DNE_SProp_to_Prop (DNE_Prop_to_SProp x)) x) as H.
    exact (seq_of_peq_t H). }
Defined.

Definition imported_Original_LF__DOT__Logic_LF_Logic_double__negation__elimination : SProp := Imported.Original_LF__DOT__Logic_LF_Logic_double__negation__elimination.
Instance Original_LF__DOT__Logic_LF_Logic_double__negation__elimination_iso : Iso Original.LF_DOT_Logic.LF.Logic.double_negation_elimination imported_Original_LF__DOT__Logic_LF_Logic_double__negation__elimination.
Proof. exact the_iso. Defined.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.double_negation_elimination := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_double__negation__elimination := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.double_negation_elimination Original_LF__DOT__Logic_LF_Logic_double__negation__elimination_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.double_negation_elimination Imported.Original_LF__DOT__Logic_LF_Logic_double__negation__elimination Original_LF__DOT__Logic_LF_Logic_double__negation__elimination_iso := {}.