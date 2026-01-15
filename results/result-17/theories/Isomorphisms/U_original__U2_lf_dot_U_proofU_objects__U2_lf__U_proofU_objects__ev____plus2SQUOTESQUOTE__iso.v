From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
#[local] Set Printing Coercions.

From IsomorphismChecker Require Export Isomorphisms.nat__iso Isomorphisms.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__ev__iso Isomorphisms.U_nat__add__iso.
Require Import Stdlib.Logic.ProofIrrelevance.

Monomorphic Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'' : SProp := Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2''.

(* Helper for n + 2 *)
Lemma add_2_rel'' : forall (n : Datatypes.nat),
  rel_iso nat_iso (n + 2) (Imported.Nat_add (nat_to_imported n) (Imported.nat_S (Imported.nat_S Imported.nat_O))).
Proof.
  intro n.
  exact (@Nat_add_iso n (nat_to_imported n) (rel_iso_refl nat_iso n) (S (S O)) (Imported.nat_S (Imported.nat_S Imported.nat_O)) (rel_iso_refl nat_iso (S (S O)))).
Qed.

(* Helper for nat_from_imported *)
Lemma nat_from_rel'' : forall (n' : imported_nat),
  rel_iso nat_iso (nat_from_imported n') n'.
Proof.
  intro n'. constructor. apply seq_of_eq. apply nat_to_from.
Qed.

Definition ev_plus2''_to : Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2'' -> imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2''.
Proof.
  unfold Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2''.
  unfold imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2''.
  unfold Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2''.
  intro H. intros n' Hev'.
  pose (n := nat_from_imported n').
  pose (Hev := from (Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_iso (nat_from_rel'' n')) Hev').
  pose (Hresult := H n Hev).
  assert (Hrel : rel_iso nat_iso (n + 2) (Imported.Nat_add n' (Imported.nat_S (Imported.nat_S Imported.nat_O)))).
  { unfold n. pose proof (add_2_rel'' (nat_from_imported n')) as H2.
    revert H2. rewrite nat_to_from. intro H2. exact H2. }
  exact (to (Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_iso Hrel) Hresult).
Defined.

Definition ev_plus2''_from : imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'' -> Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2''.
Proof.
  unfold Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2''.
  unfold imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2''.
  unfold Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2''.
  intro H. intros n Hev.
  pose (n' := nat_to_imported n).
  pose (Hev' := to (Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_iso (rel_iso_refl nat_iso n)) Hev).
  pose (Hresult' := H n' Hev').
  assert (Hrel : rel_iso nat_iso (n + 2) (Imported.Nat_add n' (Imported.nat_S (Imported.nat_S Imported.nat_O)))).
  { unfold n'. apply add_2_rel''. }
  exact (from (Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_iso Hrel) Hresult').
Defined.

Monomorphic Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2''_iso : Iso Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2'' imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'' :=
  {| to := ev_plus2''_to;
     from := ev_plus2''_from;
     to_from := fun _ => IsomorphismDefinitions.eq_refl;
     from_to := fun x => seq_of_eq (proof_irrelevance _ _ _) |}.

Instance: KnownConstant Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2'' := {}.
Instance: KnownConstant Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'' := {}.
Instance: IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2'' Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2''_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2'' Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'' Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2''_iso := {}.
