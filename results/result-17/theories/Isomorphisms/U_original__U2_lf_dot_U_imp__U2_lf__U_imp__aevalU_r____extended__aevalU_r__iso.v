From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aevalU_r____extended__aexp__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR : imported_Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp -> imported_nat -> SProp := Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR.

Import Stdlib.Logic.ProofIrrelevance.

(* Build isomorphism between Prop and SProp using proof irrelevance *)
Lemma sprop_iso (P : Prop) (S : SProp) 
  (f : P -> S) (g : S -> P) : Iso P S.
Proof.
  refine (@Build_Iso P S (fun p => f p) (fun s => g s) _ _).
  - intro s. apply IsomorphismDefinitions.eq_refl.
  - intro p. apply seq_of_eq. apply proof_irrelevance.
Defined.

(* Nat operation compatibility - proven by induction using transitivity *)
Lemma nat_add_compat : forall n m : Datatypes.nat,
  nat_to_imported (n + m) = Imported.nat_add (nat_to_imported n) (nat_to_imported m).
Proof.
  induction n as [|n IHn]; intro m; [reflexivity|].
  transitivity (Imported.nat_S (nat_to_imported (n + m))); [reflexivity|].
  transitivity (Imported.nat_S (Imported.nat_add (nat_to_imported n) (nat_to_imported m)));
    [f_equal; apply IHn | reflexivity].
Qed.

Lemma nat_sub_compat : forall n m : Datatypes.nat,
  nat_to_imported (n - m) = Imported.nat_sub (nat_to_imported n) (nat_to_imported m).
Proof.
  induction n as [|n IHn]; destruct m as [|m]; try reflexivity.
  transitivity (Imported.nat_sub (nat_to_imported n) (nat_to_imported m)); [apply IHn|reflexivity].
Qed.

Lemma nat_mul_compat : forall n m : Datatypes.nat,
  nat_to_imported (n * m) = Imported.nat_mul (nat_to_imported n) (nat_to_imported m).
Proof.
  induction n as [|n IHn]; intro m; [reflexivity|].
  transitivity (nat_to_imported (m + n * m)); [reflexivity|].
  transitivity (Imported.nat_add (nat_to_imported m) (nat_to_imported (n * m)));
    [apply nat_add_compat|].
  transitivity (Imported.nat_add (nat_to_imported m) (Imported.nat_mul (nat_to_imported n) (nat_to_imported m)));
    [f_equal; apply IHn | reflexivity].
Qed.

(* Convert original aevalR to imported aevalR *)
Lemma aevalR_to_imported : forall (a : Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp) (n : Datatypes.nat),
  Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aevalR a n ->
  Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR (aexp_to_imported a) (nat_to_imported n).
Proof.
  intros a n H.
  induction H.
  - apply Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR_E_Any.
  - apply Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR_E_ANum.
  - simpl. rewrite nat_add_compat.
    apply Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR_E_APlus; assumption.
  - simpl. rewrite nat_sub_compat.
    apply Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR_E_AMinus; assumption.
  - simpl. rewrite nat_mul_compat.
    apply Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR_E_AMult; assumption.
Qed.

(* Nat operation compatibility in reverse direction *)
Lemma nat_add_compat_rev : forall n m : Imported.nat,
  imported_to_nat (Imported.nat_add n m) = (imported_to_nat n + imported_to_nat m)%nat.
Proof.
  induction n as [|n IHn]; intro m; [reflexivity|].
  transitivity (Datatypes.S (imported_to_nat (Imported.nat_add n m))); [reflexivity|].
  transitivity (Datatypes.S (imported_to_nat n + imported_to_nat m));
    [f_equal; apply IHn | reflexivity].
Qed.

Lemma nat_sub_compat_rev : forall n m : Imported.nat,
  imported_to_nat (Imported.nat_sub n m) = (imported_to_nat n - imported_to_nat m)%nat.
Proof.
  induction n as [|n IHn]; destruct m as [|m]; try reflexivity.
  transitivity (imported_to_nat (Imported.nat_sub n m)); [reflexivity|].
  transitivity (imported_to_nat n - imported_to_nat m)%nat; [apply IHn|reflexivity].
Qed.

Lemma nat_mul_compat_rev : forall n m : Imported.nat,
  imported_to_nat (Imported.nat_mul n m) = (imported_to_nat n * imported_to_nat m)%nat.
Proof.
  induction n as [|n IHn]; intro m; [reflexivity|].
  transitivity (imported_to_nat (Imported.nat_add m (Imported.nat_mul n m))); [reflexivity|].
  transitivity ((imported_to_nat m + imported_to_nat (Imported.nat_mul n m))%nat);
    [apply nat_add_compat_rev|].
  transitivity ((imported_to_nat m + imported_to_nat n * imported_to_nat m)%nat);
    [f_equal; apply IHn | reflexivity].
Qed.

(* For the reverse direction, we use the sinhabitant axiom via SInhabited.
   Since we cannot destruct SProp to produce Prop directly, we use
   the sind induction principle which produces SProp, then extract via sinhabitant. *)

(* Helper lemma to transport aevalR along nat equality *)
Lemma aevalR_transport : forall (a : Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp) (n m : Datatypes.nat),
  @Corelib.Init.Logic.eq Datatypes.nat n m ->
  Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aevalR a n ->
  Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aevalR a m.
Proof.
  intros a n m Heq H. destruct Heq. exact H.
Qed.

Lemma aevalR_transport' : forall (a : Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp) (n m : Datatypes.nat),
  Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aevalR a n ->
  @Corelib.Init.Logic.eq Datatypes.nat n m ->
  Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aevalR a m.
Proof.
  intros a n m H Heq. destruct Heq. exact H.
Qed.

(* Prove that imported aevalR implies SInhabited of original aevalR *)
Lemma aevalR_to_SInhabited : forall (a : Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp) (n : Imported.nat),
  Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR a n ->
  SInhabited (Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aevalR (imported_to_aexp a) (imported_to_nat n)).
Proof.
  intros a n H.
  apply (Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR_sind
    (fun a n _ => SInhabited (Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aevalR (imported_to_aexp a) (imported_to_nat n)))).
  { intro n0. simpl. apply sinhabits. apply Original.LF_DOT_Imp.LF.Imp.aevalR_extended.E_Any. }
  { intro n0. simpl. apply sinhabits. apply Original.LF_DOT_Imp.LF.Imp.aevalR_extended.E_ANum. }
  { intros a1 a2 n1 n2 _ IH1 _ IH2. simpl.
    apply sinhabits.
    eapply aevalR_transport'; [| exact (Corelib.Init.Logic.eq_sym (nat_add_compat_rev n1 n2))].
    apply Original.LF_DOT_Imp.LF.Imp.aevalR_extended.E_APlus.
    - apply sinhabitant. exact IH1.
    - apply sinhabitant. exact IH2. }
  { intros a1 a2 n1 n2 _ IH1 _ IH2. simpl.
    apply sinhabits.
    eapply aevalR_transport'; [| exact (Corelib.Init.Logic.eq_sym (nat_sub_compat_rev n1 n2))].
    apply Original.LF_DOT_Imp.LF.Imp.aevalR_extended.E_AMinus.
    - apply sinhabitant. exact IH1.
    - apply sinhabitant. exact IH2. }
  { intros a1 a2 n1 n2 _ IH1 _ IH2. simpl.
    apply sinhabits.
    eapply aevalR_transport'; [| exact (Corelib.Init.Logic.eq_sym (nat_mul_compat_rev n1 n2))].
    apply Original.LF_DOT_Imp.LF.Imp.aevalR_extended.E_AMult.
    - apply sinhabitant. exact IH1.
    - apply sinhabitant. exact IH2. }
  exact H.
Qed.

(* Extract the Prop proof using sinhabitant *)
Lemma aevalR_from_imported : forall (a : Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp) (n : Imported.nat),
  Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR a n ->
  Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aevalR (imported_to_aexp a) (imported_to_nat n).
Proof.
  intros a n H.
  apply sinhabitant.
  apply aevalR_to_SInhabited.
  exact H.
Qed.

(* Now prove the main aevalR isomorphism *)
Instance Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_iso x1 x2 ->
  forall (x3 : Datatypes.nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aevalR x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR x2 x4).
Proof.
  intros x1 x2 Haexp x3 x4 Hnat.
  unfold rel_iso in *.
  unfold imported_Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp in *.
  unfold imported_nat in *.
  unfold imported_Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR.
  destruct Haexp. destruct Hnat.
  refine (@sprop_iso 
    (Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aevalR x1 x3)
    (Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR (aexp_to_imported x1) (nat_to_imported x3))
    (@aevalR_to_imported x1 x3)
    _).
  intro H.
  pose proof (@aevalR_from_imported (aexp_to_imported x1) (nat_to_imported x3) H) as H'.
  simpl in H'.
  rewrite aexp_from_to in H'.
  rewrite nat_roundtrip1 in H'.
  exact H'.
Defined.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aevalR := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aevalR Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aevalR Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR_iso := {}.
