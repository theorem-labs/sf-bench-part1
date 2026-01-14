From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso Isomorphisms.nat__iso.

(* Helper lemmas for arithmetic operations *)
Lemma nat_add_eq : forall n m, IsomorphismDefinitions.eq (Imported.nat_add (nat_to_imported n) (nat_to_imported m)) (nat_to_imported (n + m)).
Proof.
  induction n as [|n IH]; intros m.
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl. unfold Imported.S.
    apply (IsoEq.f_equal Imported.nat_S).
    apply IH.
Qed.

Lemma nat_sub_eq : forall n m, IsomorphismDefinitions.eq (Imported.nat_sub (nat_to_imported n) (nat_to_imported m)) (nat_to_imported (n - m)).
Proof.
  induction n as [|n IH]; intros m.
  - simpl. destruct m; apply IsomorphismDefinitions.eq_refl.
  - destruct m.
    + simpl. unfold Imported.S. apply IsomorphismDefinitions.eq_refl.
    + simpl. apply IH.
Qed.

Lemma nat_mul_eq : forall n m, IsomorphismDefinitions.eq (Imported.nat_mul (nat_to_imported n) (nat_to_imported m)) (nat_to_imported (n * m)).
Proof.
  induction n as [|n IH]; intros m.
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl. unfold Imported.S.
    exact (IsoEq.eq_trans 
             (IsoEq.f_equal (fun x => Imported.nat_add (nat_to_imported m) x) (IH m))
             (nat_add_eq m (n * m))).
Qed.

Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp -> imported_nat -> SProp := Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR.

(* Transport lemma for SProp *)
Definition transport_aevalR {a : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp} {n m : imported_nat}
  (H : Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR a n)
  (e : IsomorphismDefinitions.eq n m)
  : Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR a m :=
  match e with
  | IsomorphismDefinitions.eq_refl => H
  end.

(* Forward direction: original -> imported *)
Definition aevalR_to_imported : forall (a : Original.LF_DOT_Imp.LF.Imp.AExp.aexp) (n : nat),
  Original.LF_DOT_Imp.LF.Imp.AExp.aevalR_first_try.HypothesisNames.aevalR a n ->
  Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR (aexp_to_imported a) (nat_to_imported n).
Proof.
  fix IH 3.
  intros a n H.
  destruct H as [n0 | e1 e2 n1 n2 H1 H2 | e1 e2 n1 n2 H1 H2 | e1 e2 n1 n2 H1 H2].
  - (* E_ANum *)
    simpl. apply Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR_E_ANum.
  - (* E_APlus *)
    simpl.
    apply (transport_aevalR
             (Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR_E_APlus 
                (aexp_to_imported e1) (aexp_to_imported e2) (nat_to_imported n1) (nat_to_imported n2)
                (IH e1 n1 H1) (IH e2 n2 H2))
             (nat_add_eq n1 n2)).
  - (* E_AMinus *)
    simpl.
    apply (transport_aevalR
             (Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR_E_AMinus 
                (aexp_to_imported e1) (aexp_to_imported e2) (nat_to_imported n1) (nat_to_imported n2)
                (IH e1 n1 H1) (IH e2 n2 H2))
             (nat_sub_eq n1 n2)).
  - (* E_AMult *)
    simpl.
    apply (transport_aevalR
             (Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR_E_AMult 
                (aexp_to_imported e1) (aexp_to_imported e2) (nat_to_imported n1) (nat_to_imported n2)
                (IH e1 n1 H1) (IH e2 n2 H2))
             (nat_mul_eq n1 n2)).
Defined.

(* Helper for transporting along standard eq *)
Definition transport_aevalR_std {a : Original.LF_DOT_Imp.LF.Imp.AExp.aexp} {n m : nat}
  (H : Original.LF_DOT_Imp.LF.Imp.AExp.aevalR_first_try.HypothesisNames.aevalR a m)
  (e : Corelib.Init.Logic.eq n m)
  : Original.LF_DOT_Imp.LF.Imp.AExp.aevalR_first_try.HypothesisNames.aevalR a n :=
  match e in (Corelib.Init.Logic.eq _ m') return (Original.LF_DOT_Imp.LF.Imp.AExp.aevalR_first_try.HypothesisNames.aevalR a m' -> Original.LF_DOT_Imp.LF.Imp.AExp.aevalR_first_try.HypothesisNames.aevalR a n) with
  | Corelib.Init.Logic.eq_refl => fun x => x
  end H.

(* Helper lemmas using standard eq - using explicit Corelib.Init.Logic functions *)
Lemma imported_nat_add_eq_std : forall n1 n2 : Imported.nat, 
  Corelib.Init.Logic.eq (imported_to_nat (Imported.nat_add n1 n2)) (imported_to_nat n1 + imported_to_nat n2).
Proof.
  induction n1.
  - reflexivity.
  - intro n2. 
    change (Corelib.Init.Logic.eq (S (imported_to_nat (Imported.nat_add n1 n2))) (S (imported_to_nat n1 + imported_to_nat n2))).
    apply Corelib.Init.Logic.f_equal.
    apply IHn1.
Qed.

Lemma imported_nat_sub_eq_std : forall n1 n2 : Imported.nat, 
  Corelib.Init.Logic.eq (imported_to_nat (Imported.nat_sub n1 n2)) (imported_to_nat n1 - imported_to_nat n2).
Proof.
  induction n1; intros.
  - destruct n2; reflexivity.
  - destruct n2; try reflexivity. simpl. apply IHn1.
Qed.

Lemma imported_nat_mul_eq_std : forall n1 n2 : Imported.nat, 
  Corelib.Init.Logic.eq (imported_to_nat (Imported.nat_mul n1 n2)) (imported_to_nat n1 * imported_to_nat n2).
Proof.
  induction n1; intros.
  - reflexivity.
  - change (Corelib.Init.Logic.eq 
              (imported_to_nat (Imported.nat_add n2 (Imported.nat_mul n1 n2)))
              (imported_to_nat n2 + imported_to_nat n1 * imported_to_nat n2)).
    eapply Corelib.Init.Logic.eq_trans.
    + apply imported_nat_add_eq_std.
    + apply Corelib.Init.Logic.f_equal. apply IHn1.
Qed.

(* Backward direction via SInhabited *)
Definition aevalR_from_imported_sinhabited : forall (a : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n : imported_nat),
  Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR a n ->
  SInhabited (Original.LF_DOT_Imp.LF.Imp.AExp.aevalR_first_try.HypothesisNames.aevalR (imported_to_aexp a) (imported_to_nat n)).
Proof.
  fix IH 3.
  intros a n H.
  destruct H as [n0 | e1 e2 n1 n2 H1 H2 | e1 e2 n1 n2 H1 H2 | e1 e2 n1 n2 H1 H2].
  - apply sinhabits. apply Original.LF_DOT_Imp.LF.Imp.AExp.aevalR_first_try.HypothesisNames.E_ANum.
  - apply sinhabits.
    simpl imported_to_aexp.
    apply (transport_aevalR_std 
             (Original.LF_DOT_Imp.LF.Imp.AExp.aevalR_first_try.HypothesisNames.E_APlus 
                (imported_to_aexp e1) (imported_to_aexp e2) 
                (imported_to_nat n1) (imported_to_nat n2)
                (sinhabitant (IH _ _ H1)) (sinhabitant (IH _ _ H2)))
             (imported_nat_add_eq_std n1 n2)).
  - apply sinhabits.
    simpl imported_to_aexp.
    apply (transport_aevalR_std 
             (Original.LF_DOT_Imp.LF.Imp.AExp.aevalR_first_try.HypothesisNames.E_AMinus 
                (imported_to_aexp e1) (imported_to_aexp e2) 
                (imported_to_nat n1) (imported_to_nat n2)
                (sinhabitant (IH _ _ H1)) (sinhabitant (IH _ _ H2)))
             (imported_nat_sub_eq_std n1 n2)).
  - apply sinhabits.
    simpl imported_to_aexp.
    apply (transport_aevalR_std 
             (Original.LF_DOT_Imp.LF.Imp.AExp.aevalR_first_try.HypothesisNames.E_AMult 
                (imported_to_aexp e1) (imported_to_aexp e2) 
                (imported_to_nat n1) (imported_to_nat n2)
                (sinhabitant (IH _ _ H1)) (sinhabitant (IH _ _ H2)))
             (imported_nat_mul_eq_std n1 n2)).
Defined.

Definition aevalR_from_imported : forall (a : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n : imported_nat),
  Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR a n ->
  Original.LF_DOT_Imp.LF.Imp.AExp.aevalR_first_try.HypothesisNames.aevalR (imported_to_aexp a) (imported_to_nat n).
Proof.
  intros a n H.
  apply sinhabitant.
  apply aevalR_from_imported_sinhabited.
  exact H.
Defined.

Instance Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.AExp.aexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_aexp_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat),
  rel_iso nat_iso x3 x4 ->
  Iso (Original.LF_DOT_Imp.LF.Imp.AExp.aevalR_first_try.HypothesisNames.aevalR x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR x2 x4).
Proof.
  intros x1 x2 Haexp x3 x4 Hnat.
  unfold rel_iso in *.
  simpl in *.
  destruct Haexp. destruct Hnat.
  unfold imported_Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR.
  unshelve eapply Build_Iso.
  - (* to *)
    intro H. exact (@aevalR_to_imported x1 x3 H).
  - (* from *)
    intro H.
    pose proof (@aevalR_from_imported (aexp_to_imported x1) (nat_to_imported x3) H) as H'.
    (* Use round-trip properties - from_to lemmas from the Iso *)
    pose proof (from_to Original_LF__DOT__Imp_LF_Imp_AExp_aexp_iso x1) as Ha.
    pose proof (from_to nat_iso x3) as Hn.
    unfold rel_iso in *. simpl in *.
    destruct Ha. destruct Hn.
    exact H'.
  - (* to_from *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro x. 
    (* Both sides are proofs of the same Prop, use proof irrelevance *)
    apply IsoEq.seq_of_peq_t.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Qed.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.AExp.aevalR_first_try.HypothesisNames.aevalR := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.aevalR_first_try.HypothesisNames.aevalR Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.aevalR_first_try.HypothesisNames.aevalR Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR_iso := {}.
