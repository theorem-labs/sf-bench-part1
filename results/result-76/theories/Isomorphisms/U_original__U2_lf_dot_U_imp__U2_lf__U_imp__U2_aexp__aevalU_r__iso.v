From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_aevalR : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp -> imported_nat -> SProp := Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR.

(* Lemmas about arithmetic operations correspondence - using Prop equality on nat *)
Lemma nat_add_correct : forall n m : imported_nat,
  imported_to_nat (Imported.nat_add n m) = imported_to_nat n + imported_to_nat m.
Proof.
  intro n.
  pattern n.
  apply Imported.nat_rect.
  - intro m. simpl. reflexivity.
  - intros n' IHn m. simpl. f_equal. apply IHn.
Qed.

Lemma nat_sub_correct : forall n m : imported_nat,
  imported_to_nat (Imported.nat_sub n m) = imported_to_nat n - imported_to_nat m.
Proof.
  intro n.
  pattern n.
  apply Imported.nat_rect.
  - intro m. simpl. destruct m; reflexivity.
  - intros n' IHn.
    intro m.
    pattern m.
    apply Imported.nat_rect.
    + simpl. reflexivity.
    + intros m' IHm. simpl. apply IHn.
Qed.

Lemma nat_mul_correct : forall n m : imported_nat,
  imported_to_nat (Imported.nat_mul n m) = imported_to_nat n * imported_to_nat m.
Proof.
  intro n.
  pattern n.
  apply Imported.nat_rect.
  - intro m. simpl. reflexivity.
  - intros n' IHn m. simpl.
    transitivity (imported_to_nat m + imported_to_nat (Imported.nat_mul n' m)).
    + apply nat_add_correct.
    + f_equal. apply IHn.
Qed.

(* Helper lemma using SProp equality: nat_add (nat_S n) m = nat_S (nat_add n m) *)
Lemma nat_add_S : forall n m, IsomorphismDefinitions.eq (Imported.nat_add (Imported.nat_S n) m) (Imported.nat_S (Imported.nat_add n m)).
Proof. intros. apply IsomorphismDefinitions.eq_refl. Qed.

(* Helper lemma using SProp equality: nat_mul (nat_S n) m = nat_add m (nat_mul n m) *)
Lemma nat_mul_S : forall n m, IsomorphismDefinitions.eq (Imported.nat_mul (Imported.nat_S n) m) (Imported.nat_add m (Imported.nat_mul n m)).
Proof. intros. apply IsomorphismDefinitions.eq_refl. Qed.

(* Helper lemma using SProp equality: nat_sub n nat_O = n - needs induction *)
Lemma nat_sub_O : forall n, IsomorphismDefinitions.eq (Imported.nat_sub n Imported.nat_O) n.
Proof.
  intro n.
  pattern n.
  apply Imported.nat_sind.
  - apply IsomorphismDefinitions.eq_refl.
  - intros. apply IsomorphismDefinitions.eq_refl.
Qed.

(* Helper lemma using SProp equality: nat_sub (nat_S n) (nat_S m) = nat_sub n m *)
Lemma nat_sub_S : forall n m, IsomorphismDefinitions.eq (Imported.nat_sub (Imported.nat_S n) (Imported.nat_S m)) (Imported.nat_sub n m).
Proof. intros. apply IsomorphismDefinitions.eq_refl. Qed.

Lemma nat_to_imported_add : forall n m : nat,
  IsomorphismDefinitions.eq (nat_to_imported (n + m)) (Imported.nat_add (nat_to_imported n) (nat_to_imported m)).
Proof.
  induction n as [|n' IHn].
  - intro m. apply IsomorphismDefinitions.eq_refl.
  - intro m. simpl. unfold Imported.S. 
    apply (IsoEq.eq_trans (IsoEq.f_equal Imported.nat_S (IHn m))).
    apply IsoEq.eq_sym. apply nat_add_S.
Qed.

Lemma nat_to_imported_sub : forall n m : nat,
  IsomorphismDefinitions.eq (nat_to_imported (n - m)) (Imported.nat_sub (nat_to_imported n) (nat_to_imported m)).
Proof.
  induction n as [|n' IHn].
  - intro m. destruct m; apply IsomorphismDefinitions.eq_refl.
  - induction m as [|m' IHm].
    + simpl. apply IsoEq.eq_sym. apply nat_sub_O.
    + simpl. apply (IsoEq.eq_trans (IHn m')).
      apply IsoEq.eq_sym. apply nat_sub_S.
Qed.

Lemma nat_to_imported_mul : forall n m : nat,
  IsomorphismDefinitions.eq (nat_to_imported (n * m)) (Imported.nat_mul (nat_to_imported n) (nat_to_imported m)).
Proof.
  induction n as [|n' IHn].
  - intro m. apply IsomorphismDefinitions.eq_refl.
  - intro m. simpl. unfold Imported.S.
    (* Goal: nat_to_imported (m + n' * m) = nat_mul (nat_S (nat_to_imported n')) (nat_to_imported m) *)
    (* nat_mul (nat_S x) y = nat_add y (nat_mul x y) *)
    apply (IsoEq.eq_trans (nat_to_imported_add m (n' * m))).
    apply (IsoEq.eq_trans (IsoEq.f_equal2 Imported.nat_add IsomorphismDefinitions.eq_refl (IHn m))).
    apply IsoEq.eq_sym. apply nat_mul_S.
Qed.

(* Helper for transporting along SProp equality *)
Definition eq_sind_r_iso : forall (A : Type) (x : A) (P : A -> SProp), P x -> forall y : A, IsomorphismDefinitions.eq y x -> P y.
Proof.
  intros A x P Hx y Heq.
  destruct Heq.
  exact Hx.
Defined.

(* Forward direction: Original.aevalR -> Imported.aevalR *)
Lemma aevalR_to_imported : forall (e : Original.LF_DOT_Imp.LF.Imp.AExp.aexp) (n : nat),
  Original.LF_DOT_Imp.LF.Imp.AExp.aevalR e n ->
  Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR (aexp_to_imported e) (nat_to_imported n).
Proof.
  fix IH 3.
  intros e n Heval.
  destruct Heval as [n' | e1 e2 n1 n2 H1 H2 | e1 e2 n1 n2 H1 H2 | e1 e2 n1 n2 H1 H2].
  - (* E_ANum *)
    simpl. apply Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_E_ANum.
  - (* E_APlus *)
    simpl.
    apply (@eq_sind_r_iso _ (Imported.nat_add (nat_to_imported n1) (nat_to_imported n2)) (fun x => Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR _ x)).
    + apply Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_E_APlus.
      * apply IH. exact H1.
      * apply IH. exact H2.
    + apply nat_to_imported_add.
  - (* E_AMinus *)
    simpl.
    apply (@eq_sind_r_iso _ (Imported.nat_sub (nat_to_imported n1) (nat_to_imported n2)) (fun x => Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR _ x)).
    + apply Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_E_AMinus.
      * apply IH. exact H1.
      * apply IH. exact H2.
    + apply nat_to_imported_sub.
  - (* E_AMult *)
    simpl.
    apply (@eq_sind_r_iso _ (Imported.nat_mul (nat_to_imported n1) (nat_to_imported n2)) (fun x => Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR _ x)).
    + apply Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_E_AMult.
      * apply IH. exact H1.
      * apply IH. exact H2.
    + apply nat_to_imported_mul.
Qed.

(* The key is: we can use the SProp eliminator to prove SProp goals from SProp hypotheses,
   and we can use sinhabitant to go from SInhabited (Prop) to Prop.
   The composition: Imported.aevalR -> SInhabited (aevalR) -> aevalR (via sinhabitant) *)

Definition aevalR_from_imported_sinhabited : forall (e : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n : imported_nat),
  Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e n ->
  SInhabited (Original.LF_DOT_Imp.LF.Imp.AExp.aevalR (imported_to_aexp e) (imported_to_nat n)).
Proof.
  intros e n Heval.
  apply (Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_sind 
           (fun e n _ => SInhabited (Original.LF_DOT_Imp.LF.Imp.AExp.aevalR (imported_to_aexp e) (imported_to_nat n)))).
  - (* E_ANum *)
    intro n'. simpl. apply sinhabits. apply Original.LF_DOT_Imp.LF.Imp.AExp.E_ANum.
  - (* E_APlus *)
    intros e1 e2 n1 n2 H1 IH1 H2 IH2.
    simpl.
    apply sinhabits.
    (* Use standard eq_ind_r to transport along the Prop equality *)
    refine (Corelib.Init.Logic.eq_ind_r (fun x => Original.LF_DOT_Imp.LF.Imp.AExp.aevalR _ x) _ (nat_add_correct n1 n2)).
    apply Original.LF_DOT_Imp.LF.Imp.AExp.E_APlus.
    + apply sinhabitant. exact IH1.
    + apply sinhabitant. exact IH2.
  - (* E_AMinus *)
    intros e1 e2 n1 n2 H1 IH1 H2 IH2.
    simpl.
    apply sinhabits.
    refine (Corelib.Init.Logic.eq_ind_r (fun x => Original.LF_DOT_Imp.LF.Imp.AExp.aevalR _ x) _ (nat_sub_correct n1 n2)).
    apply Original.LF_DOT_Imp.LF.Imp.AExp.E_AMinus.
    + apply sinhabitant. exact IH1.
    + apply sinhabitant. exact IH2.
  - (* E_AMult *)
    intros e1 e2 n1 n2 H1 IH1 H2 IH2.
    simpl.
    apply sinhabits.
    refine (Corelib.Init.Logic.eq_ind_r (fun x => Original.LF_DOT_Imp.LF.Imp.AExp.aevalR _ x) _ (nat_mul_correct n1 n2)).
    apply Original.LF_DOT_Imp.LF.Imp.AExp.E_AMult.
    + apply sinhabitant. exact IH1.
    + apply sinhabitant. exact IH2.
  - exact Heval.
Defined.

Instance Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_iso : (forall (x1 : Original.LF_DOT_Imp.LF.Imp.AExp.aexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp)
     (_ : @rel_iso Original.LF_DOT_Imp.LF.Imp.AExp.aexp imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp Original_LF__DOT__Imp_LF_Imp_AExp_aexp_iso x1 x2) (x3 : nat) (x4 : imported_nat)
     (_ : @rel_iso nat imported_nat nat_iso x3 x4),
   Iso (Original.LF_DOT_Imp.LF.Imp.AExp.aevalR x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_aevalR x2 x4)).
Proof.
  intros x1 x2 Hx x3 x4 Hn.
  unfold rel_iso in Hx, Hn. simpl in Hx, Hn.
  destruct Hx. destruct Hn.
  unshelve econstructor.
  - (* to: aevalR x1 x3 -> Imported.aevalR ... *)
    intro Horig. exact (aevalR_to_imported Horig).
  - (* from: Imported.aevalR ... -> aevalR x1 x3 *)
    intro Himp.
    apply sinhabitant.
    pose proof (aevalR_from_imported_sinhabited Himp) as H.
    pose proof (from_to Original_LF__DOT__Imp_LF_Imp_AExp_aexp_iso x1) as He. simpl in He.
    pose proof (from_to nat_iso x3) as Hn. simpl in Hn.
    (* eq_srect_nodep : P a -> eq a y -> P y *)
    exact (IsoEq.eq_srect_nodep (fun e => SInhabited (Original.LF_DOT_Imp.LF.Imp.AExp.aevalR e x3))
             (IsoEq.eq_srect_nodep (fun n => SInhabited (Original.LF_DOT_Imp.LF.Imp.AExp.aevalR (imported_to_aexp (aexp_to_imported x1)) n)) H Hn) He).
  - (* to_from *)
    intro. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro x.
    (* Both are proofs of aevalR x1 x3 : Prop, so use SProp-compatible proof irrelevance *)
    apply IsoEq.seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.AExp.aevalR := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.aevalR Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.aevalR Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_iso := {}.
