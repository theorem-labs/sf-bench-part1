From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import Logic.ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
#[local] Set Printing Coercions.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aevalU_r____division__aexp__iso Isomorphisms.nat__iso Isomorphisms.gt__iso Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_nat__sub__iso Isomorphisms.U_nat__mul__iso.

Monomorphic Definition imported_Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR : imported_Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp -> imported_nat -> SProp := Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR.

(* Cast helper for SProp - inverse direction *)
Definition aevalR_cast_inv {a1 a2 : imported_Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp} {n1 n2 : imported_nat}
  (H1 : IsomorphismDefinitions.eq a2 a1) (H2 : IsomorphismDefinitions.eq n2 n1)
  (ev : Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a1 n1) :
  Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a2 n2.
Proof.
  destruct H1, H2. exact ev.
Defined.

(* Forward direction: aevalR a n -> Imported.aevalR (aexp_iso a) (nat_iso n) *)
Lemma aevalR_to_imported : forall a n,
  Original.LF_DOT_Imp.LF.Imp.aevalR_division.aevalR a n ->
  Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR
    (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_iso a)
    (nat_iso n).
Proof.
  fix IH 3.
  intros a n H.
  destruct H.
  - (* E_ANum *)
    apply Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR_E_ANum.
  - (* E_APlus *)
    apply (aevalR_cast_inv IsomorphismDefinitions.eq_refl (proj_rel_iso (Nat_add_iso (rel_iso_refl _) (rel_iso_refl _)))).
    apply Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR_E_APlus.
    + apply IH. exact H.
    + apply IH. exact H0.
  - (* E_AMinus *)
    apply (aevalR_cast_inv IsomorphismDefinitions.eq_refl (proj_rel_iso (Nat_sub_iso (rel_iso_refl _) (rel_iso_refl _)))).
    apply Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR_E_AMinus.
    + apply IH. exact H.
    + apply IH. exact H0.
  - (* E_AMult *)
    apply (aevalR_cast_inv IsomorphismDefinitions.eq_refl (proj_rel_iso (Nat_mul_iso (rel_iso_refl _) (rel_iso_refl _)))).
    apply Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR_E_AMult.
    + apply IH. exact H.
    + apply IH. exact H0.
  - (* E_ADiv *)
    apply (Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR_E_ADiv 
           (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_iso a1) 
           (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_iso a2)
           (nat_iso n1) (nat_iso n2) (nat_iso n3)).
    + apply IH. exact H.
    + apply IH. exact H0.
    + exact (gt_iso (rel_iso_refl n2) (rel_iso_refl O) H1).
    + (* eq (n2 * n3) n1 -> eq (Nat_mul (nat_iso n2) (nat_iso n3)) (nat_iso n1) *)
      pose proof (Corelib_Init_Logic_eq_iso 
        (Nat_mul_iso (rel_iso_refl n2) (rel_iso_refl n3)) 
        (rel_iso_refl n1) H2) as Heq.
      exact Heq.
Qed.

(* Helper: convert nat from imported representation *)
Fixpoint nat_from_imported (n : imported_nat) : Datatypes.nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S n' => S (nat_from_imported n')
  end.

(* Helper: convert aexp from imported representation *)
Fixpoint aexp_from_imported (a : imported_Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp) : Original.LF_DOT_Imp.LF.Imp.aevalR_division.aexp :=
  match a with
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_ANum n => 
      Original.LF_DOT_Imp.LF.Imp.aevalR_division.ANum (nat_from_imported n)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_APlus a1 a2 => 
      Original.LF_DOT_Imp.LF.Imp.aevalR_division.APlus (aexp_from_imported a1) (aexp_from_imported a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_AMinus a1 a2 => 
      Original.LF_DOT_Imp.LF.Imp.aevalR_division.AMinus (aexp_from_imported a1) (aexp_from_imported a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_AMult a1 a2 => 
      Original.LF_DOT_Imp.LF.Imp.aevalR_division.AMult (aexp_from_imported a1) (aexp_from_imported a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_ADiv a1 a2 => 
      Original.LF_DOT_Imp.LF.Imp.aevalR_division.ADiv (aexp_from_imported a1) (aexp_from_imported a2)
  end.

(* nat_from/to roundtrip *)
Lemma nat_from_to_eq : forall n, nat_from_imported (nat_iso n) = n.
Proof. induction n; simpl; [reflexivity | f_equal; exact IHn]. Qed.

Lemma aexp_from_to_eq : forall a, aexp_from_imported (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_iso a) = a.
Proof.
  induction a; simpl; try reflexivity;
  try (f_equal; [exact IHa1 | exact IHa2]);
  f_equal; apply nat_from_to_eq.
Qed.

(* Helper for le and gt *)
Lemma le_0_n : forall n : Datatypes.nat, (0 <= n)%nat.
Proof. intros n. induction n; [apply le_n | apply le_S; exact IHn]. Qed.

(* Convert Imported.gt to SInhabited of Coq gt *)
Fixpoint gt_to_SInhabited (n m : imported_nat) (H : Imported.gt n m) {struct H} :
  SInhabited (nat_from_imported n > nat_from_imported m).
Proof.
  destruct H as [n' | n' m' H'].
  - (* gt_gt_succ n' : gt (S n') nat_O *)
    simpl. apply sinhabits. unfold Peano.gt, Peano.lt. apply le_n_S. apply le_0_n.
  - (* gt_gt_succ_succ n' m' H' : gt (S n') (S m') *)
    simpl. apply sinhabits. 
    pose (IH := gt_to_SInhabited n' m' H').
    pose (prf := @sinhabitant _ IH).
    unfold Peano.gt, Peano.lt in *. apply le_n_S. exact prf.
Defined.

(* Arithmetic correspondence *)
Lemma add_from_iso' : forall (n m : imported_nat),
  nat_from_imported (Imported.Nat_add n m) = (nat_from_imported n + nat_from_imported m)%nat.
Proof.
  fix IH 1. intros n m. destruct n; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Lemma sub_from_iso' : forall (n m : imported_nat),
  nat_from_imported (Imported.Nat_sub n m) = (nat_from_imported n - nat_from_imported m)%nat.
Proof.
  induction n as [|n' IHn]; intros m.
  - destruct m; simpl; reflexivity.
  - destruct m as [|m']; simpl.
    + reflexivity.
    + apply IHn.
Qed.

Lemma mul_from_iso' : forall (n m : imported_nat),
  nat_from_imported (Imported.Nat_mul n m) = (nat_from_imported n * nat_from_imported m)%nat.
Proof.
  fix IH 1. intros n m. destruct n; simpl.
  - reflexivity.
  - transitivity (nat_from_imported m + nat_from_imported (Imported.Nat_mul n m))%nat.
    + apply add_from_iso'.
    + f_equal. apply IH.
Qed.

(* Convert Imported.Corelib_Init_Logic_eq to SInhabited of Coq eq *)
Definition Eq_to_SInhabited {A : Type} (x y : A) (H : Imported.Corelib_Init_Logic_eq A x y) :
  SInhabited (x = y).
Proof.
  destruct H. apply sinhabits. reflexivity.
Defined.

(* Helper for transport *)
Definition eq_rect_r {A : Type} {x : A} (P : A -> Type) (H : P x) {y : A} (e : y = x) : P y :=
  match e in (_ = z) return P z -> P y with Logic.eq_refl => fun h => h end H.

(* Backward direction via SInhabited *)
Fixpoint aevalR_to_SInhabited 
  (e : imported_Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp) (n : imported_nat)
  (H : Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR e n) {struct H} :
  SInhabited (Original.LF_DOT_Imp.LF.Imp.aevalR_division.aevalR (aexp_from_imported e) (nat_from_imported n)).
Proof.
  destruct H as [ n0 | a1 a2 n1 n2 ev1 ev2 | a1 a2 n1 n2 ev1 ev2 | a1 a2 n1 n2 ev1 ev2 | a1 a2 n1 n2 n3 ev1 ev2 gt_n2 eq_mul ].
  - (* E_ANum *) apply sinhabits. apply Original.LF_DOT_Imp.LF.Imp.aevalR_division.E_ANum.
  - (* E_APlus *)
    pose (IH1 := aevalR_to_SInhabited _ _ ev1).
    pose (IH2 := aevalR_to_SInhabited _ _ ev2).
    apply sinhabits. simpl.
    set (e' := Original.LF_DOT_Imp.LF.Imp.aevalR_division.APlus (aexp_from_imported a1) (aexp_from_imported a2)).
    apply (eq_rect_r (fun k => Original.LF_DOT_Imp.LF.Imp.aevalR_division.aevalR e' k)
      (Original.LF_DOT_Imp.LF.Imp.aevalR_division.E_APlus _ _ _ _ (sinhabitant IH1) (sinhabitant IH2))
      (add_from_iso' n1 n2)).
  - (* E_AMinus *)
    pose (IH1 := aevalR_to_SInhabited _ _ ev1).
    pose (IH2 := aevalR_to_SInhabited _ _ ev2).
    apply sinhabits. simpl.
    set (e' := Original.LF_DOT_Imp.LF.Imp.aevalR_division.AMinus (aexp_from_imported a1) (aexp_from_imported a2)).
    apply (eq_rect_r (fun k => Original.LF_DOT_Imp.LF.Imp.aevalR_division.aevalR e' k)
      (Original.LF_DOT_Imp.LF.Imp.aevalR_division.E_AMinus _ _ _ _ (sinhabitant IH1) (sinhabitant IH2))
      (sub_from_iso' n1 n2)).
  - (* E_AMult *)
    pose (IH1 := aevalR_to_SInhabited _ _ ev1).
    pose (IH2 := aevalR_to_SInhabited _ _ ev2).
    apply sinhabits. simpl.
    set (e' := Original.LF_DOT_Imp.LF.Imp.aevalR_division.AMult (aexp_from_imported a1) (aexp_from_imported a2)).
    apply (eq_rect_r (fun k => Original.LF_DOT_Imp.LF.Imp.aevalR_division.aevalR e' k)
      (Original.LF_DOT_Imp.LF.Imp.aevalR_division.E_AMult _ _ _ _ (sinhabitant IH1) (sinhabitant IH2))
      (mul_from_iso' n1 n2)).
  - (* E_ADiv *)
    pose (IH1 := aevalR_to_SInhabited _ _ ev1).
    pose (IH2 := aevalR_to_SInhabited _ _ ev2).
    pose (gt_prf := @gt_to_SInhabited n2 Imported._0 gt_n2).
    pose (eq_prf := @Eq_to_SInhabited Imported.nat (Imported.Nat_mul n2 n3) n1 eq_mul).
    apply sinhabits. simpl.
    apply (Original.LF_DOT_Imp.LF.Imp.aevalR_division.E_ADiv 
           (aexp_from_imported a1) (aexp_from_imported a2)
           (nat_from_imported n1) (nat_from_imported n2) (nat_from_imported n3)).
    + apply sinhabitant; assumption.
    + apply sinhabitant; assumption.
    + simpl in gt_prf. apply sinhabitant. exact gt_prf.
    + (* n2 * n3 = n1 - need to prove: (nat_from_imported n2 * nat_from_imported n3 = nat_from_imported n1) *)
      transitivity (nat_from_imported (Imported.Nat_mul n2 n3)).
      * symmetry. apply mul_from_iso'.
      * (* Now need: nat_from_imported (Imported.Nat_mul n2 n3) = nat_from_imported n1 *)
        (* From eq_prf we have: SInhabited (Imported.Nat_mul n2 n3 = n1) *)
        pose (eq_val := sinhabitant eq_prf).
        f_equal. exact eq_val.
Defined.

(* Now the from_imported lemma *)
Lemma aevalR_from_imported (a : Original.LF_DOT_Imp.LF.Imp.aevalR_division.aexp) (n : Datatypes.nat)
  (H : Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_iso a) (nat_iso n)) :
  Original.LF_DOT_Imp.LF.Imp.aevalR_division.aevalR a n.
Proof.
  set (e' := Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_iso a).
  set (n' := nat_iso n).
  change (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_iso a) with e' in H.
  change (nat_iso n) with n' in H.
  pose proof (@aevalR_to_SInhabited e' n' H) as H'.
  pose proof (@sinhabitant _ H') as prf.
  subst e' n'.
  rewrite <- (aexp_from_to_eq a).
  rewrite <- (nat_from_to_eq n).
  exact prf.
Defined.

Monomorphic Instance Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.aevalR_division.aexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (Original.LF_DOT_Imp.LF.Imp.aevalR_division.aevalR x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR x2 x4).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  pose proof (proj_rel_iso H12) as E12.
  pose proof (proj_rel_iso H34) as E34.
  simpl in E12, E34.
  rewrite <- (eq_of_seq E12), <- (eq_of_seq E34).
  unfold imported_Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR.
  apply relax_Iso_Ps_Ts.
  exact (@Build_Iso@{Prop SProp; Set Set}
    (Original.LF_DOT_Imp.LF.Imp.aevalR_division.aevalR x1 x3)
    (Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_iso x1) (nat_iso x3))
    (fun p => @aevalR_to_imported x1 x3 p)
    (fun sp => @aevalR_from_imported x1 x3 sp)
    (fun sp => IsomorphismDefinitions.eq_refl)
    (fun p => IsoEq.seq_of_peq (proof_irrelevance _ _ p))).
Defined.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.aevalR_division.aevalR := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.aevalR_division.aevalR Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.aevalR_division.aevalR Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR_iso := {}.
