From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From Stdlib Require Import Logic.ProofIrrelevance.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__even__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__div2__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for : imported_nat -> SProp := Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for.

Definition imported_to_nat : imported_nat -> nat := from nat_iso.

(* Auxiliary lemmas about nat_add and nat_mul *)
Lemma nat_add_S : forall n m : Imported.nat,
  Imported.nat_add (Imported.nat_S n) m = Imported.nat_S (Imported.nat_add n m).
Proof. reflexivity. Qed.

Lemma nat_add_commutes : forall (n m : nat),
  IsomorphismDefinitions.eq 
    (nat_to_imported (n + m))
    (Imported.nat_add (nat_to_imported n) (nat_to_imported m)).
Proof.
  fix IH 1.
  intros n m.
  destruct n as [|n'].
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl.
    apply (eq_trans (f_equal Imported.nat_S (IH n' m))).
    apply IsomorphismDefinitions.eq_refl.
Defined.

Lemma nat_mul_S : forall n m : Imported.nat,
  Imported.nat_mul (Imported.nat_S n) m = Imported.nat_add m (Imported.nat_mul n m).
Proof. reflexivity. Qed.

Lemma nat_mul_commutes : forall (n m : nat),
  IsomorphismDefinitions.eq 
    (nat_to_imported (n * m))
    (Imported.nat_mul (nat_to_imported n) (nat_to_imported m)).
Proof.
  fix IH 1.
  intros n m.
  destruct n as [|n'].
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl.
    apply (eq_trans (nat_add_commutes m (n' * m))).
    apply (f_equal2 Imported.nat_add (IsomorphismDefinitions.eq_refl _) (IH n' m)).
Defined.

(* Collatz step commutes *)
Lemma collatz_step_commutes : forall n : nat,
  IsomorphismDefinitions.eq
    (nat_to_imported (3 * n + 1))
    (Imported.nat_add
       (Imported.nat_mul
          (Imported.nat_S (Imported.nat_S (Imported.nat_S Imported.nat_O)))
          (nat_to_imported n))
       (Imported.nat_S Imported.nat_O)).
Proof.
  intros n.
  eapply eq_trans.
  - apply nat_add_commutes.
  - apply f_equal2.
    + apply nat_mul_commutes.
    + apply IsomorphismDefinitions.eq_refl.
Defined.

(* Helper for constructing Imported equality from Rocq equality *)
Lemma bool_eq_to_imported_bool_eq : forall b1 b2 : Original.LF_DOT_Basics.LF.Basics.bool,
  b1 = b2 -> 
  Imported.Corelib_Init_Logic_eq imported_Original_LF__DOT__Basics_LF_Basics_bool (bool_to_imported b1) (bool_to_imported b2).
Proof.
  intros b1 b2 H. rewrite H. apply Imported.Corelib_Init_Logic_eq_refl.
Defined.

(* even commutes *)
Lemma even_commutes : forall n : nat,
  IsomorphismDefinitions.eq 
    (bool_to_imported (Original.LF_DOT_Basics.LF.Basics.even n))
    (Imported.Original_LF__DOT__Basics_LF_Basics_even (nat_to_imported n)).
Proof.
  fix IH 1.
  intro n.
  destruct n as [|n']; [apply IsomorphismDefinitions.eq_refl|].
  destruct n' as [|n'']; [apply IsomorphismDefinitions.eq_refl|].
  change (bool_to_imported (Original.LF_DOT_Basics.LF.Basics.even (S (S n'')))) with 
         (bool_to_imported (Original.LF_DOT_Basics.LF.Basics.even n'')).
  change (Imported.Original_LF__DOT__Basics_LF_Basics_even (nat_to_imported (S (S n'')))) with 
         (Imported.Original_LF__DOT__Basics_LF_Basics_even (Imported.nat_S (Imported.nat_S (nat_to_imported n'')))).
  change (Imported.Original_LF__DOT__Basics_LF_Basics_even (Imported.nat_S (Imported.nat_S (nat_to_imported n'')))) with
         (Imported.Original_LF__DOT__Basics_LF_Basics_even (nat_to_imported n'')).
  apply IH.
Defined.

(* Forward direction: Original -> Imported *)
Lemma collatz_to_imported : forall n : nat,
  Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for n ->
  Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for (nat_to_imported n).
Proof.
  fix IH 2.
  intros n H.
  destruct H as [|n Heven Hrec|n Hodd Hrec].
  - (* Chf_one *)
    exact Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for_Chf_one.
  - (* Chf_even *)
    pose proof (IH _ Hrec) as Hrec'.
    (* Build the equality for even *)
    pose proof (even_commutes n) as Hev.
    assert (Heven' : Imported.Corelib_Init_Logic_eq imported_Original_LF__DOT__Basics_LF_Basics_bool
                       (bool_to_imported (Original.LF_DOT_Basics.LF.Basics.even n))
                       (bool_to_imported Original.LF_DOT_Basics.LF.Basics.true)).
    { apply bool_eq_to_imported_bool_eq. exact Heven. }
    (* Transport Heven' from (bool_to_imported (even n)) to (Imported.even (nat_to_imported n)) *)
    assert (Heq : Imported.Corelib_Init_Logic_eq _ (Imported.Original_LF__DOT__Basics_LF_Basics_even (nat_to_imported n)) Imported.Original_LF__DOT__Basics_LF_Basics_bool_true).
    { 
      apply (@eq_srect imported_Original_LF__DOT__Basics_LF_Basics_bool 
                        (bool_to_imported (Original.LF_DOT_Basics.LF.Basics.even n))
                        (fun x => Imported.Corelib_Init_Logic_eq _ x Imported.Original_LF__DOT__Basics_LF_Basics_bool_true)
                        Heven'
                        (Imported.Original_LF__DOT__Basics_LF_Basics_even (nat_to_imported n))
                        Hev).
    }
    assert (Hdiv : IsomorphismDefinitions.eq (nat_to_imported (Original.LF_DOT_IndProp.LF.IndProp.div2 n)) (Imported.Original_LF__DOT__IndProp_LF_IndProp_div2 (nat_to_imported n))).
    {
      apply div2_commutes.
    }
    apply (Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for_Chf_even (nat_to_imported n) Heq).
    exact (@eq_srect imported_nat 
                      (nat_to_imported (Original.LF_DOT_IndProp.LF.IndProp.div2 n))
                      (fun x => Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for x)
                      Hrec'
                      (Imported.Original_LF__DOT__IndProp_LF_IndProp_div2 (nat_to_imported n))
                      Hdiv).
  - (* Chf_odd *)
    pose proof (IH _ Hrec) as Hrec'.
    pose proof (even_commutes n) as Hev.
    assert (Hodd' : Imported.Corelib_Init_Logic_eq imported_Original_LF__DOT__Basics_LF_Basics_bool
                      (bool_to_imported (Original.LF_DOT_Basics.LF.Basics.even n))
                      (bool_to_imported Original.LF_DOT_Basics.LF.Basics.false)).
    { apply bool_eq_to_imported_bool_eq. exact Hodd. }
    assert (Heq : Imported.Corelib_Init_Logic_eq _ (Imported.Original_LF__DOT__Basics_LF_Basics_even (nat_to_imported n)) Imported.Original_LF__DOT__Basics_LF_Basics_bool_false).
    {
      apply (@eq_srect imported_Original_LF__DOT__Basics_LF_Basics_bool 
                        (bool_to_imported (Original.LF_DOT_Basics.LF.Basics.even n))
                        (fun x => Imported.Corelib_Init_Logic_eq _ x Imported.Original_LF__DOT__Basics_LF_Basics_bool_false)
                        Hodd'
                        (Imported.Original_LF__DOT__Basics_LF_Basics_even (nat_to_imported n))
                        Hev).
    }
    pose proof (collatz_step_commutes n) as Hstep.
    apply (Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for_Chf_odd (nat_to_imported n) Heq).
    exact (@eq_srect imported_nat 
                      (nat_to_imported (3 * n + 1))
                      (fun x => Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for x)
                      Hrec'
                      (Imported.nat_add
                         (Imported.nat_mul
                            (Imported.nat_S (Imported.nat_S (Imported.nat_S Imported.nat_O)))
                            (nat_to_imported n))
                         (Imported.nat_S Imported.nat_O))
                      Hstep).
Defined.

(* Helper for even commuting with standard Coq equality *)
Lemma even_commutes_std : forall n : nat,
  to Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.even n) = 
  Imported.Original_LF__DOT__Basics_LF_Basics_even (nat_to_imported n).
Proof.
  fix IH 1.
  intro n.
  destruct n as [|n']; [reflexivity|].
  destruct n' as [|n'']; [reflexivity|].
  change (Original.LF_DOT_Basics.LF.Basics.even (S (S n''))) with (Original.LF_DOT_Basics.LF.Basics.even n'').
  change (nat_to_imported (S (S n''))) with (Imported.nat_S (Imported.nat_S (nat_to_imported n''))).
  change (Imported.Original_LF__DOT__Basics_LF_Basics_even (Imported.nat_S (Imported.nat_S (nat_to_imported n''))))
    with (Imported.Original_LF__DOT__Basics_LF_Basics_even (nat_to_imported n'')).
  apply IH.
Qed.

(* Helper: nat_to_imported (from nat_iso n) = n (with standard equality) *)
Lemma nat_to_from : forall n : imported_nat, nat_to_imported (from nat_iso n) = n.
Proof.
  intro n. unfold nat_to_imported.
  induction n as [|n' IH].
  - reflexivity.
  - simpl. f_equal. exact IH.
Qed.

(* Helper: from nat_iso (nat_to_imported n) = n (with standard equality) *)
Lemma nat_from_to : forall n : nat, from nat_iso (nat_to_imported n) = n.
Proof.
  intro n. unfold nat_to_imported.
  induction n as [|n' IH].
  - reflexivity.
  - simpl. f_equal. exact IH.
Qed.

(* Helper: injectivity of to for bool_iso *)
Lemma bool_to_inj : forall a b : Original.LF_DOT_Basics.LF.Basics.bool,
  to Original_LF__DOT__Basics_LF_Basics_bool_iso a = to Original_LF__DOT__Basics_LF_Basics_bool_iso b -> a = b.
Proof.
  intros a b Hab. destruct a, b; simpl in Hab; try reflexivity; discriminate.
Qed.

(* Convert Imported eq to standard eq for imported_bool *)
Lemma imported_eq_to_eq {A : Type} {a b : A} :
  Imported.Corelib_Init_Logic_eq A a b -> a = b.
Proof.
  intro H. destruct H. reflexivity.
Qed.

(* Backward direction helper lemmas *)
Lemma even_backward_true : forall n : imported_nat,
  Imported.Corelib_Init_Logic_eq _ (Imported.Original_LF__DOT__Basics_LF_Basics_even n) Imported.Original_LF__DOT__Basics_LF_Basics_bool_true ->
  Original.LF_DOT_Basics.LF.Basics.even (from nat_iso n) = Original.LF_DOT_Basics.LF.Basics.true.
Proof.
  intros n' H.
  apply imported_eq_to_eq in H.
  pose proof (even_commutes_std (from nat_iso n')) as Hec.
  rewrite (nat_to_from n') in Hec.
  apply bool_to_inj.
  etransitivity. { exact Hec. }
  exact H.
Defined.

Lemma even_backward_false : forall n : imported_nat,
  Imported.Corelib_Init_Logic_eq _ (Imported.Original_LF__DOT__Basics_LF_Basics_even n) Imported.Original_LF__DOT__Basics_LF_Basics_bool_false ->
  Original.LF_DOT_Basics.LF.Basics.even (from nat_iso n) = Original.LF_DOT_Basics.LF.Basics.false.
Proof.
  intros n' H.
  apply imported_eq_to_eq in H.
  pose proof (even_commutes_std (from nat_iso n')) as Hec.
  rewrite (nat_to_from n') in Hec.
  apply bool_to_inj.
  etransitivity. { exact Hec. }
  exact H.
Defined.

Lemma div2_backward : forall n : imported_nat,
  IsomorphismDefinitions.eq
    (imported_to_nat (Imported.Original_LF__DOT__IndProp_LF_IndProp_div2 n))
    (Original.LF_DOT_IndProp.LF.IndProp.div2 (imported_to_nat n)).
Proof.
  intros n.
  pose proof (div2_commutes (imported_to_nat n)) as Hdiv.
  pose proof (nat_to_from n) as Hnat.
  assert (Hdiv2 : IsomorphismDefinitions.eq (Imported.Original_LF__DOT__IndProp_LF_IndProp_div2 (nat_to_imported (imported_to_nat n)))
                                              (Imported.Original_LF__DOT__IndProp_LF_IndProp_div2 n)).
  { apply f_equal. unfold imported_to_nat. apply seq_of_eq. exact Hnat. }
  assert (Hdiv3 : IsomorphismDefinitions.eq (nat_to_imported (Original.LF_DOT_IndProp.LF.IndProp.div2 (imported_to_nat n)))
                                              (Imported.Original_LF__DOT__IndProp_LF_IndProp_div2 n)).
  { eapply eq_trans. exact Hdiv. exact Hdiv2. }
  eapply eq_trans.
  - apply f_equal. apply eq_sym. exact Hdiv3.
  - unfold imported_to_nat. apply seq_of_eq. apply nat_from_to.
Defined.

Lemma collatz_step_backward : forall n : imported_nat,
  IsomorphismDefinitions.eq
    (imported_to_nat (Imported.nat_add
                        (Imported.nat_mul
                           (Imported.nat_S (Imported.nat_S (Imported.nat_S Imported.nat_O)))
                           n)
                        (Imported.nat_S Imported.nat_O)))
    (3 * imported_to_nat n + 1).
Proof.
  intros n.
  pose proof (collatz_step_commutes (imported_to_nat n)) as Hstep.
  pose proof (nat_to_from n) as Hnat.
  assert (Hstep2 : IsomorphismDefinitions.eq
                     (Imported.nat_add
                        (Imported.nat_mul
                           (Imported.nat_S (Imported.nat_S (Imported.nat_S Imported.nat_O)))
                           (nat_to_imported (imported_to_nat n)))
                        (Imported.nat_S Imported.nat_O))
                     (Imported.nat_add
                        (Imported.nat_mul
                           (Imported.nat_S (Imported.nat_S (Imported.nat_S Imported.nat_O)))
                           n)
                        (Imported.nat_S Imported.nat_O))).
  { apply f_equal2; try apply IsomorphismDefinitions.eq_refl.
    apply f_equal. unfold imported_to_nat. apply seq_of_eq. exact Hnat. }
  assert (Hstep3 : IsomorphismDefinitions.eq
                     (nat_to_imported (3 * imported_to_nat n + 1))
                     (Imported.nat_add
                        (Imported.nat_mul
                           (Imported.nat_S (Imported.nat_S (Imported.nat_S Imported.nat_O)))
                           n)
                        (Imported.nat_S Imported.nat_O))).
  { eapply eq_trans. exact Hstep. exact Hstep2. }
  eapply eq_trans.
  - apply f_equal. apply eq_sym. exact Hstep3.
  - unfold imported_to_nat. apply seq_of_eq. apply nat_from_to.
Defined.

(* Backward direction: Imported -> Original *)
(* Since we're going from SProp to Prop, we build SInhabited and use sinhabitant *)
Lemma collatz_from_imported : forall n : imported_nat,
  Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for n ->
  SInhabited (Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for (imported_to_nat n)).
Proof.
  fix IH 2.
  intros n H.
  destruct H as [|n Heven Hrec|n Hodd Hrec].
  - (* Chf_one *)
    apply sinhabits.
    exact Original.LF_DOT_IndProp.LF.IndProp.Chf_one.
  - (* Chf_even *)
    pose proof (IH _ Hrec) as IHrec.
    apply sinhabits.
    apply (Original.LF_DOT_IndProp.LF.IndProp.Chf_even (imported_to_nat n)).
    + apply (even_backward_true n Heven).
    + exact (@eq_srect nat
               (imported_to_nat (Imported.Original_LF__DOT__IndProp_LF_IndProp_div2 n))
               (fun x => Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for x)
               (sinhabitant IHrec)
               (Original.LF_DOT_IndProp.LF.IndProp.div2 (imported_to_nat n))
               (div2_backward n)).
  - (* Chf_odd *)
    pose proof (IH _ Hrec) as IHrec.
    apply sinhabits.
    apply (Original.LF_DOT_IndProp.LF.IndProp.Chf_odd (imported_to_nat n)).
    + apply (even_backward_false n Hodd).
    + exact (@eq_srect nat
               (imported_to_nat (Imported.nat_add
                                   (Imported.nat_mul
                                      (Imported.nat_S (Imported.nat_S (Imported.nat_S Imported.nat_O)))
                                      n)
                                   (Imported.nat_S Imported.nat_O)))
               (fun x => Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for x)
               (sinhabitant IHrec)
               (3 * imported_to_nat n + 1)
               (collatz_step_backward n)).
Defined.

(* Now we can build the Iso *)
Definition collatz_to_x2 (x1 : nat) (x2 : imported_nat) 
  (Hrel : IsomorphismDefinitions.eq (nat_to_imported x1) x2)
  (Hcol : Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for x1) 
  : imported_Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for x2.
Proof.
  pose proof (@collatz_to_imported x1 Hcol) as Hres.
  exact (@eq_srect imported_nat (nat_to_imported x1)
                   (fun y => Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for y)
                   Hres x2 Hrel).
Defined.

Definition collatz_from_x1 (x1 : nat) (x2 : imported_nat) 
  (Hrel : IsomorphismDefinitions.eq (nat_to_imported x1) x2)
  (Hcol : imported_Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for x2) 
  : Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for x1.
Proof.
  pose proof (@collatz_from_imported x2 Hcol) as Hres.
  pose (Hrel' := eq_trans (f_equal imported_to_nat (eq_sym Hrel)) (seq_of_eq (nat_from_to x1))).
  exact (@eq_srect nat (imported_to_nat x2)
                   (fun y => Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for y)
                   (sinhabitant Hres) x1 Hrel').
Defined.

Lemma sprop_eq_any {A : SProp} (x y : A) : IsomorphismDefinitions.eq x y.
Proof. exact IsomorphismDefinitions.eq_refl. Qed.

(* Build the isomorphism - Original.Collatz is Prop, Imported.Collatz is SProp *)
Instance Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for x2).
Proof.
  intros x1 x2 Hrel.
  unfold rel_iso in Hrel. simpl in Hrel.
  refine (@Build_Iso _ _ (@collatz_to_x2 x1 x2 Hrel) (@collatz_from_x1 x1 x2 Hrel) _ _).
  - intro x. apply sprop_eq_any.
  - intro x. apply seq_of_eq. apply proof_irrelevance.
Defined.

Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for_iso := {}.
