From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.nat__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__even__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__div2__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_nat__mul__iso Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_s__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.

Monomorphic Definition imported_Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for : imported_nat -> SProp := Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for.

(* Forward direction: Prop to SProp *)
Lemma Collatz_forward : forall (n : nat) (m : imported_nat), 
  rel_iso nat_iso n m ->
  Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for n -> 
  imported_Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for m.
Proof.
  intros n m Hnm H.
  revert m Hnm.
  induction H as [ | n' Heven Hrec IH | n' Hodd Hrec IH]; intros m Hnm.
  - (* Chf_one case: n = 1, m = 1 *)
    assert (Hm : m = imported_S imported_0).
    { symmetry. apply (eq_of_seq (proj_rel_iso Hnm)). }
    rewrite Hm.
    apply Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for_Chf_one.
  - (* Chf_even case *)
    apply (Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for_Chf_even m).
    + apply (Corelib_Init_Logic_eq_iso 
               (Original_LF__DOT__Basics_LF_Basics_even_iso Hnm)
               (Original_LF__DOT__Basics_LF_Basics_true_iso)).
      exact Heven.
    + apply IH.
      apply Original_LF__DOT__IndProp_LF_IndProp_div2_iso.
      exact Hnm.
  - (* Chf_odd case *)
    apply (Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for_Chf_odd m).
    + apply (Corelib_Init_Logic_eq_iso 
               (Original_LF__DOT__Basics_LF_Basics_even_iso Hnm)
               (Original_LF__DOT__Basics_LF_Basics_false_iso)).
      exact Hodd.
    + assert (Hiso3 : rel_iso nat_iso (S (S (S O))) (imported_S (imported_S (imported_S imported_0)))).
      { apply S_iso. apply S_iso. apply S_iso. exact _0_iso. }
      assert (Hiso1 : rel_iso nat_iso (S O) (imported_S imported_0)).
      { apply S_iso. exact _0_iso. }
      apply IH.
      apply Nat_add_iso.
      apply Nat_mul_iso. exact Hiso3. exact Hnm.
      exact Hiso1.
Qed.

(* Helper for the backward direction *)
Definition cast_Collatz (n1 n2 : nat) (H : n1 = n2) 
  (c : Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for n1) 
  : Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for n2 :=
  match H in Logic.eq _ x return Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for x with
  | Logic.eq_refl => c
  end.

(* Backward direction: SProp to SInhabited Prop *)
Fixpoint Collatz_backward_aux (m : imported_nat) 
  (H : imported_Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for m)
  (n : nat) (Hnm : rel_iso nat_iso n m) {struct H}
  : SInhabited (Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for n).
Proof.
  destruct H as [ | m' Heven' Hrec | m' Hodd' Hrec ].
  - (* Chf_one case *)
    apply sinhabits.
    pose proof (proj_rel_iso Hnm) as Heq.
    pose proof (eq_of_seq (@iso_move_r_seq _ _ nat_iso n _ Heq)) as Hn.
    exact (cast_Collatz (Logic.eq_sym Hn) Original.LF_DOT_IndProp.LF.IndProp.Chf_one).
  - (* Chf_even case *)
    assert (Hdiv2_iso : rel_iso nat_iso (Original.LF_DOT_IndProp.LF.IndProp.div2 n) (imported_Original_LF__DOT__IndProp_LF_IndProp_div2 m')).
    { apply Original_LF__DOT__IndProp_LF_IndProp_div2_iso. exact Hnm. }
    specialize (Collatz_backward_aux _ Hrec _ Hdiv2_iso).
    destruct Collatz_backward_aux as [IH].
    apply sinhabits.
    apply (Original.LF_DOT_IndProp.LF.IndProp.Chf_even n).
    + apply (from (Corelib_Init_Logic_eq_iso 
               (Original_LF__DOT__Basics_LF_Basics_even_iso Hnm)
               (Original_LF__DOT__Basics_LF_Basics_true_iso))).
      exact Heven'.
    + exact IH.
  - (* Chf_odd case *)
    assert (Hiso3 : rel_iso nat_iso (S (S (S O))) (imported_S (imported_S (imported_S imported_0)))).
    { apply S_iso. apply S_iso. apply S_iso. exact _0_iso. }
    assert (Hiso1 : rel_iso nat_iso (S O) (imported_S imported_0)).
    { apply S_iso. exact _0_iso. }
    assert (Hrec_iso : rel_iso nat_iso (S (S (S O)) * n + S O) (imported_Nat_add (imported_Nat_mul (imported_S (imported_S (imported_S imported_0))) m') (imported_S imported_0))).
    { apply Nat_add_iso. apply Nat_mul_iso. exact Hiso3. exact Hnm. exact Hiso1. }
    specialize (Collatz_backward_aux _ Hrec _ Hrec_iso).
    destruct Collatz_backward_aux as [IH].
    apply sinhabits.
    apply (Original.LF_DOT_IndProp.LF.IndProp.Chf_odd n).
    + apply (from (Corelib_Init_Logic_eq_iso 
               (Original_LF__DOT__Basics_LF_Basics_even_iso Hnm)
               (Original_LF__DOT__Basics_LF_Basics_false_iso))).
      exact Hodd'.
    + exact IH.
Defined.

Lemma Collatz_backward : forall (n : nat) (m : imported_nat), 
  rel_iso nat_iso n m ->
  imported_Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for m ->
  Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for n.
Proof.
  intros n m Hnm H.
  apply sinhabitant.
  exact (@Collatz_backward_aux m H n Hnm).
Qed.

Monomorphic Instance Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for x2).
Proof.
  intros n m Hnm.
  refine {| to := @Collatz_forward n m Hnm ; 
            from := @Collatz_backward n m Hnm |}.
  - (* to_from: roundtrip from SProp back - this is in SProp so eq_refl works *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: roundtrip from Prop back - use proof irrelevance *)
    intro x. apply seq_of_eq.
    apply ProofIrrelevance.proof_irrelevance.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for := {}.
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for := {}.
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for_iso := {}.
