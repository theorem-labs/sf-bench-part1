From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__grade__iso Isomorphisms.nat__iso.

Monomorphic Definition imported_Original_LF__DOT__Basics_LF_Basics_apply__late__policy : imported_nat -> imported_Original_LF__DOT__Basics_LF_Basics_grade -> imported_Original_LF__DOT__Basics_LF_Basics_grade := Imported.Original_LF__DOT__Basics_LF_Basics_apply__late__policy.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__ltb__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__lower____grade__iso.

(* Helper to relate bool match behavior - uses proof irrelevance for impossible cases *)
Lemma bool_iso_match_case : forall (b1 : Original.LF_DOT_Basics.LF.Basics.bool) (b2 : imported_Original_LF__DOT__Basics_LF_Basics_bool),
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso b1 b2 ->
  forall (g1_true g1_false : Original.LF_DOT_Basics.LF.Basics.grade),
  forall (g2_true g2_false : imported_Original_LF__DOT__Basics_LF_Basics_grade),
  rel_iso Original_LF__DOT__Basics_LF_Basics_grade_iso g1_true g2_true ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_grade_iso g1_false g2_false ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_grade_iso
    (if b1 then g1_true else g1_false)
    (Imported.Original_LF__DOT__Basics_LF_Basics_negb_match_1
       (fun _ => imported_Original_LF__DOT__Basics_LF_Basics_grade)
       b2
       (fun _ => g2_true)
       (fun _ => g2_false)).
Proof.
  intros b1 b2 Hb g1_true g1_false g2_true g2_false Htrue Hfalse.
  destruct b1; destruct b2; destruct Hb as [Hb]; simpl in *.
  - exact Htrue.
  - (* Hb : eq bool_true bool_false - impossible *)
    assert (False) as Hcontra.
    { pose proof (eq_of_seq Hb) as H. discriminate H. }
    destruct Hcontra.
  - (* Hb : eq bool_false bool_true - impossible *)
    assert (False) as Hcontra.
    { pose proof (eq_of_seq Hb) as H. discriminate H. }
    destruct Hcontra.
  - exact Hfalse.
Defined.

(* Helper for nat constant iso *)
Lemma nat_const_iso : forall n : nat, rel_iso nat_iso n (nat_to_imported n).
Proof.
  intros. constructor. apply IsomorphismDefinitions.eq_refl.
Defined.

Monomorphic Instance Original_LF__DOT__Basics_LF_Basics_apply__late__policy_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Basics.LF.Basics.grade) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_grade),
  rel_iso Original_LF__DOT__Basics_LF_Basics_grade_iso x3 x4 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_grade_iso (Original.LF_DOT_Basics.LF.Basics.apply_late_policy x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_apply__late__policy x2 x4).
Proof.
  intros x1 x2 Hx12 x3 x4 Hx34.
  unfold Original.LF_DOT_Basics.LF.Basics.apply_late_policy.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_apply__late__policy.
  unfold Imported.Original_LF__DOT__Basics_LF_Basics_apply__late__policy.
  apply bool_iso_match_case.
  - apply Original_LF__DOT__Basics_LF_Basics_ltb_iso.
    + exact Hx12.
    + apply nat_const_iso.
  - assumption.
  - apply bool_iso_match_case.
    + apply Original_LF__DOT__Basics_LF_Basics_ltb_iso.
      * exact Hx12.
      * apply nat_const_iso.
    + apply Original_LF__DOT__Basics_LF_Basics_lower__grade_iso. assumption.
    + apply bool_iso_match_case.
      * apply Original_LF__DOT__Basics_LF_Basics_ltb_iso.
        -- exact Hx12.
        -- apply nat_const_iso.
      * apply Original_LF__DOT__Basics_LF_Basics_lower__grade_iso.
        apply Original_LF__DOT__Basics_LF_Basics_lower__grade_iso. assumption.
      * apply Original_LF__DOT__Basics_LF_Basics_lower__grade_iso.
        apply Original_LF__DOT__Basics_LF_Basics_lower__grade_iso.
        apply Original_LF__DOT__Basics_LF_Basics_lower__grade_iso. assumption.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.apply_late_policy := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_apply__late__policy := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.apply_late_policy Original_LF__DOT__Basics_LF_Basics_apply__late__policy_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.apply_late_policy Imported.Original_LF__DOT__Basics_LF_Basics_apply__late__policy Original_LF__DOT__Basics_LF_Basics_apply__late__policy_iso := {}.