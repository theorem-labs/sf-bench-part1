From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Isomorphisms.nat__iso.
Local Open Scope nat_scope.

Monomorphic Definition imported_Original_LF__DOT__Logic_LF_Logic_is__even__prime : imported_nat -> imported_Original_LF__DOT__Basics_LF_Basics_bool := Imported.Original_LF__DOT__Logic_LF_Logic_is__even__prime.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__eqb__iso.
From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_s__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso.

Lemma bool_iso_inj_true : forall b2,
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso Original.LF_DOT_Basics.LF.Basics.true b2 ->
  b2 = Imported.Original_LF__DOT__Basics_LF_Basics_bool_true.
Proof.
  intros b2 H. destruct H as [H].
  apply eq_of_seq in H. simpl in H. auto.
Qed.

Lemma bool_iso_inj_false : forall b2,
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso Original.LF_DOT_Basics.LF.Basics.false b2 ->
  b2 = Imported.Original_LF__DOT__Basics_LF_Basics_bool_false.
Proof.
  intros b2 H. destruct H as [H].
  apply eq_of_seq in H. simpl in H. auto.
Qed.

Lemma negb_match_1_eq : forall b,
  Imported.Original_LF__DOT__Basics_LF_Basics_negb_match_1
       (fun _ : Imported.Original_LF__DOT__Basics_LF_Basics_bool =>
        Imported.Original_LF__DOT__Basics_LF_Basics_bool)
       b
       (fun _ : Imported.Unit =>
        Imported.Original_LF__DOT__Basics_LF_Basics_bool_true)
       (fun _ : Imported.Unit =>
        Imported.Original_LF__DOT__Basics_LF_Basics_bool_false) =
  match b with
  | Imported.Original_LF__DOT__Basics_LF_Basics_bool_true => Imported.Original_LF__DOT__Basics_LF_Basics_bool_true
  | Imported.Original_LF__DOT__Basics_LF_Basics_bool_false => Imported.Original_LF__DOT__Basics_LF_Basics_bool_false
  end.
Proof.
  intro b. destruct b; reflexivity.
Qed.

Monomorphic Instance Original_LF__DOT__Logic_LF_Logic_is__even__prime_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Logic.LF.Logic.is_even_prime x1) (imported_Original_LF__DOT__Logic_LF_Logic_is__even__prime x2).
Proof.
  intros x1 x2 Hx.
  pose proof (Original_LF__DOT__Basics_LF_Basics_eqb_iso Hx (S_iso (S_iso _0_iso))) as Heqb.
  unfold Original.LF_DOT_Logic.LF.Logic.is_even_prime.
  unfold imported_Original_LF__DOT__Logic_LF_Logic_is__even__prime.
  unfold Imported.Original_LF__DOT__Logic_LF_Logic_is__even__prime.
  rewrite negb_match_1_eq.
  change (Imported.Original_LF__DOT__Basics_LF_Basics_eqb x2 (Imported.S (Imported.S Imported._0)))
    with (imported_Original_LF__DOT__Basics_LF_Basics_eqb x2 (imported_S (imported_S imported_0))).
  destruct (Original.LF_DOT_Basics.LF.Basics.eqb x1 2) eqn:E1.
  - apply bool_iso_inj_true in Heqb. rewrite Heqb.
    apply Original_LF__DOT__Basics_LF_Basics_true_iso.
  - apply bool_iso_inj_false in Heqb. rewrite Heqb.
    apply Original_LF__DOT__Basics_LF_Basics_false_iso.
Defined.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.is_even_prime := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_is__even__prime := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.is_even_prime Original_LF__DOT__Logic_LF_Logic_is__even__prime_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.is_even_prime Imported.Original_LF__DOT__Logic_LF_Logic_is__even__prime Original_LF__DOT__Logic_LF_Logic_is__even__prime_iso := {}.