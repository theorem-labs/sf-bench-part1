From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Isomorphisms.nat__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__eqb__iso.

Definition imported_Original_LF__DOT__Tactics_LF_Tactics_sillyfun : imported_nat -> imported_Original_LF__DOT__Basics_LF_Basics_bool := Imported.Original_LF__DOT__Tactics_LF_Tactics_sillyfun.

(* Both sillyfun functions always return false, regardless of the input *)
Lemma original_sillyfun_false : forall n : nat,
  Original.LF_DOT_Tactics.LF.Tactics.sillyfun n = Original.LF_DOT_Basics.LF.Basics.false.
Proof.
  intro n.
  unfold Original.LF_DOT_Tactics.LF.Tactics.sillyfun.
  destruct (Original.LF_DOT_Basics.LF.Basics.eqb n 3); [reflexivity|].
  destruct (Original.LF_DOT_Basics.LF.Basics.eqb n 5); reflexivity.
Qed.

Lemma imported_sillyfun_false : forall n : Imported.nat,
  Imported.Original_LF__DOT__Tactics_LF_Tactics_sillyfun n = Imported.Original_LF__DOT__Basics_LF_Basics_bool_false.
Proof.
  intro n.
  unfold Imported.Original_LF__DOT__Tactics_LF_Tactics_sillyfun.
  unfold Imported.Original_LF__DOT__Basics_LF_Basics_negb_match_1.
  unfold Imported.Original_LF__DOT__Basics_LF_Basics_bool_casesOn.
  unfold Imported.Original_LF__DOT__Basics_LF_Basics_bool_recl.
  destruct (Imported.Original_LF__DOT__Basics_LF_Basics_eqb n (Imported.nat_S (Imported.nat_S (Imported.nat_S Imported.nat_O)))).
  - reflexivity.
  - destruct (Imported.Original_LF__DOT__Basics_LF_Basics_eqb n (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S Imported.nat_O)))))).
    + reflexivity.
    + reflexivity.
Qed.

Instance Original_LF__DOT__Tactics_LF_Tactics_sillyfun_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Tactics.LF.Tactics.sillyfun x1) (imported_Original_LF__DOT__Tactics_LF_Tactics_sillyfun x2).
Proof.
  intros x1 x2 H.
  destruct H as [H'].
  constructor.
  unfold imported_Original_LF__DOT__Tactics_LF_Tactics_sillyfun.
  simpl in H'.
  destruct H'.
  rewrite original_sillyfun_false.
  rewrite imported_sillyfun_false.
  simpl.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Tactics.LF.Tactics.sillyfun := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Tactics_LF_Tactics_sillyfun := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Tactics.LF.Tactics.sillyfun Original_LF__DOT__Tactics_LF_Tactics_sillyfun_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Tactics.LF.Tactics.sillyfun Imported.Original_LF__DOT__Tactics_LF_Tactics_sillyfun Original_LF__DOT__Tactics_LF_Tactics_sillyfun_iso := {}.
