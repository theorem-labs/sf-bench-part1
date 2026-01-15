From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__even__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__div2__iso.
From IsomorphismChecker Require Export Isomorphisms.U_nat__add__iso.
From IsomorphismChecker Require Export Isomorphisms.U_nat__mul__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_csf : imported_nat -> imported_nat := Imported.Original_LF__DOT__IndProp_LF_IndProp_csf.

Lemma even_commutes : forall (n : nat),
  Imported.Original_LF__DOT__Basics_LF_Basics_even (nat_to_imported n) = 
  Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.even n).
Proof.
  intro n. symmetry. apply even_commutes_with_to.
Qed.

Require Import Lia.
(* Helper to show n + (n + (n + 0)) = 3 * n *)
Lemma three_times_n : forall n : nat, n + (n + (n + 0)) = 3 * n.
Proof. intro n. lia. Qed.

Lemma csf_commutes : forall (n : nat),
  IsomorphismDefinitions.eq 
    (nat_to_imported (Original.LF_DOT_IndProp.LF.IndProp.csf n))
    (imported_Original_LF__DOT__IndProp_LF_IndProp_csf (nat_to_imported n)).
Proof.
  intro n.
  unfold Original.LF_DOT_IndProp.LF.IndProp.csf.
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_csf, Imported.Original_LF__DOT__IndProp_LF_IndProp_csf.
  unfold Imported.Original_LF__DOT__Basics_LF_Basics_negb_match_1.
  unfold Imported.Original_LF__DOT__Basics_LF_Basics_bool_casesOn.
  simpl.
  unfold Imported.Original_LF__DOT__Basics_LF_Basics_bool_recl.
  rewrite even_commutes.
  destruct (Original.LF_DOT_Basics.LF.Basics.even n) eqn:Heven.
  - (* even n = true *)
    simpl. apply div2_commutes.
  - (* even n = false - 3*n+1 case *)
    simpl.
    rewrite three_times_n.
    rewrite nat_to_imported_add_compat.
    apply IsoEq.f_equal2.
    + apply nat_to_imported_mul_compat.
    + reflexivity.
Defined.

Instance Original_LF__DOT__IndProp_LF_IndProp_csf_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> rel_iso nat_iso (Original.LF_DOT_IndProp.LF.IndProp.csf x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_csf x2).
Proof.
  intros n1 n2 [H]. constructor. simpl in *.
  apply (@eq_srect_r imported_nat (nat_to_imported n1) (fun y => IsomorphismDefinitions.eq (nat_to_imported (Original.LF_DOT_IndProp.LF.IndProp.csf n1)) (imported_Original_LF__DOT__IndProp_LF_IndProp_csf y))).
  - apply csf_commutes.
  - apply eq_sym. exact H.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.csf := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_csf := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.csf Original_LF__DOT__IndProp_LF_IndProp_csf_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.csf Imported.Original_LF__DOT__IndProp_LF_IndProp_csf Original_LF__DOT__IndProp_LF_IndProp_csf_iso := {}.