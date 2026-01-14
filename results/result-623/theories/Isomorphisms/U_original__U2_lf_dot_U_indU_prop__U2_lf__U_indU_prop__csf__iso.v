From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__even__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__div2__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_csf : imported_nat -> imported_nat := Imported.Original_LF__DOT__IndProp_LF_IndProp_csf.

(* Helper lemmas for arithmetic operations *)
Fixpoint nat_add_commutes (n m : nat) {struct n} :
  IsomorphismDefinitions.eq 
    (nat_to_imported (n + m))
    (Imported.nat_add (nat_to_imported n) (nat_to_imported m)) :=
  match n return IsomorphismDefinitions.eq 
    (nat_to_imported (n + m))
    (Imported.nat_add (nat_to_imported n) (nat_to_imported m)) with
  | O => IsomorphismDefinitions.eq_refl
  | S n' => f_equal Imported.nat_S (nat_add_commutes n' m)
  end.

Fixpoint nat_mul_commutes (n m : nat) {struct n} :
  IsomorphismDefinitions.eq 
    (nat_to_imported (n * m))
    (Imported.nat_mul (nat_to_imported n) (nat_to_imported m)) :=
  match n return IsomorphismDefinitions.eq 
    (nat_to_imported (n * m))
    (Imported.nat_mul (nat_to_imported n) (nat_to_imported m)) with
  | O => IsomorphismDefinitions.eq_refl
  | S n' => eq_trans (nat_add_commutes m (n' * m)) 
                     (f_equal2 Imported.nat_add IsomorphismDefinitions.eq_refl (nat_mul_commutes n' m))
  end.

(* Now prove that csf commutes with the isomorphism - by explicit computation on n *)
(* We need to handle that both original and imported csf do matching on even *)
Lemma csf_commutes : forall (n : nat),
  IsomorphismDefinitions.eq 
    (nat_to_imported (Original.LF_DOT_IndProp.LF.IndProp.csf n))
    (imported_Original_LF__DOT__IndProp_LF_IndProp_csf (nat_to_imported n)).
Proof.
  intro n.
  unfold Original.LF_DOT_IndProp.LF.IndProp.csf.
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_csf.
  (* Both sides match on even n *)
  pose proof (even_commutes n) as Hev.
  destruct (Original.LF_DOT_Basics.LF.Basics.even n) eqn:Heven.
  - (* even case: csf n = div2 n *)
    simpl bool_to_imported in Hev.
    (* Hev: eq imported_true (imported_even (nat_to_imported n)) *)
    eapply eq_trans.
    + apply div2_commutes.
    + apply (@eq_srect_r _ Imported.Original_LF__DOT__Basics_LF_Basics_bool_true 
               (fun b => IsomorphismDefinitions.eq 
                  (Imported.Original_LF__DOT__IndProp_LF_IndProp_div2 (nat_to_imported n))
                  (Imported.Original_LF__DOT__IndProp_LF_IndProp_csf_match_1 
                     (fun _ => Imported.nat) b
                     (fun _ => Imported.Original_LF__DOT__IndProp_LF_IndProp_div2 (nat_to_imported n))
                     (fun _ => Imported.nat_add (Imported.nat_mul (Imported.nat_S (Imported.nat_S (Imported.nat_S Imported.nat_O))) (nat_to_imported n)) (Imported.nat_S Imported.nat_O))))).
      * apply IsomorphismDefinitions.eq_refl.
      * apply eq_sym. exact Hev.
  - (* odd case: csf n = 3 * n + 1 *)
    simpl bool_to_imported in Hev.
    eapply eq_trans.
    + eapply eq_trans.
      * apply nat_add_commutes.
      * apply f_equal2; [apply nat_mul_commutes | apply IsomorphismDefinitions.eq_refl].
    + apply (@eq_srect_r _ Imported.Original_LF__DOT__Basics_LF_Basics_bool_false 
               (fun b => IsomorphismDefinitions.eq 
                  (Imported.nat_add (Imported.nat_mul (Imported.nat_S (Imported.nat_S (Imported.nat_S Imported.nat_O))) (nat_to_imported n)) (Imported.nat_S Imported.nat_O))
                  (Imported.Original_LF__DOT__IndProp_LF_IndProp_csf_match_1 
                     (fun _ => Imported.nat) b
                     (fun _ => Imported.Original_LF__DOT__IndProp_LF_IndProp_div2 (nat_to_imported n))
                     (fun _ => Imported.nat_add (Imported.nat_mul (Imported.nat_S (Imported.nat_S (Imported.nat_S Imported.nat_O))) (nat_to_imported n)) (Imported.nat_S Imported.nat_O))))).
      * apply IsomorphismDefinitions.eq_refl.
      * apply eq_sym. exact Hev.
Defined.

Instance Original_LF__DOT__IndProp_LF_IndProp_csf_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> rel_iso nat_iso (Original.LF_DOT_IndProp.LF.IndProp.csf x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_csf x2).
Proof.
  unfold rel_iso. simpl.
  intros x1 x2 H.
  apply (@eq_srect_r imported_nat (nat_to_imported x1) (fun y => IsomorphismDefinitions.eq (nat_to_imported (Original.LF_DOT_IndProp.LF.IndProp.csf x1)) (imported_Original_LF__DOT__IndProp_LF_IndProp_csf y))).
  - apply csf_commutes.
  - apply eq_sym. exact H.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.csf := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_csf := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.csf Original_LF__DOT__IndProp_LF_IndProp_csf_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.csf Imported.Original_LF__DOT__IndProp_LF_IndProp_csf Original_LF__DOT__IndProp_LF_IndProp_csf_iso := {}.