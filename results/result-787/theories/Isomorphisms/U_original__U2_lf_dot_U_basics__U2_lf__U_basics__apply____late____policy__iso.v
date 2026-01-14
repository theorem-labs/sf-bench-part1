From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__grade__iso Isomorphisms.nat__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__ltb__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__lower____grade__iso.

(* Helper lemma: the imported match function is like case analysis *)
Lemma match_bool_simpl : forall (A : Type) (b : Imported.Original_LF__DOT__Basics_LF_Basics_bool) 
  (t f : Imported.Unit -> A),
  Imported.Original_LF__DOT__Basics_LF_Basics_bool__rec_match_1
    (fun _ => A) b t f =
  match b with
  | Imported.Original_LF__DOT__Basics_LF_Basics_bool_true => t Imported.Unit_unit
  | Imported.Original_LF__DOT__Basics_LF_Basics_bool_false => f Imported.Unit_unit
  end.
Proof. intros. destruct b; reflexivity. Qed.

(* Helper for if-then-else with related bools *)
Lemma if_match_rel : forall (b1 : Original.LF_DOT_Basics.LF.Basics.bool) (b2 : imported_Original_LF__DOT__Basics_LF_Basics_bool),
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso b1 b2 ->
  forall (g1 h1 : Original.LF_DOT_Basics.LF.Basics.grade) (g2 h2 : imported_Original_LF__DOT__Basics_LF_Basics_grade),
  rel_iso Original_LF__DOT__Basics_LF_Basics_grade_iso g1 g2 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_grade_iso h1 h2 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_grade_iso
    (if b1 then g1 else h1)
    (match b2 with
     | Imported.Original_LF__DOT__Basics_LF_Basics_bool_true => g2
     | Imported.Original_LF__DOT__Basics_LF_Basics_bool_false => h2
     end).
Proof.
  intros b1 b2 Hb g1 h1 g2 h2 Hg Hh.
  unfold rel_iso in Hb. simpl in Hb.
  destruct b1, b2; simpl; try exact Hg; try exact Hh.
  - (* true vs false - contradiction *) 
    unfold to, from, bool_to_imported, imported_to_bool in Hb. simpl in Hb.
    inversion Hb.
  - (* false vs true - contradiction *)
    unfold to, from, bool_to_imported, imported_to_bool in Hb. simpl in Hb.
    inversion Hb.
Qed.

(* nat isomorphism preserves constants *)
Definition nine : Datatypes.nat := 9%nat.
Definition seventeen : Datatypes.nat := 17%nat.
Definition twentyone : Datatypes.nat := 21%nat.

Lemma nat_iso_9 : rel_iso nat_iso nine (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S Imported.nat_O))))))))).
Proof. unfold rel_iso, nine. simpl. apply IsomorphismDefinitions.eq_refl. Qed.

Lemma nat_iso_17 : rel_iso nat_iso seventeen (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S Imported.nat_O))))))))))))))))).
Proof. unfold rel_iso, seventeen. simpl. apply IsomorphismDefinitions.eq_refl. Qed.

Lemma nat_iso_21 : rel_iso nat_iso twentyone (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S (Imported.nat_S Imported.nat_O))))))))))))))))))))).
Proof. unfold rel_iso, twentyone. simpl. apply IsomorphismDefinitions.eq_refl. Qed.

Definition imported_Original_LF__DOT__Basics_LF_Basics_apply__late__policy : imported_nat -> imported_Original_LF__DOT__Basics_LF_Basics_grade -> imported_Original_LF__DOT__Basics_LF_Basics_grade := Imported.Original_LF__DOT__Basics_LF_Basics_apply__late__policy.

Instance Original_LF__DOT__Basics_LF_Basics_apply__late__policy_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Basics.LF.Basics.grade) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_grade),
  rel_iso Original_LF__DOT__Basics_LF_Basics_grade_iso x3 x4 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_grade_iso (Original.LF_DOT_Basics.LF.Basics.apply_late_policy x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_apply__late__policy x2 x4).
Proof.
  intros x1 x2 Hnat x3 x4 Hgrade.
  unfold Original.LF_DOT_Basics.LF.Basics.apply_late_policy.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_apply__late__policy.
  unfold Imported.Original_LF__DOT__Basics_LF_Basics_apply__late__policy.
  (* Simplify the imported match expressions *)
  repeat rewrite match_bool_simpl.
  (* Now we need to show the nested if/match are related *)
  (* Use the ltb_iso for the boolean comparisons *)
  apply if_match_rel.
  - apply Original_LF__DOT__Basics_LF_Basics_ltb_iso; [exact Hnat | exact nat_iso_9].
  - exact Hgrade.
  - apply if_match_rel.
    + apply Original_LF__DOT__Basics_LF_Basics_ltb_iso; [exact Hnat | exact nat_iso_17].
    + apply Original_LF__DOT__Basics_LF_Basics_lower__grade_iso. exact Hgrade.
    + apply if_match_rel.
      * apply Original_LF__DOT__Basics_LF_Basics_ltb_iso; [exact Hnat | exact nat_iso_21].
      * apply Original_LF__DOT__Basics_LF_Basics_lower__grade_iso.
        apply Original_LF__DOT__Basics_LF_Basics_lower__grade_iso.
        exact Hgrade.
      * apply Original_LF__DOT__Basics_LF_Basics_lower__grade_iso.
        apply Original_LF__DOT__Basics_LF_Basics_lower__grade_iso.
        apply Original_LF__DOT__Basics_LF_Basics_lower__grade_iso.
        exact Hgrade.
Qed.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.apply_late_policy := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_apply__late__policy := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.apply_late_policy Original_LF__DOT__Basics_LF_Basics_apply__late__policy_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.apply_late_policy Imported.Original_LF__DOT__Basics_LF_Basics_apply__late__policy Original_LF__DOT__Basics_LF_Basics_apply__late__policy_iso := {}.