From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_eqb : imported_nat -> imported_nat -> imported_Original_LF__DOT__Basics_LF_Basics_bool := Imported.Original_LF__DOT__Basics_LF_Basics_eqb.

(* Helper lemma: the imported eqb computes the same as the original *)
Lemma eqb_iso_helper : forall (n m : nat),
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso 
    (Original.LF_DOT_Basics.LF.Basics.eqb n m) 
    (imported_Original_LF__DOT__Basics_LF_Basics_eqb (to nat_iso n) (to nat_iso m)).
Proof.
  intro n.
  induction n as [|n' IHn'].
  - (* n = 0 *)
    intro m.
    destruct m as [|m'].
    + (* m = 0: eqb 0 0 = true *)
      simpl. unfold rel_iso. simpl. apply IsomorphismDefinitions.eq_refl.
    + (* m = S m': eqb 0 (S m') = false *)
      simpl. unfold rel_iso. simpl. apply IsomorphismDefinitions.eq_refl.
  - (* n = S n' *)
    intro m.
    destruct m as [|m'].
    + (* m = 0: eqb (S n') 0 = false *)
      simpl. unfold rel_iso. simpl. apply IsomorphismDefinitions.eq_refl.
    + (* m = S m': eqb (S n') (S m') = eqb n' m' *)
      simpl.
      apply IHn'.
Qed.

Instance Original_LF__DOT__Basics_LF_Basics_eqb_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat),
  rel_iso nat_iso x3 x4 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.eqb x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_eqb x2 x4).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  unfold rel_iso in *.
  (* H12 : to nat_iso x1 = x2, H34 : to nat_iso x3 = x4 *)
  pose (eqb_x1_x3 := eqb_iso_helper x1 x3).
  unfold rel_iso in eqb_x1_x3.
  (* Need to transport from (to nat_iso x1, to nat_iso x3) to (x2, x4) *)
  pose (step1 := IsoEq.f_equal (fun y => imported_Original_LF__DOT__Basics_LF_Basics_eqb y (to nat_iso x3)) H12).
  pose (step2 := IsoEq.f_equal (fun y => imported_Original_LF__DOT__Basics_LF_Basics_eqb x2 y) H34).
  exact (IsoEq.eq_trans eqb_x1_x3 (IsoEq.eq_trans step1 step2)).
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.eqb := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_eqb := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.eqb Original_LF__DOT__Basics_LF_Basics_eqb_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.eqb Imported.Original_LF__DOT__Basics_LF_Basics_eqb Original_LF__DOT__Basics_LF_Basics_eqb_iso := {}.