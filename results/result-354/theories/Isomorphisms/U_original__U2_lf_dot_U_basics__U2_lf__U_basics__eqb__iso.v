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

(* Show that the eqb functions are the same under iso *)
Lemma eqb_transfer : forall n m : nat,
  to Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.eqb n m) =
  Imported.Original_LF__DOT__Basics_LF_Basics_eqb (to nat_iso n) (to nat_iso m).
Proof.
  fix IH 1.
  intros [|n] [|m]; simpl; try reflexivity.
  apply IH.
Qed.

Instance Original_LF__DOT__Basics_LF_Basics_eqb_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat),
  rel_iso nat_iso x3 x4 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.eqb x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_eqb x2 x4).
Proof.
  intros x1 x2 H1 x3 x4 H3.
  unfold rel_iso in *.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_eqb.
  pose proof (eqb_transfer x1 x3) as Htrans.
  refine (match H1 in IsomorphismDefinitions.eq _ y2 return IsomorphismDefinitions.eq _ (Imported.Original_LF__DOT__Basics_LF_Basics_eqb y2 x4) with
          | IsomorphismDefinitions.eq_refl => _
          end).
  refine (match H3 in IsomorphismDefinitions.eq _ y4 return IsomorphismDefinitions.eq _ (Imported.Original_LF__DOT__Basics_LF_Basics_eqb (to nat_iso x1) y4) with
          | IsomorphismDefinitions.eq_refl => _
          end).
  rewrite Htrans.
  apply IsomorphismDefinitions.eq_refl.
Qed.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.eqb := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant imported_Original_LF__DOT__Basics_LF_Basics_eqb := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.eqb Original_LF__DOT__Basics_LF_Basics_eqb_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.eqb imported_Original_LF__DOT__Basics_LF_Basics_eqb Original_LF__DOT__Basics_LF_Basics_eqb_iso := {}.