From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_plus : imported_nat -> imported_nat -> imported_nat := Imported.Original_LF__DOT__Basics_LF_Basics_plus.

(* Prove the isomorphism by induction on x1 *)
Instance Original_LF__DOT__Basics_LF_Basics_plus_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> rel_iso nat_iso (Original.LF_DOT_Basics.LF.Basics.plus x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_plus x2 x4).
Proof.
  unfold rel_iso, imported_Original_LF__DOT__Basics_LF_Basics_plus. simpl.
  fix IH 1.
  intros x1 x2 H12 x3 x4 H34.
  destruct x1 as [| x1'].
  - (* x1 = O *)
    simpl. destruct H12. simpl. exact H34.
  - (* x1 = S x1' *)
    simpl.
    destruct H12. simpl.
    apply (f_equal Imported.nat_S).
    apply IH.
    + apply IsomorphismDefinitions.eq_refl.
    + exact H34.
Defined.

Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.plus := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_plus := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.plus Original_LF__DOT__Basics_LF_Basics_plus_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.plus Imported.Original_LF__DOT__Basics_LF_Basics_plus Original_LF__DOT__Basics_LF_Basics_plus_iso := {}.