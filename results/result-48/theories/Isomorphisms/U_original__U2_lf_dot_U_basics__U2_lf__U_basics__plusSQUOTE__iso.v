From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_plus' : imported_nat -> imported_nat -> imported_nat := Imported.Original_LF__DOT__Basics_LF_Basics_plus'.

(* plus' is defined in Original.v (not Admitted), so we need to prove equivalence *)
Lemma plus'_preserves : forall n m : nat,
  Logic.eq (nat_to_imported (Original.LF_DOT_Basics.LF.Basics.plus' n m))
           (Imported.Original_LF__DOT__Basics_LF_Basics_plus' (nat_to_imported n) (nat_to_imported m)).
Proof.
  induction n; intros m.
  - reflexivity.
  - simpl.
    change (Imported.nat_S (nat_to_imported (Original.LF_DOT_Basics.LF.Basics.plus' n m)) =
            Imported.nat_S (Imported.Original_LF__DOT__Basics_LF_Basics_plus' (nat_to_imported n) (nat_to_imported m))).
    f_equal.
    apply IHn.
Defined.

Instance Original_LF__DOT__Basics_LF_Basics_plus'_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> rel_iso nat_iso (Original.LF_DOT_Basics.LF.Basics.plus' x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_plus' x2 x4).
Proof.
  intros x1 x2 [h1] x3 x4 [h2].
  simpl in *.
  destruct h1, h2.
  constructor.
  simpl.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_plus'.
  apply seq_of_eq.
  apply plus'_preserves.
Defined.

Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.plus' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_plus' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.plus' Original_LF__DOT__Basics_LF_Basics_plus'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.plus' Imported.Original_LF__DOT__Basics_LF_Basics_plus' Original_LF__DOT__Basics_LF_Basics_plus'_iso := {}.