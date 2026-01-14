From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_minus : imported_nat -> imported_nat -> imported_nat := Imported.Original_LF__DOT__Basics_LF_Basics_minus.

(* Helper: the to function from nat_iso *)
Definition nat_to_imported : nat -> imported_nat := to nat_iso.

(* Helper lemma: minus respects the isomorphism *)
Lemma minus_iso_aux : forall (n m : nat),
  nat_to_imported (Original.LF_DOT_Basics.LF.Basics.minus n m) = 
  Imported.Original_LF__DOT__Basics_LF_Basics_minus (nat_to_imported n) (nat_to_imported m).
Proof.
  induction n as [|n' IHn].
  - (* n = O *) intros m. simpl. reflexivity.
  - induction m as [|m' IHm].
    + (* m = O *) simpl. reflexivity.
    + (* m = S m' *) simpl.
      apply IHn.
Qed.

(* Convert standard eq to SProp eq for rewriting *)
Definition eq_to_speq {A : Type} {x y : A} (H : x = y) : IsomorphismDefinitions.eq x y :=
  match H with Logic.eq_refl => IsomorphismDefinitions.eq_refl end.

Instance Original_LF__DOT__Basics_LF_Basics_minus_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> rel_iso nat_iso (Original.LF_DOT_Basics.LF.Basics.minus x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_minus x2 x4).
Proof.
  intros x1 x2 Hx12 x3 x4 Hx34.
  unfold rel_iso in *.
  simpl in *.
  (* Hx12 : eq (nat_to_imported x1) x2 *)
  (* Hx34 : eq (nat_to_imported x3) x4 *)
  destruct Hx12.
  destruct Hx34.
  (* Now we need: eq (nat_to_imported (minus x1 x3)) (Imported.minus (nat_to_imported x1) (nat_to_imported x3)) *)
  unfold imported_Original_LF__DOT__Basics_LF_Basics_minus.
  apply eq_to_speq.
  apply minus_iso_aux.
Defined.

Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.minus := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_minus := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.minus Original_LF__DOT__Basics_LF_Basics_minus_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.minus Imported.Original_LF__DOT__Basics_LF_Basics_minus Original_LF__DOT__Basics_LF_Basics_minus_iso := {}.