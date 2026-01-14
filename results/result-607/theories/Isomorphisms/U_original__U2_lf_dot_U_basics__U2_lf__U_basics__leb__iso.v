From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_leb : imported_nat -> imported_nat -> imported_Original_LF__DOT__Basics_LF_Basics_bool := Imported.Original_LF__DOT__Basics_LF_Basics_leb.

(* Helper lemma: imported_leb reduces on successors *)
Lemma imported_leb_SS : forall n m : Imported.nat,
  Imported.Original_LF__DOT__Basics_LF_Basics_leb (Imported.nat_S n) (Imported.nat_S m) =
  Imported.Original_LF__DOT__Basics_LF_Basics_leb n m.
Proof. intros n m. reflexivity. Qed.

(* Prove that leb is preserved across the isomorphism *)
Lemma leb_preserves : forall (n m : nat),
  bool_to_imported (Original.LF_DOT_Basics.LF.Basics.leb n m) =
  imported_Original_LF__DOT__Basics_LF_Basics_leb (nat_to_imported n) (nat_to_imported m).
Proof.
  induction n as [|n' IHn'].
  { intro m. reflexivity. }
  { intro m. destruct m as [|m'].
    { reflexivity. }
    { simpl.
      transitivity (imported_Original_LF__DOT__Basics_LF_Basics_leb (nat_to_imported n') (nat_to_imported m')).
      { apply IHn'. }
      { symmetry. apply imported_leb_SS. }
    }
  }
Qed.

(* Convert from Leibniz eq to SProp eq *)
Lemma leb_preserves_sprop : forall (n m : nat),
  IsomorphismDefinitions.eq
    (bool_to_imported (Original.LF_DOT_Basics.LF.Basics.leb n m))
    (imported_Original_LF__DOT__Basics_LF_Basics_leb (nat_to_imported n) (nat_to_imported m)).
Proof.
  intros n m.
  rewrite leb_preserves.
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance Original_LF__DOT__Basics_LF_Basics_leb_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat),
  rel_iso nat_iso x3 x4 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.leb x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_leb x2 x4).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  unfold rel_iso in H12, H34.
  destruct H12.
  destruct H34.
  unfold rel_iso.
  simpl.
  apply leb_preserves_sprop.
Defined.

Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.leb := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_leb := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.leb Original_LF__DOT__Basics_LF_Basics_leb_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.leb Imported.Original_LF__DOT__Basics_LF_Basics_leb Original_LF__DOT__Basics_LF_Basics_leb_iso := {}.