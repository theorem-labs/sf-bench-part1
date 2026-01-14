From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Isomorphisms.nat__iso.

(* Define eqb manually since it's not in Imported.v *)
Fixpoint imported_Original_LF__DOT__Basics_LF_Basics_eqb (n m : imported_nat) : imported_Original_LF__DOT__Basics_LF_Basics_bool :=
  match n, m with
  | Imported.O, Imported.O => Original_LF__DOT__Basics_LF_Basics_bool_true
  | Imported.O, Imported.S _ => Original_LF__DOT__Basics_LF_Basics_bool_false
  | Imported.S _, Imported.O => Original_LF__DOT__Basics_LF_Basics_bool_false
  | Imported.S n', Imported.S m' => imported_Original_LF__DOT__Basics_LF_Basics_eqb n' m'
  end.
Instance Original_LF__DOT__Basics_LF_Basics_eqb_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat),
  rel_iso nat_iso x3 x4 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.eqb x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_eqb x2 x4).
Proof.
  intros x1 x2 H1 x3 x4 H3.
  unfold rel_iso in *.
  generalize dependent x4.
  generalize dependent x3.
  generalize dependent x2.
  generalize dependent x1.
  fix IH 1.
  intros [|x1] x2 H1 [|x3] x4 H3.
  - inversion H1. inversion H3. simpl. reflexivity.
  - inversion H1. inversion H3. simpl. reflexivity.
  - inversion H1. inversion H3. simpl. reflexivity.
  - inversion H1. inversion H3. simpl. apply IH; reflexivity.
Qed.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.eqb := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant imported_Original_LF__DOT__Basics_LF_Basics_eqb := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.eqb Original_LF__DOT__Basics_LF_Basics_eqb_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.eqb imported_Original_LF__DOT__Basics_LF_Basics_eqb Original_LF__DOT__Basics_LF_Basics_eqb_iso := {}.