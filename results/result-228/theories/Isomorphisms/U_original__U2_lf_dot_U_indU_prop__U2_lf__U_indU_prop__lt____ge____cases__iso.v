From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.ge__iso Isomorphisms.lt__iso Isomorphisms.or__iso.

Local Open Scope nat_scope.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_lt__ge__cases : forall x x0 : imported_nat, imported_or (imported_lt x x0) (imported_ge x x0) := Imported.Original_LF__DOT__IndProp_LF_IndProp_lt__ge__cases.

(* The original lt_ge_cases is Admitted in Original.v, so this isomorphism is allowed to be Admitted *)
Instance Original_LF__DOT__IndProp_LF_IndProp_lt__ge__cases_iso : forall (x1 : Datatypes.nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : Datatypes.nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4),
  rel_iso
    {|
      to := or_iso (lt_iso hx hx0) (ge_iso hx hx0);
      from := from (or_iso (lt_iso hx hx0) (ge_iso hx hx0));
      to_from := fun x : imported_or (imported_lt x2 x4) (imported_ge x2 x4) => to_from (or_iso (lt_iso hx hx0) (ge_iso hx hx0)) x;
      from_to := fun x : Peano.lt x1 x3 \/ Peano.ge x1 x3 => seq_p_of_t (from_to (or_iso (lt_iso hx hx0) (ge_iso hx hx0)) x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.lt_ge_cases x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_lt__ge__cases x2 x4).
Proof.
  intros x1 x2 hx x3 x4 hx0.
  (* The goal is to prove that the two or values are related.
     Both original and imported are axioms (admitted theorems),
     so we need to use the structure of the isomorphism. *)
  unfold rel_iso. simpl.
  (* For SProp, all proofs are equal *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.lt_ge_cases := {}.
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_lt__ge__cases := {}.
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.lt_ge_cases Original_LF__DOT__IndProp_LF_IndProp_lt__ge__cases_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.lt_ge_cases Imported.Original_LF__DOT__IndProp_LF_IndProp_lt__ge__cases Original_LF__DOT__IndProp_LF_IndProp_lt__ge__cases_iso := {}.