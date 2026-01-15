From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_lt : imported_nat -> imported_nat -> SProp := Imported.Original_LF__DOT__IndProp_LF_IndProp_lt.

(* lt is defined as: lt n m = le (S n) m *)
(* We need to show that Original.lt x1 x3 is isomorphic to Imported.lt x2 x4 *)
(* Since Original.lt x1 x3 = Original.le (S x1) x3 *)
(* and Imported.lt x2 x4 = Imported.le (S x2) x4 *)
(* We can use the le isomorphism *)

Instance Original_LF__DOT__IndProp_LF_IndProp_lt_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.lt x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_lt x2 x4).
Proof.
  intros x1 x2 Hx1x2 x3 x4 Hx3x4.
  unfold Original.LF_DOT_IndProp.LF.IndProp.lt.
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_lt.
  unfold Imported.Original_LF__DOT__IndProp_LF_IndProp_lt.
  simpl in *.
  (* Use the le isomorphism with (S x1, nat_S x2) and (x3, x4) *)
  destruct Hx1x2 as [Hx1x2]. destruct Hx3x4 as [Hx3x4].
  apply Original_LF__DOT__IndProp_LF_IndProp_le_iso.
  - constructor. simpl. exact (f_equal Imported.nat_S Hx1x2).
  - constructor. exact Hx3x4.
Defined.

Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.lt := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_lt := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.lt Original_LF__DOT__IndProp_LF_IndProp_lt_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.lt Imported.Original_LF__DOT__IndProp_LF_IndProp_lt Original_LF__DOT__IndProp_LF_IndProp_lt_iso := {}.
