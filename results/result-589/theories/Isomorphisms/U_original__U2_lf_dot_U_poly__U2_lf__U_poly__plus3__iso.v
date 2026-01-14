From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__plus__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_plus3 : imported_nat -> imported_nat := Imported.Original_LF__DOT__Poly_LF_Poly_plus3.

(* plus3 = plus 3 in both implementations *)
Instance Original_LF__DOT__Poly_LF_Poly_plus3_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> rel_iso nat_iso (Original.LF_DOT_Poly.LF.Poly.plus3 x1) (imported_Original_LF__DOT__Poly_LF_Poly_plus3 x2).
Proof.
  intros x1 x2 H12.
  unfold Original.LF_DOT_Poly.LF.Poly.plus3.
  unfold imported_Original_LF__DOT__Poly_LF_Poly_plus3.
  unfold Imported.Original_LF__DOT__Poly_LF_Poly_plus3.
  (* Both are plus 3 applied to x *)
  apply Original_LF__DOT__Basics_LF_Basics_plus_iso.
  - (* 3 corresponds to 3 *)
    unfold rel_iso. simpl.
    apply IsomorphismDefinitions.eq_refl.
  - exact H12.
Defined.

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.plus3 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_plus3 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.plus3 Original_LF__DOT__Poly_LF_Poly_plus3_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.plus3 Imported.Original_LF__DOT__Poly_LF_Poly_plus3 Original_LF__DOT__Poly_LF_Poly_plus3_iso := {}.