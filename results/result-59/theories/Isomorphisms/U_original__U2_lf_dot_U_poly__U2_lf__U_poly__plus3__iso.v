From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__plus__iso.

Monomorphic Definition imported_Original_LF__DOT__Poly_LF_Poly_plus3 : imported_nat -> imported_nat := Imported.Original_LF__DOT__Poly_LF_Poly_plus3.

Lemma plus3_commutes : forall n : nat,
  IsomorphismDefinitions.eq 
    (nat_to_imported (Original.LF_DOT_Poly.LF.Poly.plus3 n))
    (imported_Original_LF__DOT__Poly_LF_Poly_plus3 (nat_to_imported n)).
Proof.
  intro n.
  unfold Original.LF_DOT_Poly.LF.Poly.plus3.
  unfold imported_Original_LF__DOT__Poly_LF_Poly_plus3.
  simpl. apply IsomorphismDefinitions.eq_refl.
Qed.

Monomorphic Instance Original_LF__DOT__Poly_LF_Poly_plus3_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> rel_iso nat_iso (Original.LF_DOT_Poly.LF.Poly.plus3 x1) (imported_Original_LF__DOT__Poly_LF_Poly_plus3 x2).
Proof.
  intros x1 x2 H.
  destruct H as [H].
  constructor.
  pose proof (plus3_commutes x1) as Hpc.
  unfold imported_Original_LF__DOT__Poly_LF_Poly_plus3 in *.
  eapply eq_trans.
  - exact Hpc.
  - apply f_equal. exact H.
Defined.
Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.plus3 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_plus3 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.plus3 Original_LF__DOT__Poly_LF_Poly_plus3_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.plus3 Imported.Original_LF__DOT__Poly_LF_Poly_plus3 Original_LF__DOT__Poly_LF_Poly_plus3_iso := {}.