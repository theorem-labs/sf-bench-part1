From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
#[local] Set Printing Coercions.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.nat__iso.

Monomorphic Definition imported_Original_LF__DOT__Poly_LF_Poly_repeat''' : forall x : Type, x -> imported_nat -> imported_Original_LF__DOT__Poly_LF_Poly_list x := (@Imported.Original_LF__DOT__Poly_LF_Poly_repeat''').

(* Helper lemma: prove the isomorphism for a fixed nat, using nat_to_imported *)
Lemma repeat'''_iso_helper : forall (X1 X2 : Type) (hx : Iso X1 X2) (x1 : X1) (x2 : X2),
  rel_iso hx x1 x2 ->
  forall n : nat,
    rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx)
      (Original.LF_DOT_Poly.LF.Poly.repeat''' x1 n)
      (imported_Original_LF__DOT__Poly_LF_Poly_repeat''' x2 (nat_to_imported n)).
Proof.
  intros X1 X2 hx x1 x2 Hx12.
  fix IH 1.
  intro n.
  destruct n as [|n'].
  - (* n = 0 *)
    simpl. 
    apply Original_LF__DOT__Poly_LF_Poly_nil_iso.
  - (* n = S n' *)
    simpl.
    apply Original_LF__DOT__Poly_LF_Poly_cons_iso.
    + exact Hx12.
    + apply IH.
Qed.

Monomorphic Instance Original_LF__DOT__Poly_LF_Poly_repeat'''_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 ->
  forall (x5 : nat) (x6 : imported_nat),
  rel_iso nat_iso x5 x6 -> rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Poly.LF.Poly.repeat''' x3 x5) (imported_Original_LF__DOT__Poly_LF_Poly_repeat''' x4 x6).
Proof.
  intros X1 X2 hx x1 x2 Hx12 n m Hnm.
  destruct Hnm as [Hnm].
  rewrite <- (eq_of_seq Hnm).
  apply repeat'''_iso_helper.
  exact Hx12.
Defined.

Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.repeat''') := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Poly_LF_Poly_repeat''') := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.repeat''') Original_LF__DOT__Poly_LF_Poly_repeat'''_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.repeat''') (@Imported.Original_LF__DOT__Poly_LF_Poly_repeat''') Original_LF__DOT__Poly_LF_Poly_repeat'''_iso := {}.
