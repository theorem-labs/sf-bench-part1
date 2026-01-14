From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_repeat''' : forall x : Type, x -> imported_nat -> imported_Original_LF__DOT__Poly_LF_Poly_list x := (@Imported.Original_LF__DOT__Poly_LF_Poly_repeat''').

(* Lemma: imported repeat''' has the expected computation rule at S *)
Lemma imported_repeat'''_compute_S : forall (X : Type) (x : X) (n : Imported.nat),
  IsomorphismDefinitions.eq 
    (Imported.Original_LF__DOT__Poly_LF_Poly_repeat''' X x (Imported.nat_S n))
    (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons X x (Imported.Original_LF__DOT__Poly_LF_Poly_repeat''' X x n)).
Proof.
  intros. apply IsomorphismDefinitions.eq_refl.
Qed.

(* Key lemma: repeat''' preserves isomorphism *)
Lemma repeat'''_iso_lemma : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 ->
  forall (n : Datatypes.nat),
  IsomorphismDefinitions.eq 
    (list_to_imported hx (Original.LF_DOT_Poly.LF.Poly.repeat''' x3 n))
    (Imported.Original_LF__DOT__Poly_LF_Poly_repeat''' x2 x4 (nat_to_imported n)).
Proof.
  intros x1 x2 hx x3 x4 Hx34 n.
  induction n as [|n' IH]; simpl.
  apply IsomorphismDefinitions.eq_refl.
  unfold rel_iso in Hx34.
  apply (@IsoEq.eq_trans (Imported.Original_LF__DOT__Poly_LF_Poly_list x2) _ 
    (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2 x4 (Imported.Original_LF__DOT__Poly_LF_Poly_repeat''' x2 x4 (nat_to_imported n'))) _).
  apply (IsoEq.f_equal2 (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2) Hx34 IH).
  apply IsoEq.eq_sym.
  apply imported_repeat'''_compute_S.
Qed.

Instance Original_LF__DOT__Poly_LF_Poly_repeat'''_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 ->
  forall (x5 : Datatypes.nat) (x6 : imported_nat),
  rel_iso nat_iso x5 x6 -> rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Poly.LF.Poly.repeat''' x3 x5) (imported_Original_LF__DOT__Poly_LF_Poly_repeat''' x4 x6).
Proof.
  intros x1 x2 hx x3 x4 Hx34 x5 x6 Hx56.
  unfold rel_iso in Hx56.
  unfold rel_iso. simpl.
  unfold imported_Original_LF__DOT__Poly_LF_Poly_repeat'''.
  apply (IsoEq.eq_trans (@repeat'''_iso_lemma x1 x2 hx x3 x4 Hx34 x5)).
  apply IsoEq.f_equal.
  exact Hx56.
Defined.

Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.repeat''') := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Poly_LF_Poly_repeat''') := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.repeat''') Original_LF__DOT__Poly_LF_Poly_repeat'''_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.repeat''') (@Imported.Original_LF__DOT__Poly_LF_Poly_repeat''') Original_LF__DOT__Poly_LF_Poly_repeat'''_iso := {}.