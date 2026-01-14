From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_app : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x :=
  @Imported.Original_LF__DOT__Poly_LF_Poly_app.

(* Helper: list isomorphism commutes with app *)
Lemma list_iso_app_commute : forall (x1 x2 : Type) (hx : Iso x1 x2)
  (l1 l2 : Original.LF_DOT_Poly.LF.Poly.list x1),
  to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Poly.LF.Poly.app l1 l2) =
  @Imported.Original_LF__DOT__Poly_LF_Poly_app x2
    (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l1)
    (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l2).
Proof.
  intros x1 x2 hx l1 l2.
  induction l1 as [|h t IH]; cbn; [ reflexivity | f_equal; exact IH ].
Qed.

(* Prove the app isomorphism *)
Instance Original_LF__DOT__Poly_LF_Poly_app_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4 ->
  forall (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6 ->
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Poly.LF.Poly.app x3 x5) (imported_Original_LF__DOT__Poly_LF_Poly_app x4 x6).
Proof.
  intros x1 x2 hx x3 x4 Hx34 x5 x6 Hx56.
  unfold rel_iso in *.
  rewrite <- (eq_of_seq Hx34).
  rewrite <- (eq_of_seq Hx56).
  (* Use seq_of_eq to convert standard eq to SProp eq *)
  apply seq_of_eq.
  exact (list_iso_app_commute hx x3 x5).
Defined.
Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.app) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Poly_LF_Poly_app) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.app) Original_LF__DOT__Poly_LF_Poly_app_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.app) (@Imported.Original_LF__DOT__Poly_LF_Poly_app) Original_LF__DOT__Poly_LF_Poly_app_iso := {}.
