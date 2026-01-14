From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_app : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x := (@Imported.Original_LF__DOT__Poly_LF_Poly_app).

(* Helper lemma for the app nil case *)
Lemma imported_app_nil_eq : forall (X : Type) (l : Imported.Original_LF__DOT__Poly_LF_Poly_list X),
  IsomorphismDefinitions.eq (Imported.Original_LF__DOT__Poly_LF_Poly_app X (Imported.Original_LF__DOT__Poly_LF_Poly_list_nil X) l) l.
Proof.
  intros. apply IsomorphismDefinitions.eq_refl.
Defined.

(* Helper lemma for the app cons case *)
Lemma imported_app_cons_eq : forall (X : Type) (h : X) (t l : Imported.Original_LF__DOT__Poly_LF_Poly_list X),
  IsomorphismDefinitions.eq 
    (Imported.Original_LF__DOT__Poly_LF_Poly_app X (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons X h t) l)
    (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons X h (Imported.Original_LF__DOT__Poly_LF_Poly_app X t l)).
Proof.
  intros. apply IsomorphismDefinitions.eq_refl.
Defined.

(* First prove a lemma about the structure of app in both systems *)
Lemma app_iso_helper : forall (x1 x2 : Type) (hx : Iso x1 x2) 
  (l1 : Original.LF_DOT_Poly.LF.Poly.list x1) 
  (l2 : Original.LF_DOT_Poly.LF.Poly.list x1),
  IsomorphismDefinitions.eq 
    (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Poly.LF.Poly.app l1 l2))
    (Imported.Original_LF__DOT__Poly_LF_Poly_app x2 
      (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l1) 
      (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l2)).
Proof.
  intros x1 x2 hx l1.
  induction l1 as [|h t IH]; intro l2.
  - (* nil case: Original.app nil l2 = l2 and Imported.app nil (to l2) = to l2 *)
    simpl. apply IsomorphismDefinitions.eq_refl.
  - (* cons case *)
    simpl.
    (* Goal: cons (to h) (to (app t l2)) = Imported.app (cons (to h) (to t)) (to l2) *)
    (* We need to show the LHS equals RHS *)
    (* By imported_app_cons_eq: Imported.app (cons h' t') l' = cons h' (Imported.app t' l') *)
    eapply IsoEq.eq_trans.
    + apply IsoEq.f_equal2.
      * apply IsomorphismDefinitions.eq_refl.
      * apply IH.
    + apply IsoEq.eq_sym. apply imported_app_cons_eq.
Defined.

Instance Original_LF__DOT__Poly_LF_Poly_app_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4 ->
  forall (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6 ->
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Poly.LF.Poly.app x3 x5) (imported_Original_LF__DOT__Poly_LF_Poly_app x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unfold imported_Original_LF__DOT__Poly_LF_Poly_app.
  (* Goal: to (app x3 x5) = Imported.app x4 x6 *)
  (* We have H34: to x3 = x4 and H56: to x5 = x6 *)
  eapply IsoEq.eq_trans.
  - apply app_iso_helper.
  - apply IsoEq.f_equal2.
    + exact H34.
    + exact H56.
Defined.
Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.app) := {}.
Instance: KnownConstant (@Imported.Original_LF__DOT__Poly_LF_Poly_app) := {}.
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.app) Original_LF__DOT__Poly_LF_Poly_app_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.app) (@Imported.Original_LF__DOT__Poly_LF_Poly_app) Original_LF__DOT__Poly_LF_Poly_app_iso := {}.