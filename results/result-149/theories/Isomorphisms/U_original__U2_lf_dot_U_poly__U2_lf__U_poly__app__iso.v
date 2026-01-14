From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_app : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x := Imported.Original_LF__DOT__Poly_LF_Poly_app.
(* Helper lemma: the to function commutes with app *)
Lemma to_app_commutes : forall (x1 x2 : Type) (hx : Iso x1 x2) 
  (l1 l2 : Original.LF_DOT_Poly.LF.Poly.list x1),
  IsomorphismDefinitions.eq 
    (@to _ _ (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Poly.LF.Poly.app l1 l2))
    (Imported.Original_LF__DOT__Poly_LF_Poly_app x2 
       (@to _ _ (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l1)
       (@to _ _ (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l2)).
Proof.
  intros x1 x2 hx l1 l2.
  induction l1 as [|h1 t1 IH].
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl. 
    apply (IsoEq.f_equal2 (@imported_Original_LF__DOT__Poly_LF_Poly_list_cons x2)).
    + apply IsomorphismDefinitions.eq_refl.
    + exact IH.
Defined.

Definition Original_LF__DOT__Poly_LF_Poly_app_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4 ->
  forall (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6 ->
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Poly.LF.Poly.app x3 x5) (imported_Original_LF__DOT__Poly_LF_Poly_app x4 x6).
Proof.
  intros x1 x2 hx x3 x4 Hx3 x5 x6 Hx5.
  unfold rel_iso in *.
  simpl in *.
  unfold imported_Original_LF__DOT__Poly_LF_Poly_app.
  (* to (app x3 x5) = Imported.app (to x3) (to x5) = Imported.app x4 x6 *)
  (* We use the commutation lemma and then rewrite with Hx3, Hx5 *)
  pose proof (@to_app_commutes x1 x2 hx x3 x5) as Hcomm.
  (* Hcomm : to (app x3 x5) = Imported.app (to x3) (to x5) *)
  (* Hx3 : to x3 = x4 *)
  (* Hx5 : to x5 = x6 *)
  (* Goal : to (app x3 x5) = Imported.app x4 x6 *)
  apply (@IsoEq.eq_trans _ _ _ _ Hcomm).
  apply (IsoEq.f_equal2 (Imported.Original_LF__DOT__Poly_LF_Poly_app x2) Hx3 Hx5).
Defined.
Existing Instance Original_LF__DOT__Poly_LF_Poly_app_iso.
Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.app) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant imported_Original_LF__DOT__Poly_LF_Poly_app := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.app) Original_LF__DOT__Poly_LF_Poly_app_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.app) imported_Original_LF__DOT__Poly_LF_Poly_app Original_LF__DOT__Poly_LF_Poly_app_iso := {}.