From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_map : forall x x0 : Type, (x -> x0) -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x0 := (@Imported.Original_LF__DOT__Poly_LF_Poly_map).

(* Imported map has the expected behavior *)
Lemma imported_map_nil : forall X Y (f : X -> Y), 
  Imported.Original_LF__DOT__Poly_LF_Poly_map X Y f (Imported.Original_LF__DOT__Poly_LF_Poly_list_nil X) = Imported.Original_LF__DOT__Poly_LF_Poly_list_nil Y.
Proof. intros. reflexivity. Qed.

Lemma imported_map_cons : forall X Y (f : X -> Y) h t, 
  Imported.Original_LF__DOT__Poly_LF_Poly_map X Y f (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons X h t) = 
  Imported.Original_LF__DOT__Poly_LF_Poly_list_cons Y (f h) (Imported.Original_LF__DOT__Poly_LF_Poly_map X Y f t).
Proof. intros. reflexivity. Qed.

(* Helper lemma: the to function preserves map *)
Lemma list_to_map_compat : forall (x1 x2 : Type) (hx : Iso x1 x2)
  (x3 x4 : Type) (hx0 : Iso x3 x4) (f1 : x1 -> x3) (f2 : x2 -> x4)
  (Hf : forall a : x1, IsomorphismDefinitions.eq (to hx0 (f1 a)) (f2 (to hx a)))
  (l : Original.LF_DOT_Poly.LF.Poly.list x1),
  IsomorphismDefinitions.eq
    (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx0) (Original.LF_DOT_Poly.LF.Poly.map f1 l))
    (Imported.Original_LF__DOT__Poly_LF_Poly_map x2 x4 f2 (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l)).
Proof.
  intros x1 x2 hx x3 x4 hx0 f1 f2 Hf l.
  induction l as [|h t IH].
  - (* nil case *)
    simpl. apply IsomorphismDefinitions.eq_refl.
  - (* cons case *)
    simpl.
    (* LHS: Imported.cons (to hx0 (f1 h)) (to list_iso (map f1 t)) *)
    (* RHS: Imported.map f2 (Imported.cons (to hx h) (to list_iso t)) *)
    (*    = Imported.cons (f2 (to hx h)) (Imported.map f2 (to list_iso t)) by imported_map_cons *)
    eapply eq_sym.
    eapply eq_trans.
    { apply seq_of_eq. apply imported_map_cons. }
    (* Now RHS is Imported.cons (f2 (to hx h)) (Imported.map f2 (to list_iso t)) *)
    apply eq_sym.
    apply f_equal2.
    + (* to hx0 (f1 h) = f2 (to hx h) *)
      apply Hf.
    + (* to list_iso (map f1 t) = Imported.map f2 (to list_iso t) by IH *)
      exact IH.
Qed.

Instance Original_LF__DOT__Poly_LF_Poly_map_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 x4 : Type) (hx0 : Iso x3 x4) (x5 : x1 -> x3) (x6 : x2 -> x4),
  (forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> rel_iso hx0 (x5 x7) (x6 x8)) ->
  forall (x7 : Original.LF_DOT_Poly.LF.Poly.list x1) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x7 x8 ->
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx0) (Original.LF_DOT_Poly.LF.Poly.map x5 x7) (imported_Original_LF__DOT__Poly_LF_Poly_map x6 x8).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 Hf x7 x8 H78.
  unfold rel_iso in *. simpl in *.
  unfold imported_Original_LF__DOT__Poly_LF_Poly_map.
  eapply eq_trans.
  - apply list_to_map_compat.
    intro a. apply Hf. apply IsomorphismDefinitions.eq_refl.
  - apply f_equal. exact H78.
Defined.
Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.map) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Poly_LF_Poly_map) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.map) Original_LF__DOT__Poly_LF_Poly_map_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.map) (@Imported.Original_LF__DOT__Poly_LF_Poly_map) Original_LF__DOT__Poly_LF_Poly_map_iso := {}.