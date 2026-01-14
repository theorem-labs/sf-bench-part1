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

(* Helper lemmas for map computation *)
Lemma imported_map_nil : forall (x2 x4 : Type) (x6 : x2 -> x4),
  imported_Original_LF__DOT__Poly_LF_Poly_map x6 (Imported.Original_LF__DOT__Poly_LF_Poly_list_nil x2) = 
  Imported.Original_LF__DOT__Poly_LF_Poly_list_nil x4.
Proof. reflexivity. Qed.

Lemma imported_map_cons : forall (x2 x4 : Type) (x6 : x2 -> x4) h t,
  imported_Original_LF__DOT__Poly_LF_Poly_map x6 (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2 h t) = 
  Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x4 (x6 h) (imported_Original_LF__DOT__Poly_LF_Poly_map x6 t).
Proof. reflexivity. Qed.

(* Prove map preserves the isomorphism relation *)
Instance Original_LF__DOT__Poly_LF_Poly_map_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 x4 : Type) (hx0 : Iso x3 x4) (x5 : x1 -> x3) (x6 : x2 -> x4),
  (forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> rel_iso hx0 (x5 x7) (x6 x8)) ->
  forall (x7 : Original.LF_DOT_Poly.LF.Poly.list x1) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x7 x8 ->
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx0) (Original.LF_DOT_Poly.LF.Poly.map x5 x7) (imported_Original_LF__DOT__Poly_LF_Poly_map x6 x8).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 Hf x7.
  induction x7 as [|h t IH]; intros x8 Hx8.
  - (* nil case *)
    unfold rel_iso in *. simpl in *.
    destruct Hx8. 
    rewrite imported_map_nil.
    apply IsomorphismDefinitions.eq_refl.
  - (* cons case *)
    unfold rel_iso in Hx8. simpl in Hx8.
    destruct Hx8.
    unfold rel_iso. simpl.
    rewrite imported_map_cons.
    apply (f_equal2 (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x4)).
    + (* to hx0 (x5 h) = x6 (to hx h) *)
      apply (Hf h (to hx h) IsomorphismDefinitions.eq_refl).
    + (* to list_iso (map x5 t) = imported_map x6 (to list_iso t) *)
      apply (IH (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) t) IsomorphismDefinitions.eq_refl).
Defined.
Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.map) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Poly_LF_Poly_map) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.map) Original_LF__DOT__Poly_LF_Poly_map_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.map) (@Imported.Original_LF__DOT__Poly_LF_Poly_map) Original_LF__DOT__Poly_LF_Poly_map_iso := {}.