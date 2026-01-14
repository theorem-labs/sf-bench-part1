From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_rev__append : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x := (@Imported.Original_LF__DOT__Logic_LF_Logic_rev__append).

(* Define the proof by explicit recursion - fix on x3 only *)
Fixpoint Original_LF__DOT__Logic_LF_Logic_rev__append_iso_aux
  (x1 x2 : Type) (hx : Iso x1 x2) 
  (x3 : Original.LF_DOT_Poly.LF.Poly.list x1)
  (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
  (H56 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6) {struct x3}
  : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) 
      (Original.LF_DOT_Logic.LF.Logic.rev_append x3 x5) 
      (imported_Original_LF__DOT__Logic_LF_Logic_rev__append (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3) x6) :=
  match x3 as x3' return
    rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) 
      (Original.LF_DOT_Logic.LF.Logic.rev_append x3' x5) 
      (imported_Original_LF__DOT__Logic_LF_Logic_rev__append (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3') x6)
  with
  | Original.LF_DOT_Poly.LF.Poly.nil => H56
  | Original.LF_DOT_Poly.LF.Poly.cons h3 t3 => 
      @Original_LF__DOT__Logic_LF_Logic_rev__append_iso_aux x1 x2 hx t3 
        (Original.LF_DOT_Poly.LF.Poly.cons h3 x5) 
        (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2 (to hx h3) x6)
        (f_equal2 (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2) IsomorphismDefinitions.eq_refl H56)
  end.

(* Now prove the actual isomorphism *)
Definition Original_LF__DOT__Logic_LF_Logic_rev__append_iso :
  forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4 ->
  forall (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6 ->
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Logic.LF.Logic.rev_append x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_rev__append x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso.
  apply (@eq_trans _ _ (imported_Original_LF__DOT__Logic_LF_Logic_rev__append (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3) x6) _).
  { exact (@Original_LF__DOT__Logic_LF_Logic_rev__append_iso_aux x1 x2 hx x3 x5 x6 H56). }
  { unfold imported_Original_LF__DOT__Logic_LF_Logic_rev__append.
    apply (@f_equal _ _ (fun l => Imported.Original_LF__DOT__Logic_LF_Logic_rev__append x2 l x6)).
    exact H34. }
Defined.
Instance: KnownConstant (@Original.LF_DOT_Logic.LF.Logic.rev_append) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Logic_LF_Logic_rev__append) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Logic.LF.Logic.rev_append) Original_LF__DOT__Logic_LF_Logic_rev__append_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Logic.LF.Logic.rev_append) (@Imported.Original_LF__DOT__Logic_LF_Logic_rev__append) Original_LF__DOT__Logic_LF_Logic_rev__append_iso := {}.