From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Monomorphic Definition imported_Original_LF__DOT__Logic_LF_Logic_rev__append : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x := (@Imported.Original_LF__DOT__Logic_LF_Logic_rev__append).

(* Helper: to commutes with rev_append *)
Lemma list_to_rev_append_compat : forall (X1 X2 : Type) (hx : Iso X1 X2)
  (l1 l2 : Original.LF_DOT_Poly.LF.Poly.list X1),
  IsomorphismDefinitions.eq
    (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Logic.LF.Logic.rev_append l1 l2))
    (Imported.Original_LF__DOT__Logic_LF_Logic_rev__append X2 
       (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l1) 
       (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l2)).
Proof.
  intros X1 X2 hx l1.
  induction l1 as [|x xs IH]; intro l2; simpl.
  - apply IsomorphismDefinitions.eq_refl.
  - apply IH.
Qed.

Monomorphic Instance Original_LF__DOT__Logic_LF_Logic_rev__append_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4 ->
  forall (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6 ->
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Logic.LF.Logic.rev_append x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_rev__append x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  constructor. simpl.
  pose proof (proj_rel_iso H34) as Heq34. simpl in Heq34.
  pose proof (proj_rel_iso H56) as Heq56. simpl in Heq56.
  unfold imported_Original_LF__DOT__Logic_LF_Logic_rev__append.
  eapply eq_trans.
  - apply list_to_rev_append_compat.
  - apply f_equal2; assumption.
Defined.
Instance: KnownConstant (@Original.LF_DOT_Logic.LF.Logic.rev_append) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Logic_LF_Logic_rev__append) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Logic.LF.Logic.rev_append) Original_LF__DOT__Logic_LF_Logic_rev__append_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Logic.LF.Logic.rev_append) (@Imported.Original_LF__DOT__Logic_LF_Logic_rev__append) Original_LF__DOT__Logic_LF_Logic_rev__append_iso := {}.