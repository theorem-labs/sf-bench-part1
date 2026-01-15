From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From Stdlib Require Import Logic.ProofIrrelevance.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Isomorphisms.U_original__U_false__iso Isomorphisms.or__iso Isomorphisms.U_corelib__U_init__U_logic__eq__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_In : forall x : Type, x -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> SProp := (@Imported.Original_LF__DOT__Logic_LF_Logic_In).

(* Helper function: to direction *)
Section In_to_section.
Variables (x1 x2 : Type) (hx : Iso x1 x2).

Fixpoint In_to_helper (x3 : x1) (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) {struct x5}
  : Original.LF_DOT_Logic.LF.Logic.In x3 x5 -> 
    Imported.Original_LF__DOT__Logic_LF_Logic_In x2 (hx x3) (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5).
Proof.
  destruct x5 as [|h t].
  - (* nil case *)
    simpl. intro H. destruct H.
  - (* cons case *)
    simpl. intro H. destruct H as [Heq | Hin].
    + (* h = x3 *)
      apply Imported.or_inl. subst x3. apply Imported.Corelib_Init_Logic_eq_refl.
    + (* In x3 t *)
      apply Imported.or_inr. apply In_to_helper. exact Hin.
Defined.
End In_to_section.

(* Helper function: from direction - builds SInhabited *)
Section In_from_section.
Variables (x1 x2 : Type) (hx : Iso x1 x2).

(* Helper to convert from Imported.Eq injectivity *)
Definition iso_injective (a b : x1) (H : Imported.Corelib_Init_Logic_eq x2 (hx a) (hx b)) : IsomorphismDefinitions.eq a b.
Proof.
  pose proof (from_to hx a) as Ha.
  pose proof (from_to hx b) as Hb.
  destruct H.
  apply (IsoEq.eq_trans (IsoEq.eq_sym Ha)).
  exact Hb.
Defined.

Fixpoint In_from_helper (a : x1) (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) {struct x5}
  : Imported.Original_LF__DOT__Logic_LF_Logic_In x2 (hx a) (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5) ->
    SInhabited (Original.LF_DOT_Logic.LF.Logic.In a x5).
Proof.
  destruct x5 as [|h t].
  - (* nil case *)
    simpl. intro Hin. destruct Hin.
  - (* cons case *)
    simpl. intro Hin.
    apply (Imported.or_indl _ _ (fun _ => SInhabited (h = a \/ Original.LF_DOT_Logic.LF.Logic.In a t))) in Hin.
    + exact Hin.
    + (* hx h = hx a -> SInhabited (h = a \/ In a t) *)
      intro Heq.
      apply sinhabits. left.
      (* from injectivity: hx h = hx a => h = a *)
      apply eq_of_seq.
      apply iso_injective.
      exact Heq.
    + (* Imported.In (hx a) (to t) -> SInhabited (h = a \/ In a t) *)
      intro Hin'.
      apply sinhabits. right.
      apply sinhabitant.
      apply (In_from_helper a t).
      exact Hin'.
Defined.
End In_from_section.

(* Main isomorphism *)
Instance Original_LF__DOT__Logic_LF_Logic_In_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
     (_ : @rel_iso (Original.LF_DOT_Poly.LF.Poly.list x1) (imported_Original_LF__DOT__Poly_LF_Poly_list x2) (@Original_LF__DOT__Poly_LF_Poly_list_iso x1 x2 hx) x5 x6),
   Iso (@Original.LF_DOT_Logic.LF.Logic.In x1 x3 x5) (@imported_Original_LF__DOT__Logic_LF_Logic_In x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 Hx34 x5 x6 Hx56.
  pose proof (proj_rel_iso Hx34) as Heq34. simpl in Heq34.
  pose proof (proj_rel_iso Hx56) as Heq56. simpl in Heq56.
  unshelve eapply Build_Iso.
  - (* to: Original.In x3 x5 -> Imported.In x4 x6 *)
    intro H.
    unfold imported_Original_LF__DOT__Logic_LF_Logic_In.
    rewrite <- (eq_of_seq Heq34).
    rewrite <- (eq_of_seq Heq56).
    apply (In_to_helper hx x3 x5). exact H.
  - (* from: Imported.In x4 x6 -> Original.In x3 x5 *)
    intro H.
    apply sinhabitant.
    unfold imported_Original_LF__DOT__Logic_LF_Logic_In in H.
    rewrite <- (eq_of_seq Heq34) in H.
    rewrite <- (eq_of_seq Heq56) in H.
    apply (In_from_helper hx x3 x5). exact H.
  - (* to_from: for SProp, trivial *)
    intro y. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: for Prop, use proof_irrelevance *)
    intro y. apply seq_of_eq. apply proof_irrelevance.
Defined.

Instance: KnownConstant (@Original.LF_DOT_Logic.LF.Logic.In) := {}.
Instance: KnownConstant (@Imported.Original_LF__DOT__Logic_LF_Logic_In) := {}.
Instance: IsoStatementProofFor (@Original.LF_DOT_Logic.LF.Logic.In) Original_LF__DOT__Logic_LF_Logic_In_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Logic.LF.Logic.In) (@Imported.Original_LF__DOT__Logic_LF_Logic_In) Original_LF__DOT__Logic_LF_Logic_In_iso := {}.
