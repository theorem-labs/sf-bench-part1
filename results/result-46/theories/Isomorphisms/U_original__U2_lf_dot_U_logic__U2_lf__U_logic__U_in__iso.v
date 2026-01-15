From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From Stdlib Require Import Logic.ProofIrrelevance.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Isomorphisms.U_original__U_false__iso.

Monomorphic Definition imported_Original_LF__DOT__Logic_LF_Logic_In : forall x : Type, x -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> SProp := (@Imported.Original_LF__DOT__Logic_LF_Logic_In).

(* Reduction lemmas for Imported.In *)
Lemma imported_In_nil : forall A (a : A), 
  Imported.Original_LF__DOT__Logic_LF_Logic_In A a (Imported.Original_LF__DOT__Poly_LF_Poly_list_nil A) = Imported.MyFalse.
Proof. intros. reflexivity. Qed.

Lemma imported_In_cons : forall A (a : A) (x : A) (l : Imported.Original_LF__DOT__Poly_LF_Poly_list A), 
  Imported.Original_LF__DOT__Logic_LF_Logic_In A a (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons A x l) = 
  Imported.or (Imported.Corelib_Init_Logic_eq A x a) (Imported.Original_LF__DOT__Logic_LF_Logic_In A a l).
Proof. intros. reflexivity. Qed.

(* Helper lemma for the equality part - works in SInhabited context *)
(* Returns SInhabited (h = from iso_AB y) *)
Definition eq_from_imported_eq_SI_aux {A B : Type} (iso_AB : Iso A B) (h : A) (y : B)
  (Heq : Imported.Corelib_Init_Logic_eq B (to iso_AB h) y) : SInhabited (@Logic.eq A h (from iso_AB y)).
Proof.
  (* Use the eliminator to extract from SProp into SProp *)
  refine (Imported.Corelib_Init_Logic_eq_indl B (to iso_AB h) 
    (fun b _ => SInhabited (@Logic.eq A h (from iso_AB b))) 
    _ y Heq).
  apply sinhabits.
  (* Need: h = from iso_AB (to iso_AB h) *)
  (* from_to gives: from iso_AB (to iso_AB h) = h *)
  apply Logic.eq_sym.
  exact (eq_of_seq (from_to iso_AB h)).
Defined.

Definition eq_from_imported_eq {A B : Type} (iso_AB : Iso A B) (h x : A) (y : B)
  (Heq : Imported.Corelib_Init_Logic_eq B (to iso_AB h) y) (Hxy : to iso_AB x = y) : @Logic.eq A h x.
Proof.
  apply sinhabitant.
  (* eq_from_imported_eq_SI_aux gives us SInhabited (h = from iso_AB y) *)
  pose proof (@eq_from_imported_eq_SI_aux A B iso_AB h y Heq) as H.
  destruct H as [H].
  apply sinhabits.
  transitivity (from iso_AB y).
  - exact H.
  - (* from iso_AB y = x *)
    transitivity (from iso_AB (to iso_AB x)).
    + f_equal. symmetry. exact Hxy.
    + exact (eq_of_seq (from_to iso_AB x)).
Defined.

(* Backward: Imported.In -> SInhabited Original.In *)
Fixpoint In_from_SInhabited {A B : Type} (iso_AB : Iso A B)
         (x : A) (y : B) (Hxy : rel_iso iso_AB x y)
         (l1 : Original.LF_DOT_Poly.LF.Poly.list A) 
         (l2 : imported_Original_LF__DOT__Poly_LF_Poly_list B)
         (Hl : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso iso_AB) l1 l2)
  : imported_Original_LF__DOT__Logic_LF_Logic_In y l2 -> SInhabited (Original.LF_DOT_Logic.LF.Logic.In x l1).
Proof.
  destruct l1 as [|h1 t1].
  - (* nil case *)
    intro H.
    destruct Hl as [Hl]. simpl in Hl. apply eq_of_seq in Hl. subst l2.
    unfold imported_Original_LF__DOT__Logic_LF_Logic_In in H. rewrite imported_In_nil in H.
    destruct H.
  - (* cons case *)
    intro Hin.
    destruct Hl as [Hl]. simpl in Hl. apply eq_of_seq in Hl. subst l2.
    unfold imported_Original_LF__DOT__Logic_LF_Logic_In in Hin. rewrite imported_In_cons in Hin.
    (* Get the equality from Hxy for later use *)
    pose proof Hxy as Hxy_copy.
    destruct Hxy as [Hxy']. simpl in Hxy'. apply eq_of_seq in Hxy'.
    (* Hxy' : to iso_AB x = y *)
    apply (Imported.or_indl _ _ (fun _ => SInhabited (h1 = x \/ Original.LF_DOT_Logic.LF.Logic.In x t1))) in Hin.
    + exact Hin.
    + (* Left case: iso_AB h1 = y *) 
      intro Heq.
      apply sinhabits. left.
      exact (@eq_from_imported_eq A B iso_AB h1 x y Heq Hxy').
    + (* Right case: In y t2' *) 
      intro Hin'.
      apply sinhabits. right.
      apply sinhabitant.
      refine (In_from_SInhabited A B iso_AB x y Hxy_copy t1 _ _ Hin').
      constructor. apply IsomorphismDefinitions.eq_refl.
Defined.

(* Forward: Original.In -> Imported.In *)
Definition In_to {A B : Type} (iso_AB : Iso A B)
         (x : A) (y : B) (Hxy : rel_iso iso_AB x y)
         (l1 : Original.LF_DOT_Poly.LF.Poly.list A) 
         (l2 : imported_Original_LF__DOT__Poly_LF_Poly_list B)
         (Hl : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso iso_AB) l1 l2)
  : Original.LF_DOT_Logic.LF.Logic.In x l1 -> imported_Original_LF__DOT__Logic_LF_Logic_In y l2.
Proof.
  revert l2 Hl.
  induction l1 as [|h1 t1 IH]; intros l2 Hl H.
  - simpl in H. destruct H.
  - simpl in H.
    destruct Hl as [Hl]. simpl in Hl. apply eq_of_seq in Hl. subst l2.
    unfold imported_Original_LF__DOT__Logic_LF_Logic_In. rewrite imported_In_cons.
    destruct H as [H | H].
    + apply Imported.or_inl.
      subst x.
      destruct Hxy as [Hxy']. simpl in Hxy'. apply eq_of_seq in Hxy'.
      rewrite Hxy'. apply Imported.Corelib_Init_Logic_eq_refl.
    + apply Imported.or_inr.
      apply IH.
      * constructor. apply IsomorphismDefinitions.eq_refl.
      * exact H.
Defined.

Definition In_from {A B : Type} (iso_AB : Iso A B)
         (x : A) (y : B) (Hxy : rel_iso iso_AB x y)
         (l1 : Original.LF_DOT_Poly.LF.Poly.list A) 
         (l2 : imported_Original_LF__DOT__Poly_LF_Poly_list B)
         (Hl : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso iso_AB) l1 l2)
  : imported_Original_LF__DOT__Logic_LF_Logic_In y l2 -> Original.LF_DOT_Logic.LF.Logic.In x l1 :=
  fun H => sinhabitant (@In_from_SInhabited A B iso_AB x y Hxy l1 l2 Hl H).

Monomorphic Instance Original_LF__DOT__Logic_LF_Logic_In_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 ->
  forall (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6 -> Iso (Original.LF_DOT_Logic.LF.Logic.In x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_In x4 x6).
Proof.
  intros x1 x2 hx x3 x4 Hx34 x5 x6 Hx56.
  unshelve eapply Build_Iso.
  - exact (@In_to x1 x2 hx x3 x4 Hx34 x5 x6 Hx56).
  - exact (@In_from x1 x2 hx x3 x4 Hx34 x5 x6 Hx56).
  - (* to_from: for SProp, trivial *)
    intro y. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: for Prop, use proof_irrelevance *)
    intro y. apply seq_of_eq. apply proof_irrelevance.
Defined.
Instance: KnownConstant (@Original.LF_DOT_Logic.LF.Logic.In) := {}. 
Instance: KnownConstant (@Imported.Original_LF__DOT__Logic_LF_Logic_In) := {}. 
Instance: IsoStatementProofFor (@Original.LF_DOT_Logic.LF.Logic.In) Original_LF__DOT__Logic_LF_Logic_In_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Logic.LF.Logic.In) (@Imported.Original_LF__DOT__Logic_LF_Logic_In) Original_LF__DOT__Logic_LF_Logic_In_iso := {}.
