From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From Stdlib Require Import Logic.ProofIrrelevance.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Isomorphisms.U_original__U_false__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_In : forall x : Type, x -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> SProp := (@Imported.Original_LF__DOT__Logic_LF_Logic_In).

(* Helper *)
Lemma Imported_Eq_to_eq {A : Type} {x y : A} :
  Imported.Corelib_Init_Logic_eq A x y -> x = y.
Proof. intro H. destruct H. reflexivity. Qed.

Lemma iso_injective {A B : Type} (iso : Iso A B) (x y : A) :
  iso x = iso y -> x = y.
Proof.
  intro H.
  assert (from iso (iso x) = from iso (iso y)) as Hfrom by (f_equal; exact H).
  rewrite (eq_of_seq (from_to iso x)) in Hfrom.
  rewrite (eq_of_seq (from_to iso y)) in Hfrom.
  exact Hfrom.
Qed.

(* Forward direction *)
Fixpoint In_to (A B : Type) (iso_AB : Iso A B) (x : A) (l : Original.LF_DOT_Poly.LF.Poly.list A) {struct l}
  : Original.LF_DOT_Logic.LF.Logic.In x l -> imported_Original_LF__DOT__Logic_LF_Logic_In (iso_AB x) (Original_LF__DOT__Poly_LF_Poly_list_iso iso_AB l).
Proof.
  destruct l as [|h t].
  - simpl. intro H. destruct H.
  - simpl. intro H. destruct H as [Heq | Hin].
    + subst. apply Imported.or_inl. apply Imported.Corelib_Init_Logic_eq_refl.
    + apply Imported.or_inr. apply (In_to A B iso_AB x t). exact Hin.
Defined.

(* Backward direction to SInhabited *)
Fixpoint In_from_SI (A B : Type) (iso_AB : Iso A B) (x : A) (l : Original.LF_DOT_Poly.LF.Poly.list A) {struct l}
  : imported_Original_LF__DOT__Logic_LF_Logic_In (iso_AB x) (Original_LF__DOT__Poly_LF_Poly_list_iso iso_AB l) -> SInhabited (Original.LF_DOT_Logic.LF.Logic.In x l).
Proof.
  destruct l as [|h t].
  - simpl. intro H. destruct H.
  - simpl. intro H. destruct H as [Heq | Hin].
    + apply sinhabits. left. apply iso_injective with (iso := iso_AB). apply Imported_Eq_to_eq. exact Heq.
    + apply sinhabits. right. apply sinhabitant. apply (In_from_SI A B iso_AB x t). exact Hin.
Defined.

Definition In_from (A B : Type) (iso_AB : Iso A B) (x : A) (l : Original.LF_DOT_Poly.LF.Poly.list A)
  : imported_Original_LF__DOT__Logic_LF_Logic_In (iso_AB x) (Original_LF__DOT__Poly_LF_Poly_list_iso iso_AB l) ->
    Original.LF_DOT_Logic.LF.Logic.In x l :=
  fun H => sinhabitant (@In_from_SI A B iso_AB x l H).

(* General versions *)
Lemma In_to_general (A B : Type) (iso_AB : Iso A B) (x : A) (y : B) (Hxy : rel_iso iso_AB x y)
    (l1 : Original.LF_DOT_Poly.LF.Poly.list A)
    (l2 : imported_Original_LF__DOT__Poly_LF_Poly_list B)
    (Hl : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso iso_AB) l1 l2)
  : Original.LF_DOT_Logic.LF.Logic.In x l1 -> imported_Original_LF__DOT__Logic_LF_Logic_In y l2.
Proof.
  intro H.
  destruct Hxy as [Hxy']. destruct Hxy'.
  destruct Hl as [Hl']. destruct Hl'.
  apply In_to. exact H.
Defined.

Lemma In_from_general_SI (A B : Type) (iso_AB : Iso A B) (x : A) (y : B) (Hxy : rel_iso iso_AB x y)
    (l1 : Original.LF_DOT_Poly.LF.Poly.list A)
    (l2 : imported_Original_LF__DOT__Poly_LF_Poly_list B)
    (Hl : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso iso_AB) l1 l2)
  : imported_Original_LF__DOT__Logic_LF_Logic_In y l2 -> SInhabited (Original.LF_DOT_Logic.LF.Logic.In x l1).
Proof.
  intro H.
  destruct Hxy as [Hxy']. destruct Hxy'.
  destruct Hl as [Hl']. destruct Hl'.
  exact (@In_from_SI A B iso_AB x l1 H).
Defined.

Definition In_from_general (A B : Type) (iso_AB : Iso A B) (x : A) (y : B) (Hxy : rel_iso iso_AB x y)
    (l1 : Original.LF_DOT_Poly.LF.Poly.list A)
    (l2 : imported_Original_LF__DOT__Poly_LF_Poly_list B)
    (Hl : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso iso_AB) l1 l2)
  : imported_Original_LF__DOT__Logic_LF_Logic_In y l2 -> Original.LF_DOT_Logic.LF.Logic.In x l1 :=
  fun H => sinhabitant (@In_from_general_SI A B iso_AB x y Hxy l1 l2 Hl H).

(* Now the iso instance *)
Instance Original_LF__DOT__Logic_LF_Logic_In_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
     (_ : @rel_iso (Original.LF_DOT_Poly.LF.Poly.list x1) (imported_Original_LF__DOT__Poly_LF_Poly_list x2) (@Original_LF__DOT__Poly_LF_Poly_list_iso x1 x2 hx) x5 x6),
   Iso (@Original.LF_DOT_Logic.LF.Logic.In x1 x3 x5) (@imported_Original_LF__DOT__Logic_LF_Logic_In x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 Hx34 x5 x6 Hx56.
  unshelve eapply Build_Iso.
  - exact (@In_to_general x1 x2 hx x3 x4 Hx34 x5 x6 Hx56).
  - exact (@In_from_general x1 x2 hx x3 x4 Hx34 x5 x6 Hx56).
  - intro y. apply IsomorphismDefinitions.eq_refl.
  - intro y. apply seq_of_eq. apply proof_irrelevance.
Defined.
Instance: KnownConstant (@Original.LF_DOT_Logic.LF.Logic.In) := {}.
Instance: KnownConstant (@Imported.Original_LF__DOT__Logic_LF_Logic_In) := {}.
Instance: IsoStatementProofFor (@Original.LF_DOT_Logic.LF.Logic.In) Original_LF__DOT__Logic_LF_Logic_In_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Logic.LF.Logic.In) (@Imported.Original_LF__DOT__Logic_LF_Logic_In) Original_LF__DOT__Logic_LF_Logic_In_iso := {}.
