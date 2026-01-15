From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From Stdlib Require Import Logic.ProofIrrelevance.
Import IsoEq.

#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Local Open Scope nat_scope.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Isomorphisms.U_original__U_false__iso Isomorphisms.or__iso Isomorphisms.U_corelib__U_init__U_logic__eq__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_In : forall x : Type, x -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> SProp := (@Imported.Original_LF__DOT__Logic_LF_Logic_In).

(* Helper to convert between Original and Imported In definitions *)
(* Original.In is defined as:
   - In x [] = False
   - In x (h :: t) = (h = x) \/ In x t
   Imported.In has the same structure but with SProp or/eq
*)

(* Forward: Original.In -> Imported.In *)
Definition In_to {A B : Type} (iso_AB : Iso A B) (x : A) (y : B) (Hxy : rel_iso iso_AB x y)
  : forall (l1 : Original.LF_DOT_Poly.LF.Poly.list A),
    Original.LF_DOT_Logic.LF.Logic.In x l1 -> 
    imported_Original_LF__DOT__Logic_LF_Logic_In y (to (Original_LF__DOT__Poly_LF_Poly_list_iso iso_AB) l1).
Proof.
  induction l1 as [|h1 t1 IH]; intro H.
  - simpl in H. destruct H.
  - simpl in H. simpl.
    destruct H as [Heq | Hin].
    + apply Imported.or_inl.
      subst h1.
      pose proof (proj_rel_iso Hxy) as Hxy'.
      destruct Hxy'. apply Imported.Corelib_Init_Logic_eq_refl.
    + apply Imported.or_inr.
      exact (IH Hin).
Defined.

(* Backward helper: Imported.In -> SInhabited (Original.In) *)
Definition In_from_SInhabited {A B : Type} (iso_AB : Iso A B) (x : A) (y : B) (Hxy : rel_iso iso_AB x y)
  : forall (l1 : Original.LF_DOT_Poly.LF.Poly.list A),
    imported_Original_LF__DOT__Logic_LF_Logic_In y (to (Original_LF__DOT__Poly_LF_Poly_list_iso iso_AB) l1) ->
    SInhabited (Original.LF_DOT_Logic.LF.Logic.In x l1).
Proof.
  induction l1 as [|h1 t1 IH]; intro H.
  - simpl in H. exact (Imported.MyFalse_indl (fun _ => SInhabited _) H).
  - simpl in H.
    destruct H as [Heq | Hin].
    + (* Heq : Corelib_Init_Logic_eq B (to iso_AB h1) y *)
      (* We need: SInhabited (h1 = x \/ In x t1) *)
      (* Strategy: Use Hxy (which says to x = y) and Heq (which says to h1 = y)
         to derive h1 = x *)
      pose proof (proj_rel_iso Hxy) as Hxy'.
      (* Hxy' : to x = y *)
      (* Heq : to h1 = y (in SProp) *)
      (* First eliminate Heq to transform y -> to h1 in all hypotheses *)
      refine (Imported.Corelib_Init_Logic_eq_indl B (to iso_AB h1) 
               (fun y' _ => IsomorphismDefinitions.eq (to iso_AB x) y' -> 
                           SInhabited (h1 = x \/ Original.LF_DOT_Logic.LF.Logic.In x t1)) 
               _ y Heq Hxy').
      (* Now we need: to x = to h1 -> SInhabited (h1 = x \/ ...) *)
      intro HH.
      apply sinhabits. left.
      (* HH : to x = to h1 *)
      transitivity (from iso_AB (to iso_AB h1)).
      { symmetry. apply (eq_of_seq (from_to iso_AB h1)). }
      transitivity (from iso_AB (to iso_AB x)).
      2: { apply (eq_of_seq (from_to iso_AB x)). }
      f_equal. symmetry. destruct HH. reflexivity.
    + apply sinhabits. right.
      exact (sinhabitant (IH Hin)).
Defined.

Definition In_from {A B : Type} (iso_AB : Iso A B) (x : A) (y : B) (Hxy : rel_iso iso_AB x y)
         (l1 : Original.LF_DOT_Poly.LF.Poly.list A)
  : imported_Original_LF__DOT__Logic_LF_Logic_In y (to (Original_LF__DOT__Poly_LF_Poly_list_iso iso_AB) l1) ->
    Original.LF_DOT_Logic.LF.Logic.In x l1 :=
  fun H => sinhabitant (@In_from_SInhabited A B iso_AB x y Hxy l1 H).

(* Main iso instance - note we use the canonical form *)
Instance Original_LF__DOT__Logic_LF_Logic_In_iso : 
  forall (x1 x2 : Type) (hx : Iso x1 x2) 
         (x3 : x1) (x4 : x2) (_ : rel_iso hx x3 x4) 
         (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) 
         (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
         (_ : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6),
   Iso (Original.LF_DOT_Logic.LF.Logic.In x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_In x4 x6).
Proof.
  intros x1 x2 hx x3 x4 Hx34 x5 x6 Hx56.
  pose proof (proj_rel_iso Hx56) as Hlist_eq.
  (* Use the canonical form: x6 = to list_iso x5 *)
  (* Hlist_eq : to list_iso x5 = x6, need to rewrite x6 -> to list_iso x5 *)
  destruct Hlist_eq.
  unshelve eapply Build_Iso.
  - exact (@In_to x1 x2 hx x3 x4 Hx34 x5).
  - exact (@In_from x1 x2 hx x3 x4 Hx34 x5).
  - (* to_from: for SProp, trivial *)
    intro H. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: for Prop, use proof_irrelevance *)
    intro H. apply seq_of_eq. apply proof_irrelevance.
Defined.

Instance: KnownConstant (@Original.LF_DOT_Logic.LF.Logic.In) := {}.
Instance: KnownConstant (@Imported.Original_LF__DOT__Logic_LF_Logic_In) := {}.
Instance: IsoStatementProofFor (@Original.LF_DOT_Logic.LF.Logic.In) Original_LF__DOT__Logic_LF_Logic_In_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Logic.LF.Logic.In) (@Imported.Original_LF__DOT__Logic_LF_Logic_In) Original_LF__DOT__Logic_LF_Logic_In_iso := {}.
