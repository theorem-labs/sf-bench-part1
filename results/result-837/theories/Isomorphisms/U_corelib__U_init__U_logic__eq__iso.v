From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_true__iso.
From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso__U_prop.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq).

(* Helper: extract Logic.eq from Imported.Corelib_Init_Logic_eq *)
Definition seq_to_eq {A : Type} {x y : A} (H : Imported.Corelib_Init_Logic_eq A x y) : x = y :=
  match H with Imported.Corelib_Init_Logic_eq_refl _ _ => Logic.eq_refl end.

(* Helper lemma: isomorphisms are injective *)
Lemma iso_injective : forall (A B : Type) (i : Iso A B) (x y : A),
  to i x = to i y -> x = y.
Proof.
  intros A B i x y H.
  rewrite <- (from_to i x).
  rewrite <- (from_to i y).
  apply Logic.f_equal. exact H.
Qed.

(* We define the isomorphism by providing explicit functions *)
Definition eq_iso_to (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : IsomorphismDefinitions.eq (to hx x3) x4) (x5 : x1) (x6 : x2) (H56 : IsomorphismDefinitions.eq (to hx x5) x6)
  : x3 = x5 -> imported_Corelib_Init_Logic_eq x4 x6.
Proof.
  intro Heq.
  destruct H34. destruct H56. destruct Heq.
  exact (Imported.Corelib_Init_Logic_eq_refl _ _).
Defined.

Definition eq_iso_from (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : IsomorphismDefinitions.eq (to hx x3) x4) (x5 : x1) (x6 : x2) (H56 : IsomorphismDefinitions.eq (to hx x5) x6)
  : imported_Corelib_Init_Logic_eq x4 x6 -> x3 = x5.
Proof.
  intro Hseq.
  destruct H34. destruct H56.
  apply (@iso_injective x1 x2 hx x3 x5).
  apply seq_to_eq. exact Hseq.
Defined.

(* Use proof irrelevance to handle all equality proofs *)
Lemma eq_proofs_equal : forall (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intros A x y p q.
  apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Qed.

Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  + exact (@eq_iso_to x1 x2 hx x3 x4 H34 x5 x6 H56).
  + exact (@eq_iso_from x1 x2 hx x3 x4 H34 x5 x6 H56).
  + intro Hseq.
    reflexivity.
  + intro Heq.
    destruct H34. destruct H56. destruct Heq.
    unfold eq_iso_from, eq_iso_to. simpl.
    rewrite (@eq_proofs_equal x1 x3 x3 (iso_injective hx x3 x3 Logic.eq_refl) Logic.eq_refl).
    apply IsomorphismDefinitions.eq_refl.
Defined.

(* For SProp variant - required by Interface *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := Imported.Corelib_Init_Logic_eq_Prop.

(* The key insight: Iso x1 x2 where x2 : SProp means x1 has at most one element.
   This is because all elements of x2 are equal in SProp, and the iso is bijective. *)

(* Helper to convert IsomorphismDefinitions.eq to Logic.eq *)
Lemma iso_eq_to_eq : forall (A : Type) (x y : A), IsomorphismDefinitions.eq x y -> x = y.
Proof. intros A x y H. destruct H. reflexivity. Qed.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unfold rel_iso in H34, H56.
  destruct H34. destruct H56.
  (* Since x2 : SProp, (to hx x3) and (to hx x5) are definitionally equal in SProp *)
  (* Hence from hx (to hx x3) = from hx (to hx x5) *)
  assert (Heq : x3 = x5).
  { 
    pose proof (from_to hx x3) as H1.
    pose proof (from_to hx x5) as H2.
    apply iso_eq_to_eq in H1. apply iso_eq_to_eq in H2.
    rewrite <- H1. rewrite <- H2.
    reflexivity. (* Works because x2 : SProp makes to hx x3 = to hx x5 definitionally *)
  }
  rewrite Heq.
  unshelve eapply Build_Iso.
  { intro H. exact (Imported.Corelib_Init_Logic_eq_refl_Prop x2 (to hx x5)). }
  { intro H. reflexivity. }
  { intro H. apply IsomorphismDefinitions.eq_refl. }
  { intro H.
    (* Need: eq eq_refl H where H : x5 = x5 *)
    (* Use proof irrelevance: all proofs of x5 = x5 are equal *)
    rewrite (@eq_proofs_equal x1 x5 x5 Logic.eq_refl H).
    apply IsomorphismDefinitions.eq_refl. }
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.

Instance: KnownConstant imported_Corelib_Init_Logic_eq_Prop := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) imported_Corelib_Init_Logic_eq_Prop Corelib_Init_Logic_eq_iso_Prop := {}.