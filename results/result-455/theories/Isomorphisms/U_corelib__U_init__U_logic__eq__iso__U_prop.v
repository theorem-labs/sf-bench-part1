From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.
From Stdlib Require Import Logic.ProofIrrelevance.

(* Use proof irrelevance for Prop equalities *)
Lemma eq_proofs_equal : forall (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intros A x y p q.
  apply proof_irrelevance.
Qed.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For the Prop variant, the isomorphism between Type and SProp uses an Iso where
   from_to and to_from are in SProp. We define the mapping explicitly. *)
Definition eq_iso_Prop_to (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : IsomorphismDefinitions.eq (to hx x3) x4) (x5 : x1) (x6 : x2) (H56 : IsomorphismDefinitions.eq (to hx x5) x6)
  : x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x6.
Proof.
  intro Heq.
  destruct H34. destruct H56. destruct Heq.
  exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
Defined.

(* For SProp targets, we use from_to from the Iso to get back *)
Definition eq_iso_Prop_from (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : IsomorphismDefinitions.eq (to hx x3) x4) (x5 : x1) (x6 : x2) (H56 : IsomorphismDefinitions.eq (to hx x5) x6)
  : imported_Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5.
Proof.
  intro Hseq.
  destruct H34. destruct H56.
  (* Hseq : imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
  (* We need x3 = x5. Use from_to and the fact that from is injective on the image of to *)
  rewrite <- (from_to hx x3).
  rewrite <- (from_to hx x5).
  destruct Hseq. (* SProp equality can be destructed *)
  reflexivity.
Defined.

(* When mapping to SProp, the isomorphism is essentially between Prop (x3=x5) and SProp (imported eq) *)
(* Key insight: If Iso x1 x2 exists where x2 : SProp, then x1 is a subsingleton!
   Proof: for any a, b : x1, we have to hx a, to hx b : x2 (SProp), so they're equal.
   Since from is a function, from (to hx a) = from (to hx b).
   By from_to (which gives SProp equality but implies transport), a = b.
*)

(* Helper: Any two elements of a type isomorphic to SProp are equal *)
Lemma iso_to_SProp_subsingleton : forall (A : Type) (B : SProp) (i : Iso A B) (x y : A), x = y.
Proof.
  intros A B i x y.
  (* to i x and to i y are both in B : SProp, so from i applied to them is equal *)
  transitivity (from i (to i x)).
  - symmetry. destruct (from_to i x). reflexivity.
  - transitivity (from i (to i y)).
    + reflexivity. (* from i applied to equal SProp values *)
    + destruct (from_to i y). reflexivity.
Qed.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  destruct H34. destruct H56.
  (* Now x4 = to hx x3, x6 = to hx x5, both in x2 : SProp *)
  (* imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) is SProp *)
  
  unshelve eapply Build_Iso.
  + (* to: x3 = x5 -> imported eq (to hx x3) (to hx x5) *)
    intro Heq. destruct Heq. exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  + (* from: imported eq (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Hseq. exact (iso_to_SProp_subsingleton hx x3 x5).
  + (* to_from: trivial since target is SProp *)
    intro Hseq. reflexivity.
  + (* from_to: we need IsomorphismDefinitions.eq (from (to Heq)) Heq *)
    intro Heq.
    (* from (to Heq) = iso_to_SProp_subsingleton hx x3 x5 regardless of Heq *)
    (* Heq : x3 = x5 *)
    (* We need to show: IsomorphismDefinitions.eq (iso_to_SProp_subsingleton hx x3 x5) Heq *)
    (* Use eq_proofs_equal and then transport to SProp eq *)
    rewrite (@eq_proofs_equal x1 x3 x5 (iso_to_SProp_subsingleton hx x3 x5) Heq).
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
