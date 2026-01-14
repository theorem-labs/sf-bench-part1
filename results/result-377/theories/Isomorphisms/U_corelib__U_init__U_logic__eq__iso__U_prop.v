From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is now in SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop types: We need an isomorphism between (x3 = x5) in Type 
   and imported_Corelib_Init_Logic_eq_Prop x4 x6 in SProp.
   Here x1 : Type, x2 : SProp, with an Iso between them. *)

(* Use proof irrelevance to handle all equality proofs *)
Lemma eq_proofs_equal_Prop : forall (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intros A x y p q.
  apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Qed.

(* We define the isomorphism by providing explicit functions *)
Definition eq_iso_to_Prop (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : IsomorphismDefinitions.eq (to hx x3) x4) (x5 : x1) (x6 : x2) (H56 : IsomorphismDefinitions.eq (to hx x5) x6)
  : x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x6.
Proof.
  intro Heq.
  destruct H34. destruct H56. destruct Heq.
  exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
Defined.

(* For SProp, all elements of the same type are definitionally equal.
   So if we have an SProp equality, we can derive the Type equality by
   using the round-trip property of the isomorphism. *)
Definition eq_iso_from_Prop (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : IsomorphismDefinitions.eq (to hx x3) x4) (x5 : x1) (x6 : x2) (H56 : IsomorphismDefinitions.eq (to hx x5) x6)
  : imported_Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5.
Proof.
  intro Hseq.
  destruct H34. destruct H56.
  (* Since x4 = to hx x3 and x6 = to hx x5, and x4, x6 : x2 : SProp,
     all elements of x2 are definitionally equal.
     So to hx x3 = to hx x5 definitionally in SProp.
     We use from_to to recover x3 = from (to x3) and x5 = from (to x5).
     Since to x3 and to x5 are definitionally equal in SProp,
     from (to x3) = from (to x5), hence x3 = x5. *)
  pose proof (from_to_tseq hx x3) as H3.
  pose proof (from_to_tseq hx x5) as H5.
  (* from (to x3) = x3, from (to x5) = x5 *)
  (* In SProp, to x3 = to x5 definitionally, so from (to x3) = from (to x5) *)
  rewrite <- H3. rewrite <- H5.
  reflexivity.
Defined.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  + exact (@eq_iso_to_Prop x1 x2 hx x3 x4 H34 x5 x6 H56).
  + exact (@eq_iso_from_Prop x1 x2 hx x3 x4 H34 x5 x6 H56).
  + intro Hseq.
    reflexivity.
  + intro Heq.
    (* The goal is IsomorphismDefinitions.eq _ _, which is in SProp, so proof irrelevance applies *)
    apply seq_of_eq.
    apply eq_proofs_equal_Prop.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
