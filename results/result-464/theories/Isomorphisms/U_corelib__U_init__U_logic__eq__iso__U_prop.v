From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is in SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Key lemma: when x2 : SProp and hx : Iso x1 x2, all elements of x1 are equal *)
(* Because all elements of x2 are equal (SProp irrelevance), and from hx is injective *)
Lemma iso_to_sprop_singleton (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (a b : x1) : a = b.
Proof.
  (* to hx a and to hx b are both in x2 : SProp, so they are definitionally equal *)
  (* Therefore from hx (to hx a) = from hx (to hx b) *)
  (* By from_to: a = from hx (to hx a) and b = from hx (to hx b) *)
  transitivity (from hx (to hx a)).
  - symmetry. apply IsoEq.eq_of_seq. apply from_to.
  - transitivity (from hx (to hx b)).
    + reflexivity.  (* to hx a = to hx b in SProp *)
    + apply IsoEq.eq_of_seq. apply from_to.
Qed.

(* Lemma: proof irrelevance for reflexive equality *)
Lemma eq_refl_unique (A : Type) (x : A) (H : x = x) : H = Logic.eq_refl.
Proof.
  apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Qed.

(* For SProp types, the isomorphism is trivial since all elements are equal *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  (* Since hx : Iso x1 x2 with x2 : SProp, x1 is a singleton *)
  pose proof (iso_to_sprop_singleton hx x3 x5) as Heq35.
  (* Rewrite x5 to x3 everywhere *)
  subst x5.
  (* Now the goal is Iso (x3 = x3) (Corelib_Init_Logic_eq_Prop x4 x6) *)
  (* Both x4 and x6 are in x2:SProp, so are definitionally equal *)
  (* imported_Corelib_Init_Logic_eq_Prop x4 x6 is inhabited since x4 = x6 *)
  unshelve eapply Build_Iso.
  - (* to : (x3 = x3) -> (Corelib_Init_Logic_eq_Prop x4 x6) *)
    intro Heq. destruct H34. destruct H56.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - (* from : (Corelib_Init_Logic_eq_Prop x4 x6) -> (x3 = x3) *)
    intro Hseq. reflexivity.
  - (* to_from *)
    intro Hseq.
    reflexivity.  (* Both sides are in SProp *)
  - (* from_to *)
    intro Heq.
    (* Heq : x3 = x3. Need: eq (from (to Heq)) Heq in SProp *)
    (* from (to Heq) = eq_refl, so we need eq eq_refl Heq *)
    (* First show Heq = eq_refl in Prop, then convert to SProp eq *)
    pose proof (@eq_refl_unique x1 x3 Heq) as HH.
    rewrite HH.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
