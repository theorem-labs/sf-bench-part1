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

(* For Prop/SProp isomorphisms, build directly *)
Definition eq_iso_to_Prop (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6)
  : (x3 = x5) -> imported_Corelib_Init_Logic_eq_Prop x4 x6.
Proof.
  intro Heq. destruct Heq.
  unfold rel_iso in H34, H56.
  destruct H34, H56.
  exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
Defined.

(* Helper to get equality in x1 from SProp equality via isomorphism *)
Definition iso_injective_sprop : forall (A : Type) (B : SProp) (iso : Iso A B) (x y : A),
  IsomorphismDefinitions.eq (to iso x) (to iso y) -> x = y.
Proof.
  intros A B iso x y H.
  (* H : to iso x = to iso y in SProp *)
  (* Use f_equal from and from_to *)
  pose proof (f_equal (from iso) H) as H'.
  (* H' : from (to iso x) = from (to iso y) in SProp *)
  pose proof (from_to iso x) as Hx.
  pose proof (from_to iso y) as Hy.
  (* Hx : from (to iso x) = x, Hy : from (to iso y) = y, both in SProp *)
  destruct Hx. destruct Hy. destruct H'.
  reflexivity.
Defined.

Definition eq_iso_from_Prop (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6)
  : imported_Corelib_Init_Logic_eq_Prop x4 x6 -> (x3 = x5).
Proof.
  intro Hseq.
  unfold rel_iso in H34, H56.
  (* H34 : to hx x3 = x4 in SProp, H56 : to hx x5 = x6 in SProp *)
  (* Hseq : imported_Corelib_Init_Logic_eq_Prop x4 x6 in SProp *)
  destruct Hseq.
  (* Now x4 = x6 definitionally in SProp *)
  apply (iso_injective_sprop hx x3 x5).
  destruct H34. destruct H56.
  apply IsomorphismDefinitions.eq_refl.
Defined.

From Stdlib Require Import Logic.ProofIrrelevance.

(* Use proof irrelevance to convert any equality proof to eq_refl in SProp *)
Lemma pi_eq_to_seq {A : Type} {x y : A} (p : x = y) : IsomorphismDefinitions.eq p (match p with Logic.eq_refl => Logic.eq_refl end).
Proof.
  destruct p. apply IsomorphismDefinitions.eq_refl.
Defined.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  - exact (@eq_iso_to_Prop x1 x2 hx x3 x4 H34 x5 x6 H56).
  - exact (@eq_iso_from_Prop x1 x2 hx x3 x4 H34 x5 x6 H56).
  - intro Hseq. reflexivity.
  - intro Heq.
    (* from_to needs IsomorphismDefinitions.eq@{Type|...} *)
    (* Use proof irrelevance: all proofs of x3 = x5 are equal *)
    pose proof (proof_irrelevance _ (eq_iso_from_Prop H34 H56 (eq_iso_to_Prop H34 H56 Heq)) Heq) as PI.
    apply seq_of_peq_t. exact PI.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
