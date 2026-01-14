From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
From LeanImport Require Import Lean.
From Stdlib Require Import Logic.Eqdep_dec.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Use proof irrelevance to handle all equality proofs *)
Lemma eq_proofs_equal_prop : forall (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intros A x y p q.
  apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Qed.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Convert from IsomorphismDefinitions.eq (SProp) to Logic.eq *)
Definition seq_to_logeq_Prop {A : Type} {x y : A} (H : IsomorphismDefinitions.eq x y) : x = y :=
  match H with IsomorphismDefinitions.eq_refl => Logic.eq_refl end.

(* For Prop/SProp isomorphisms, elements of SProp x2 are all proof-irrelevantly equal.
   So imported_Corelib_Init_Logic_eq_Prop x4 x6 is always inhabited since x4 = x6 in SProp. *)

(* For Prop, we need a version that works with SProp on both sides *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  + (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq. destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  + (* from: imported_Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5 *)
    intro Hseq.
    destruct H34. destruct H56.
    transitivity (from hx (to hx x3)).
    * symmetry. exact (seq_to_logeq_Prop (from_to hx x3)).
    * transitivity (from hx (to hx x5)).
      -- reflexivity. (* SProp proof irrelevance: to hx x3 = to hx x5 in SProp *)
      -- exact (seq_to_logeq_Prop (from_to hx x5)).
  + intro Hseq. reflexivity.
  + intro Heq.
    destruct H34. destruct H56. destruct Heq.
    pose proof (@eq_proofs_equal_prop x1 x3 x3 
      (Logic.eq_trans (Logic.eq_sym (seq_to_logeq_Prop (from_to hx x3)))
         (Logic.eq_trans Logic.eq_refl (seq_to_logeq_Prop (from_to hx x3))))
      Logic.eq_refl) as Hpi.
    rewrite Hpi.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
