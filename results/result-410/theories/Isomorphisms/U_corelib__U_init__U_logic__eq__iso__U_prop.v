From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is in SProp (defined over Prop in Lean, which becomes SProp) *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper lemma: When x2 : SProp and hx : Iso x1 x2, all elements of x1 must be equal *)
(* This is because all elements of x2 are definitionally equal (SProp irrelevance) *)
(* So to hx x3 = to hx x5 definitionally, and by the isomorphism, x3 = x5 *)

Lemma SProp_iso_injective (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 x5 : x1) : x3 = x5.
Proof.
  (* Since x2 : SProp, to hx x3 and to hx x5 are definitionally equal *)
  (* Use from_to to get: from (to x3) = x3 and from (to x5) = x5 *)
  (* Since to x3 = to x5 (by SProp), from (to x3) = from (to x5), hence x3 = x5 *)
  pose proof (from_to hx x3) as H3.
  pose proof (from_to hx x5) as H5.
  (* H3 : IsomorphismDefinitions.eq (from hx (to hx x3)) x3 *)
  (* H5 : IsomorphismDefinitions.eq (from hx (to hx x5)) x5 *)
  (* Since to hx x3 : x2 and to hx x5 : x2 where x2 : SProp, they are definitionally equal *)
  (* So from hx (to hx x3) = from hx (to hx x5) definitionally *)
  destruct H3. destruct H5.
  reflexivity. (* Goal: from hx (to hx x3) = from hx (to hx x5), which is true by SProp *)
Qed.

(* For Prop/SProp case, the isomorphism uses proof irrelevance *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  + intro Heq.
    destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  + intro Hseq.
    destruct H34. destruct H56.
    (* Since x2 : SProp, all values in x2 are definitionally equal *)
    (* So we can use SProp_iso_injective *)
    exact (SProp_iso_injective hx x3 x5).
  + intro Hseq.
    reflexivity.
  + intro Heq.
    destruct H34. destruct H56. destruct Heq.
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
