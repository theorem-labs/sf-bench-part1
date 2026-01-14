From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* This is an isomorphism between Prop eq (for Prop arguments) and SProp eq 
   The key insight: if we have Iso x1 x2 where x2 : SProp, then x1 has at most one
   inhabitant up to equality (since all SProp values are definitionally equal and
   the iso preserves this). *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> Imported.Corelib_Init_Logic_eq_Prop (hx x3) (hx x5) *)
    intro Heq. subst x5. apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: Imported.Corelib_Init_Logic_eq_Prop (hx x3) (hx x5) -> x3 = x5 *)
    intro Heq.
    (* Key: hx x3 and hx x5 are in SProp, so they're definitionally equal.
       Therefore from (hx x3) = from (hx x5) definitionally.
       Combined with from_to, we get x3 = from (hx x3) = from (hx x5) = x5 *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    (* from_to gives SProp eq; destruct it to rewrite *)
    destruct Hft3. destruct Hft5.
    (* Now we're in context where x3 = from (hx x3) and x5 = from (hx x5) 
       and goal is from (hx x3) = from (hx x5)
       Since hx x3 and hx x5 are both in SProp and thus definitionally equal,
       from (hx x3) = from (hx x5) by computation *)
    exact Logic.eq_refl.
  - (* to_from: target is SProp so use eq_refl *)
    intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to *)
    intro Heq.
    (* The 'from' function composes the destruct of from_to with eq_refl.
       After applying 'to' then 'from', we need to show the result equals Heq.
       Since x3 = x5 is a Prop, use proof irrelevance. *)
    apply (match Stdlib.Logic.ProofIrrelevance.proof_irrelevance (x3 = x5) _ Heq 
           in (_ = y) return (IsomorphismDefinitions.eq _ y) with
           | Logic.eq_refl => IsomorphismDefinitions.eq_refl
           end).
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
