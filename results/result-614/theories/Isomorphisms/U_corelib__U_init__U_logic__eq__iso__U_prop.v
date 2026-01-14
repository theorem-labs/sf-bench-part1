From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

(* Helper: proof irrelevance for Prop eq expressed in SProp eq *)
Lemma prop_eq_proof_irrel {A : Type} {x y : A} (p q : x = y) : IsomorphismDefinitions.eq p q.
Proof.
  pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ p q) as H.
  destruct H. exact (IsomorphismDefinitions.eq_refl _).
Defined.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Isomorphism for Prop version - when the first type argument maps Type to SProp *)
(* x1 : Type but represents a Prop, x2 : SProp *)
(* Since x2 : SProp, all values of type x2 are proof-irrelevant *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* Since x2 : SProp, x4 and x6 are definitionally equal - SProp has proof irrelevance *)
  (* Also, imported_Corelib_Init_Logic_eq_Prop x4 x6 : SProp, so it's inhabited iff provable *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> Imported.Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    (* x4 and x6 are proof-irrelevant in SProp, so they are definitionally equal *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - (* from: Imported.Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5 *)
    intro Heq.
    (* We need to go back. Since we have H34 and H56, we can use them. *)
    (* H34 : to hx x3 = x4 in SProp, H56 : to hx x5 = x6 in SProp *)
    (* Use the isomorphism *)
    destruct H34. destruct H56.
    (* Now x4 = to hx x3 and x6 = to hx x5 *)
    (* Heq : Imported.Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    (* Use recl to extract equality on from hx _ *)
    pose proof (Imported.Corelib_Init_Logic_eq_Prop_recl x2 (to hx x3) 
             (fun y _ => from hx (to hx x3) = from hx y) 
             (Corelib.Init.Logic.eq_refl _)
             (to hx x5) Heq) as H.
    (* H : from hx (to hx x3) = from hx (to hx x5) *)
    (* Use from_to to convert *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    destruct Hft3. destruct Hft5.
    exact H.
  - (* to_from - goal in SProp *)
    intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to - goal: eq (from ...) (Heq) for Prop eq *)
    intro Heq.
    apply prop_eq_proof_irrel.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
