From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Helper: proof irrelevance for Prop eq expressed in SProp eq *)
(* We use the fact that Stdlib.Logic.ProofIrrelevance.proof_irrelevance is allowed *)
Lemma prop_eq_proof_irrel_Prop {A : Type} {x y : A} (p q : x = y) : IsomorphismDefinitions.eq p q.
Proof.
  pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ p q) as H.
  destruct H. exact (IsomorphismDefinitions.eq_refl _).
Defined.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* This is an isomorphism between Prop eq (for Prop-valued types) and SProp eq *)
(* For SProp-valued x2, all inhabitants are equal by proof irrelevance *)
(* So imported_Corelib_Init_Logic_eq_Prop x4 x6 is always inhabited by refl *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  (* Now x4 = to hx x3 and x6 = to hx x5, both in SProp x2 *)
  (* Since x2 : SProp, we know that to hx x3 = to hx x5 definitionally in SProp *)
  (* So imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) is inhabited by refl *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq. subst x5.
    apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Heq.
    (* Since to hx is an iso and x3, x5 both map to the same SProp, 
       we need to use the inverse. But wait - we can't just get x3 = x5 from 
       SProp equality of their images. We need more structure. *)
    (* Actually, since from_to gives us x3 = from(to x3) and x5 = from(to x5),
       and since to hx x3 and to hx x5 are in SProp (so definitionally equal),
       from(to hx x3) = from(to hx x5) *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    destruct Hft3. destruct Hft5.
    (* Now goal is: from hx (to hx x3) = from hx (to hx x5) *)
    (* Since to hx x3 and to hx x5 are both in SProp x2, they are equal *)
    reflexivity.
  - (* to_from *)
    intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to *)
    intro Heq.
    apply prop_eq_proof_irrel_Prop.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
