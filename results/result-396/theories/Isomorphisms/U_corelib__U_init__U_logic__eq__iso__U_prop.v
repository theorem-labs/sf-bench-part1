From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For SProp, we use proof irrelevance - all proofs are equal *)
(* The Iso from Prop eq (x = y) to SProp eq uses the fact that both are propositions *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  (* Goal: Iso (x3 = x5) (Imported.Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5)) *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> Imported.Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq. subst x5. apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: Imported.Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Heq.
    (* Use the recursor to build a proof *)
    pose proof (Imported.Corelib_Init_Logic_eq_Prop_recl x2 (hx x3) 
           (fun z _ => from hx (hx x3) = from hx z) 
           (Corelib.Init.Logic.eq_refl _) 
           (hx x5) Heq) as Hfrom.
    (* Now combine using the SProp eq_rect 
       eq_rect α a P base y e  gives  P y e,  where base : P a eq_refl 
       
       We have: from_to hx x3 : eq (from hx (hx x3)) x3
       We have: from_to hx x5 : eq (from hx (hx x5)) x5
       We have: Hfrom : from hx (hx x3) = from hx (hx x5)
       We want: x3 = x5
       
       First use from_to hx x5 to transport Hfrom into (from hx (hx x3) = x5):
         eq_rect (from hx (hx x5)) (fun y _ => from hx (hx x3) = y) Hfrom x5 (from_to hx x5)
       
       Then use from_to hx x3 to transport (from hx (hx x3) = x5) into (x3 = x5):
         eq_rect (from hx (hx x3)) (fun y _ => y = x5) ... x3 (from_to hx x3)
    *)
    exact (@IsomorphismDefinitions.eq_rect x1 (from hx (hx x3))
             (fun y _ => y = x5) 
             (@IsomorphismDefinitions.eq_rect x1 (from hx (hx x5))
                (fun y _ => from hx (hx x3) = y)
                Hfrom
                x5 (from_to hx x5))
             x3 (from_to hx x3)).
  - (* to_from *)
    intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to *)
    intro Heq.
    (* The from function maps to a term of type x3 = x5 *)
    (* Use proof irrelevance for Prop equalities *)
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance (x3 = x5) 
      (@IsomorphismDefinitions.eq_rect x1 (from hx (hx x3))
             (fun y _ => y = x5) 
             (@IsomorphismDefinitions.eq_rect x1 (from hx (hx x5))
                (fun y _ => from hx (hx x3) = y)
                (Imported.Corelib_Init_Logic_eq_Prop_recl x2 (hx x3) 
                   (fun z _ => from hx (hx x3) = from hx z) 
                   (Corelib.Init.Logic.eq_refl _) 
                   (hx x5) (Imported.Corelib_Init_Logic_eq_Prop_refl x2 (hx x3)))
                x5 (from_to hx x5))
             x3 (from_to hx x3))
      Heq) as PI.
    destruct PI. exact (IsomorphismDefinitions.eq_refl _).
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
