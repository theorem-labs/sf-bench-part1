From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Equality specialized to SProp - using the SProp version from Imported *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* The isomorphism for equality at the Prop level *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop, Imported.Corelib_Init_Logic_eq_Prop.
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> eq'_Prop x2 x4 x6 *)
    intro Heq.
    destruct Heq.
    (* x3 = x3, need eq'_Prop x2 x4 x6 *)
    (* H34 : to hx x3 = x4, H56 : to hx x3 = x6 *)
    (* First transport: change (to hx x3) to x6 in second argument of eq'_Prop *)
    pose proof (@IsomorphismDefinitions.eq_sind x2 (to hx x3) 
                  (fun z _ => Imported.eq'_Prop x2 (to hx x3) z) 
                  (Imported.eq'_Prop_refl x2 (to hx x3)) x6 H56) as step1.
    (* step1 : eq'_Prop x2 (to hx x3) x6 *)
    (* Now transport: change (to hx x3) to x4 in first argument *)
    exact (@IsomorphismDefinitions.eq_sind x2 (to hx x3) 
             (fun z _ => Imported.eq'_Prop x2 z x6) 
             step1 x4 H34).
  - (* from: eq'_Prop x2 x4 x6 -> x3 = x5 *)
    intro Heq.
    pose proof (from_to hx x3) as FT3.
    pose proof (from_to hx x5) as FT5.
    pose proof (@IsomorphismDefinitions.eq_rect _ (to hx x3)
      (fun y _ => from hx y = x3) 
      (@IsomorphismDefinitions.eq_rect _ (from hx (to hx x3))
        (fun y _ => from hx (to hx x3) = y) 
        (@Corelib.Init.Logic.eq_refl x1 (from hx (to hx x3))) x3 FT3)
      x4 H34) as HX3.
    pose proof (@IsomorphismDefinitions.eq_rect _ (to hx x5)
      (fun y _ => from hx y = x5) 
      (@IsomorphismDefinitions.eq_rect _ (from hx (to hx x5))
        (fun y _ => from hx (to hx x5) = y) 
        (@Corelib.Init.Logic.eq_refl x1 (from hx (to hx x5))) x5 FT5)
      x6 H56) as HX5.
    (* Use eq'_Prop_recl to transport along Heq *)
    pose proof (Imported.eq'_Prop_recl x2 x4
      (fun z _ => from hx x4 = from hx z) 
      (@Corelib.Init.Logic.eq_refl x1 (from hx x4)) x6 Heq) as Hfrom.
    exact (Corelib.Init.Logic.eq_trans 
           (Corelib.Init.Logic.eq_sym HX3) 
           (Corelib.Init.Logic.eq_trans Hfrom HX5)).
  - (* to_from *)
    intro Heq.
    apply (Imported.eq'_Prop_indl x2 x4 
      (fun z pf => IsomorphismDefinitions.eq _ pf) 
      IsomorphismDefinitions.eq_refl x6 Heq).
  - (* from_to *)
    intro Heq.
    destruct Heq.
    apply IsoEq.seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@IsomorphismDefinitions.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
