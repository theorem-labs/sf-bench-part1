From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* For equality at SProp, we use the imported version *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := 
  Imported.Corelib_Init_Logic_eq_Prop.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
    rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> 
    Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* Since x2 is SProp, x4 and x6 are definitionally equal, so we can derive x3 = x5 *)
  (* The key insight is that from hx maps both x4 and x6 to the same value *)
  pose proof (from_to hx x3) as FT3.
  pose proof (from_to hx x5) as FT5.
  (* from hx x4 = x3 follows from H34 and FT3 *)
  assert (HX3 : from hx x4 = x3).
  { pose proof (@IsomorphismDefinitions.eq_rect x2 (to hx x3)
      (fun y dummy2 => from hx y = x3) 
      (@IsomorphismDefinitions.eq_rect x1 (from hx (to hx x3))
        (fun y dummy2 => from hx (to hx x3) = y) 
        (@Corelib.Init.Logic.eq_refl x1 (from hx (to hx x3))) x3 FT3)
      x4 H34).
    exact H. }
  assert (HX5 : from hx x6 = x5).
  { pose proof (@IsomorphismDefinitions.eq_rect x2 (to hx x5)
      (fun y dummy2 => from hx y = x5) 
      (@IsomorphismDefinitions.eq_rect x1 (from hx (to hx x5))
        (fun y dummy2 => from hx (to hx x5) = y) 
        (@Corelib.Init.Logic.eq_refl x1 (from hx (to hx x5))) x5 FT5)
      x6 H56).
    exact H. }
  (* Since x4 and x6 are in SProp, from hx x4 = from hx x6 definitionally *)
  (* So x3 = from hx x4 = from hx x6 = x5 *)
  pose proof (Corelib.Init.Logic.eq_trans (Corelib.Init.Logic.eq_sym HX3) HX5) as X3_eq_X5.
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> True' *)
    intro Heq. exact Imported.True_intro.
  - (* from: True' -> x3 = x5 *)
    intro Htrue. exact X3_eq_X5.
  - (* to_from *)
    intro t.
    apply (Imported.True_indl (fun t => IsomorphismDefinitions.eq Imported.True_intro t) IsomorphismDefinitions.eq_refl t).
  - (* from_to *)
    intro Heq.
    (* Use proof irrelevance: all proofs of x3 = x5 are equal *)
    (* The goal is eq (from (to Heq)) Heq where eq is in SProp *)
    (* from (to Heq) = X3_eq_X5 and Heq : x3 = x5 *)
    (* Since they're both proofs of x3 = x5, by proof irrelevance they're equal *)
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance (x3 = x5) X3_eq_X5 Heq) as PI.
    rewrite PI.
    apply IsomorphismDefinitions.eq_refl.
Defined.
