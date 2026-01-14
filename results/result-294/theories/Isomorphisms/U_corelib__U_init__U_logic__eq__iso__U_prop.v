From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper to convert IsomorphismDefinitions.eq to Prop equality *)
Lemma iso_eq_to_prop_eq : forall (A : Type) (x y : A), 
  IsomorphismDefinitions.eq x y -> x = y.
Proof.
  intros A x y H.
  apply (@IsomorphismDefinitions.eq_rect A x (fun z _ => x = z) (@Corelib.Init.Logic.eq_refl A x) y H).
Defined.

(* For the SProp case, x1 is Type (like Prop in original), x2 is SProp *)
(* The key insight is that all inhabitants of SProp are definitionally equal *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
  rel_iso hx x3 x4 -> 
  forall (x5 : x1) (x6 : x2), 
  rel_iso hx x5 x6 -> 
  Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> eq in SProp *)
    intro Heq.
    destruct Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: eq in SProp -> eq in Prop *)
    intro Heq.
    pose proof (from_to hx x3) as FT3.
    pose proof (from_to hx x5) as FT5.
    apply iso_eq_to_prop_eq in FT3.
    apply iso_eq_to_prop_eq in FT5.
    assert (from hx (to hx x3) = from hx (to hx x5)) as Hmid by reflexivity.
    apply (Corelib.Init.Logic.eq_trans (Corelib.Init.Logic.eq_sym FT3)).
    apply (Corelib.Init.Logic.eq_trans Hmid FT5).
  - (* to_from *)
    intro Heq.
    apply (Imported.Corelib_Init_Logic_eq_Prop_indl x2 x4 
      (fun z pf => IsomorphismDefinitions.eq _ pf) 
      IsomorphismDefinitions.eq_refl x6 Heq).
  - (* from_to *)
    intro Heq.
    destruct Heq.
    set (complex_proof := (let FT3 := from_to hx x3 in
                           let FT5 := from_to hx x3 in
                           let FT4 := iso_eq_to_prop_eq FT3 in
                           let FT6 := iso_eq_to_prop_eq FT5 in
                           let Hmid := @Corelib.Init.Logic.eq_refl x1 (from hx (to hx x3)) in
                           Corelib.Init.Logic.eq_trans (Corelib.Init.Logic.eq_sym FT4) 
                             (Corelib.Init.Logic.eq_trans Hmid FT6))).
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance 
      (x3 = x3) complex_proof (@Corelib.Init.Logic.eq_refl x1 x3)) as UIP.
    subst complex_proof.
    rewrite UIP.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
