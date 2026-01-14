From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Use imported Corelib_Init_Logic_eq_Prop which is now in SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* First, let's establish the Prop-to-SProp bridge using SInhabited *)
Definition Corelib_Init_Logic_eq_iso_Prop_aux (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) 
    (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) 
    (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6) :
    Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6).
Proof.
  (* Both sides are propositions. Use SInhabited to bridge Prop <-> SProp *)
  unshelve eapply Build_Iso.
  - (* to *)
    intro Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    unfold rel_iso in H34, H56.
    simpl in H34, H56.
    subst x5.
    destruct H34, H56.
    apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from *)
    intro Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop in Heq.
    unfold rel_iso in H34, H56.
    simpl in H34, H56.
    destruct Heq.
    (* x4 and x6 are now definitionally equal since x2 is SProp *)
    (* Goal: x3 = x5 in Prop *)
    (* Since x2 is SProp, hx x3 and hx x5 are definitionally equal *)
    (* from_to gives: from hx (hx x3) = x3 and from hx (hx x5) = x5 in SProp *)
    (* But hx x3 = hx x5 definitionally, so from hx (hx x3) = from hx (hx x5) definitionally *)
    (* Thus x3 = x5 follows by transitivity *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    apply eq_of_seq in Hft3.
    apply eq_of_seq in Hft5.
    rewrite <- Hft3, <- Hft5.
    reflexivity. (* Works because hx x3 and hx x5 are definitionally equal in SProp *)
  - (* to_from: SProp proof irrelevance *)
    intro. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: Prop proof irrelevance *)
    intro Heq.
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)) := 
  Corelib_Init_Logic_eq_iso_Prop_aux.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
