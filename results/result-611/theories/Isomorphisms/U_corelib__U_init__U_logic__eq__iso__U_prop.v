From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* For the SProp version, we need eq on SProp arguments *)
(* Use the imported version from Lean *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := 
  @Imported.Corelib_Init_Logic_eq_Prop.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
  rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> 
  Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros A B hx a b Hab c d Hcd.
  unshelve eapply Build_Iso.
  - (* to : a = c -> imported_Corelib_Init_Logic_eq_Prop b d *)
    intro Heq.
    (* Since B is SProp, b and d are definitionally equal (SProp proof irrelevance) *)
    (* So imported_Corelib_Init_Logic_eq_Prop b d = imported_Corelib_Init_Logic_eq_Prop b b *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl B b).
  - (* from : imported_Corelib_Init_Logic_eq_Prop b d -> a = c *)
    intro H. 
    (* Need to show a = c : A *)
    (* Since B is SProp, all elements are equal, so to hx a = to hx c *)
    (* By injectivity of to, a = c *)
    pose proof (from_to hx a) as Hfta.
    pose proof (from_to hx c) as Hftc.
    (* Hfta : eq (from hx (to hx a)) a in SProp *)
    (* Hftc : eq (from hx (to hx c)) c in SProp *)
    (* Since B is SProp, to hx a = to hx c definitionally *)
    (* So from hx (to hx a) = from hx (to hx c) *)
    (* Use eq_rect to transport along Hfta and Hftc *)
    pose proof (IsomorphismDefinitions.eq_rect _ (fun z _ => z = from hx (to hx c)) Logic.eq_refl _ Hfta) as step1.
    pose proof (IsomorphismDefinitions.eq_rect _ (fun z _ => a = z) step1 _ Hftc) as step2.
    exact step2.
  - (* to_from: goal in SProp *) intro H. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *) intro Heq.
    (* Goal: IsomorphismDefinitions.eq (from (to Heq)) Heq *)
    (* Both are proofs of a = c : Prop *)
    (* Use proof_irrelevance to get Logic.eq between them, then convert to SProp eq *)
    apply IsoEq.seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.
