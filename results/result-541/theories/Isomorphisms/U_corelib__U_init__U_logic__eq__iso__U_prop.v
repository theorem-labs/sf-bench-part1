From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* The interface expects: imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp *)
(* This matches Imported.Corelib_Init_Logic_eq_Prop exactly *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* This is an isomorphism between Prop eq (on Prop types) and SProp eq *)
(* For Prop types (x1 : Type, x2 : SProp), we need to map equality *)
(* x2 : SProp means x2 is a type of sort SProp *)
(* x4 : x2 means x4 is an element of x2 *)
(* imported_Corelib_Init_Logic_eq_Prop x4 x6 means: Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 *)
(* Wait - that's not right. Let me re-read the interface. *)
(* "forall x : SProp, x -> x -> SProp" means the FIRST argument x is a type in SProp,
   then x4, x6 : x are elements of that type. *)
(* So imported_Corelib_Init_Logic_eq_Prop x4 x6 doesn't typecheck as x4 : x2. *)
(* Actually, looking again: the call is imported_Corelib_Init_Logic_eq_Prop x4 x6
   where x4, x6 : x2 (with x2 : SProp). But the definition says:
   forall x : SProp, x -> x -> SProp
   So when we apply it to x4 : x2, we're using x2 as the implicit first argument. *)

(* Since all proofs in SProp are equal, the isomorphism is trivial *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  (* Goal: Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5)) *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> Imported.Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx x5) *)
    intro Heq. subst x5. apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: Imported.Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Heq.
    pose proof (Imported.Corelib_Init_Logic_eq_Prop_recl x2 (to hx x3) (fun z _ => from hx (to hx x3) = from hx z) (Corelib.Init.Logic.eq_refl _) (to hx x5) Heq) as H.
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    destruct Hft3. destruct Hft5.
    exact H.
  - (* to_from *)
    intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to *)
    intro Heq.
    (* Use proof irrelevance for Prop equalities *)
    assert (Hpi: forall (p q : x3 = x5), IsomorphismDefinitions.eq p q).
    { intros p q. 
      pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ p q) as H.
      rewrite H. apply IsomorphismDefinitions.eq_refl. }
    apply Hpi.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
