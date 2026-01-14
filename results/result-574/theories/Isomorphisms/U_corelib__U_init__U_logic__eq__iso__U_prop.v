From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper to go from SProp eq to Prop eq *)
Definition sprop_eq_to_prop_eq_Prop' {A : SProp} {x y : A} (H : Imported.Corelib_Init_Logic_eq_Prop A x y) {P : A -> Type} (p : P x) : P y :=
  Imported.Corelib_Init_Logic_eq_Prop_recl A x (fun z _ => P z) p y H.

(* This is an isomorphism between Prop eq and SProp eq for Prop arguments *)
(* Note: x1 : Type because the interface expects Type, but we constrain it to Prop via hx : Iso x1 x2 where x2 : SProp *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  unshelve eapply Build_Iso.
  - (* to: (x3 = x5) -> Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq. subst x5. exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - (* from: Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> (x3 = x5) *)
    intro Heq.
    pose proof (Imported.Corelib_Init_Logic_eq_Prop_recl x2 (to hx x3) 
                  (fun z _ => from hx (to hx x3) = from hx z) 
                  (Corelib.Init.Logic.eq_refl (from hx (to hx x3))) 
                  (to hx x5) Heq) as H.
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    destruct Hft3. destruct Hft5.
    exact H.
  - (* to_from: in SProp, trivial *)
    intro Heq. exact IsomorphismDefinitions.eq_refl.
  - (* from_to: use proof irrelevance *)
    intro Heq.
    apply seq_of_peq_t. apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
