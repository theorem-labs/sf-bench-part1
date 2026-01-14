From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.
From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso__U_prop.

(* The Lean export now produces eq in SProp directly *)
Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq.

Definition eq_iso_to {x1 x2 : Type} (hx : Iso x1 x2) (x3 x5 : x1) 
  (Heq : x3 = x5) : Imported.Corelib_Init_Logic_eq x2 (to hx x3) (to hx x5).
Proof.
  destruct Heq.
  apply Imported.Corelib_Init_Logic_eq_refl.
Defined.

Definition eq_iso_from {x1 x2 : Type} (hx : Iso x1 x2) (x3 x5 : x1) 
  (Heq : Imported.Corelib_Init_Logic_eq x2 (to hx x3) (to hx x5)) : x3 = x5.
Proof.
  pose proof (from_to hx x3) as Hrt3.
  pose proof (from_to hx x5) as Hrt5.
  destruct Hrt3. destruct Hrt5.
  apply (Imported.Corelib_Init_Logic_eq_recl x2 (to hx x3) (fun y _ => from hx (to hx x3) = from hx y) Logic.eq_refl (to hx x5) Heq).
Defined.

Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  unshelve eapply Build_Iso.
  - (* to: eq in Type -> eq in SProp *)
    intro Heq.
    exact (@eq_iso_to x1 x2 hx x3 x5 Heq).
  - (* from: eq in SProp -> eq in Type *)
    intro Heq.
    exact (@eq_iso_from x1 x2 hx x3 x5 Heq).
  - (* to_from: SProp proof irrelevance is automatic *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: Need to show eq_iso_from (eq_iso_to Heq) = Heq *)
    intro Heq.
    (* Use UIP / proof irrelevance for Type equality *)
    destruct Heq.
    (* After destruct, x3 = x5 becomes x3 = x3, i.e. eq_refl *)
    (* Goal: eq_iso_from (eq_iso_to eq_refl) = eq_refl *)
    (* Both sides have type x3 = x3, which is a singleton type by UIP *)
    (* But we're in SProp for IsomorphismDefinitions.eq, so we can use eq_refl *)
    unfold eq_iso_from, eq_iso_to.
    (* The goal should reduce to eq_refl = eq_refl after unfolding *)
    (* However the nested destructs complicate this *)
    (* Let's use proof irrelevance *)
    match goal with
    | |- IsomorphismDefinitions.eq ?x ?y => 
        pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ x y) as Hirr;
        destruct Hirr; apply IsomorphismDefinitions.eq_refl
    end.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.
