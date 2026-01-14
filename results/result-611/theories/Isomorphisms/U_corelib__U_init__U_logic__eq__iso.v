From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Use the Imported.Corelib_Init_Logic_eq which is now SProp *)
Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := 
  @Imported.Corelib_Init_Logic_eq.

(* Build the iso to function *)
Definition Corelib_Init_Logic_eq_iso_to (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6) :
  @Corelib.Init.Logic.eq x1 x3 x5 -> @imported_Corelib_Init_Logic_eq x2 x4 x6.
Proof.
  unfold imported_Corelib_Init_Logic_eq.
  intro Heq.
  destruct Heq. (* Now x3 = x5 *)
  (* H34 : eq (to hx x3) x4, H56 : eq (to hx x3) x6 *)
  (* Need to show x4 = x6 *)
  destruct H34 using IsomorphismDefinitions.eq_sind.
  destruct H56 using IsomorphismDefinitions.eq_sind.
  exact (Imported.Corelib_Init_Logic_eq_refl _ _).
Defined.

(* For the reverse direction, we use the fact that Imported eq is in SProp *)
(* We use recl which eliminates into Type *)
Definition Corelib_Init_Logic_eq_iso_from (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6) :
  @imported_Corelib_Init_Logic_eq x2 x4 x6 -> @Corelib.Init.Logic.eq x1 x3 x5.
Proof.
  unfold imported_Corelib_Init_Logic_eq.
  intro Heq.
  (* Heq : Imported.Corelib_Init_Logic_eq x4 x6 which is SProp *)
  (* Use _recl to eliminate to Type *)
  apply (Imported.Corelib_Init_Logic_eq_recl x2 x4 (fun y _ => x3 = from hx y)) in Heq.
  - (* Now Heq : x3 = from hx x6 *)
    (* H56 : eq (to hx x5) x6 *)
    pose proof (from_to hx x5) as Hft5.
    (* Hft5 : eq (from hx (to hx x5)) x5 *)
    (* from hx x6 = from hx (to hx x5) by H56 *)
    pose proof (IsomorphismDefinitions.eq_rect (to hx x5) (fun z _ => from hx z = from hx (to hx x5)) Logic.eq_refl x6 H56) as step.
    (* step : from hx x6 = from hx (to hx x5) *)
    pose proof (IsomorphismDefinitions.eq_rect (from hx (to hx x5)) (fun z _ => from hx (to hx x5) = z) Logic.eq_refl x5 Hft5) as step2.
    (* step2 : from hx (to hx x5) = x5 *)
    exact (Logic.eq_trans Heq (Logic.eq_trans step step2)).
  - (* Need to show x3 = from hx x4 *)
    pose proof (from_to hx x3) as Hft3.
    (* Hft3 : eq (from hx (to hx x3)) x3 *)
    (* H34 : eq (to hx x3) x4 *)
    pose proof (IsomorphismDefinitions.eq_rect (to hx x3) (fun z _ => from hx (to hx x3) = from hx z) Logic.eq_refl x4 H34) as step.
    (* step : from hx (to hx x3) = from hx x4 *)
    pose proof (IsomorphismDefinitions.eq_rect (from hx (to hx x3)) (fun z _ => z = from hx (to hx x3)) Logic.eq_refl x3 Hft3) as step2.
    (* step2 : x3 = from hx (to hx x3) *)
    exact (Logic.eq_trans step2 step).
Defined.

Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros A B hx a b Hab c d Hcd.
  unshelve eapply Build_Iso.
  - exact (@Corelib_Init_Logic_eq_iso_to A B hx a b Hab c d Hcd).
  - exact (@Corelib_Init_Logic_eq_iso_from A B hx a b Hab c d Hcd).
  - (* to_from: goal is in SProp, so proof irrelevance applies definitionally *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: goal is eq (from (to Heq)) Heq : Type *)
    intro Heq.
    (* Use UIP derived from proof_irrelevance *)
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ 
      (@Corelib_Init_Logic_eq_iso_from A B hx a b Hab c d Hcd 
        (@Corelib_Init_Logic_eq_iso_to A B hx a b Hab c d Hcd Heq))
      Heq) as UIP_pf.
    exact (match UIP_pf with Logic.eq_refl => IsomorphismDefinitions.eq_refl end).
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.

(* Re-export the Prop version from the separate file *)
From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso__U_prop.
