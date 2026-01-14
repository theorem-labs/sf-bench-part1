From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper to convert from IsomorphismDefinitions.eq to Prop eq *)
Definition eq_to_Prop_eq {A : Type} {x y : A} (H : IsomorphismDefinitions.eq x y) : x = y :=
  match H with
  | IsomorphismDefinitions.eq_refl => Corelib.Init.Logic.eq_refl
  end.

(* This is an isomorphism between Prop eq (with Type argument from Prop) and SProp eq (with SProp argument) *)
(* Since both sides are propositions/SProp types, we use SInhabited approach *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  (* Now x4 = to hx x3 and x6 = to hx x5 *)
  (* Goal: Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5)) *)
  (* Both sides are propositions. Build directly *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq.
    subst x5. exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 (to hx x3)).
  - (* from: imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Heq.
    (* Extract equality from SProp eq using recursor *)
    pose proof (Imported.Corelib_Init_Logic_eq_Prop_recl x2 (to hx x3) 
                  (fun z _ => from hx (to hx x3) = from hx z) 
                  (Corelib.Init.Logic.eq_refl _) (to hx x5) Heq) as Hrec.
    pose proof (eq_to_Prop_eq (from_to hx x3)) as Hft3.
    pose proof (eq_to_Prop_eq (from_to hx x5)) as Hft5.
    rewrite <- Hft3. rewrite <- Hft5.
    exact Hrec.
  - (* to_from: SProp so trivial *)
    intro x. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to: use proof irrelevance for Prop (x3 = x5 is a Prop) *)
    intro x.
    (* Goal: IsomorphismDefinitions.eq (from (to x)) x *)
    (* Both sides are proofs of x3 = x5, which is a Prop. *)
    (* The from function computes as follows: 
       - to x gives an SProp eq
       - from uses that to get a Prop eq from hx x3 = from hx x5
       - Then we use from_to to rewrite to x3 = x5
       The result is a proof of x3 = x5, and by proof irrelevance equals x *)
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance (x3 = x5)) as PI.
    match goal with
    | |- IsomorphismDefinitions.eq ?lhs ?rhs => 
        specialize (PI lhs rhs);
        destruct PI;
        exact (IsomorphismDefinitions.eq_refl _)
    end.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
