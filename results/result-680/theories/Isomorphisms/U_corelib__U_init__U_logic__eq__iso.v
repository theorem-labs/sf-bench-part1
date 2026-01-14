From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Corelib_Init_Logic_eq from Lean wraps Eq which is in SProp *)
Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq).

(* Helper function: x3 = x5 -> Imported.Eq x2 x4 x6 given the rel_iso constraints *)
Definition to_eq {x1 x2 : Type} {hx : Iso x1 x2} {x3 : x1} {x4 : x2} (h34 : rel_iso hx x3 x4) {x5 : x1} {x6 : x2} (h56 : rel_iso hx x5 x6) 
  : x3 = x5 -> Imported.Eq x2 x4 x6.
Proof.
  intro e.
  subst x5.
  unfold rel_iso in h34, h56.
  destruct h34. destruct h56.
  exact (Imported.Eq_refl x2 (hx x3)).
Defined.

(* Helper function: Imported.Eq x2 x4 x6 -> x3 = x5 given the rel_iso constraints *)
Definition from_eq {x1 x2 : Type} {hx : Iso x1 x2} {x3 : x1} {x4 : x2} (h34 : rel_iso hx x3 x4) {x5 : x1} {x6 : x2} (h56 : rel_iso hx x5 x6) 
  : Imported.Eq x2 x4 x6 -> x3 = x5.
Proof.
  intro e.
  destruct e.
  unfold rel_iso in h34, h56.
  pose proof (from_to hx x3) as H3.
  pose proof (from_to hx x5) as H5.
  destruct h34.
  destruct h56.
  exact (match H3 in (IsomorphismDefinitions.eq _ y) return (y = x5) with 
         | IsomorphismDefinitions.eq_refl => 
           match H5 in (IsomorphismDefinitions.eq _ z) return (from hx (hx x5) = z) with
           | IsomorphismDefinitions.eq_refl => Logic.eq_refl
           end
         end).
Defined.

Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 h34 x5 x6 h56.
  unfold imported_Corelib_Init_Logic_eq.
  unfold Imported.Corelib_Init_Logic_eq.
  refine {| to := to_eq h34 h56; from := from_eq h34 h56 |}.
  - intro x. destruct x. apply IsomorphismDefinitions.eq_refl.
  - intro x. destruct x.
    (* Use proof irrelevance for Logic.eq - the result is in Prop, so we can use this *)
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ (from_eq h34 h56 (to_eq h34 h56 Logic.eq_refl)) Logic.eq_refl) as Hirr.
    destruct Hirr.
    apply IsomorphismDefinitions.eq_refl.
Qed.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.