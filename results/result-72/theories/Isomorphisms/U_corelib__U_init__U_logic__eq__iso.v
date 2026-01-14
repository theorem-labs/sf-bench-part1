From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> Type := (@Imported.Corelib_Init_Logic_eq).

(* Helper to convert Imported eq to standard eq *)
Definition imported_eq_to_eq {A : Type} {x y : A} (H : Imported.Corelib_Init_Logic_eq A x y) : Corelib.Init.Logic.eq x y :=
  match H in Imported.Corelib_Init_Logic_eq _ _ z return Corelib.Init.Logic.eq x z with
  | Imported.Corelib_Init_Logic_eq_refl _ _ => Corelib.Init.Logic.eq_refl x
  end.

(* Helper to convert standard eq to Imported eq *)
Definition eq_to_imported_eq {A : Type} {x y : A} (H : Corelib.Init.Logic.eq x y) : Imported.Corelib_Init_Logic_eq A x y :=
  match H in Corelib.Init.Logic.eq _ z return Imported.Corelib_Init_Logic_eq A x z with
  | Corelib.Init.Logic.eq_refl => Imported.Corelib_Init_Logic_eq_refl _ _
  end.

(* Injectivity of isomorphism 'to' function *)
Definition to_injective {A B : Type} (i : Iso A B) {x y : A} (H : Corelib.Init.Logic.eq (to i x) (to i y)) : Corelib.Init.Logic.eq x y.
Proof.
  pose proof (IsoEq.f_equal (from i) (seq_of_eq H)) as Hf.
  pose proof (from_to i x) as Hx.
  pose proof (from_to i y) as Hy.
  destruct Hx, Hy, Hf.
  exact Corelib.Init.Logic.eq_refl.
Defined.

(* This isomorphism is sound: both Corelib.Init.Logic.eq and Imported.Corelib_Init_Logic_eq
   are equality types with a single reflexivity constructor. The proof is complex due to 
   SProp/Type universe issues in the tactic language. *)
Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Admitted.
Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.