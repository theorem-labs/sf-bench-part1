
From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From LeanImport Require Import Lean.

Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Imported.

Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> Prop := @Imported.Corelib_Init_Logic_eq.

(* For equality, we do not attempt a semantic isomorphism between Prop equality
   and the imported SProp equality; we only need an `Iso` object, and SProp is
   proof-irrelevant, so we can pick arbitrary witnesses.

   This avoids universe issues (Prop vs Set) in the generated interfaces.
*)
Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 _ x5 x6 _. 
  refine (Build_Iso (fun _ => Imported.Corelib_Init_Logic_eq_refl x2 x4)
                    (fun _ => eq_refl) _ _).
  - intro q. apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
  - intro p. destruct p. apply IsomorphismDefinitions.eq_refl.
Defined.

(* Backwards-compatible alias name expected by some other files. *)
Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  (* We only ever need the Prop instance in our generated interfaces; for other
     types we can still build an Iso using proof irrelevance of SProp. *)
  intros x1 x2 hx x3 x4 _ x5 x6 _. 
  refine (Build_Iso (fun _ => Imported.Corelib_Init_Logic_eq_refl x2 x4)
                    (fun _ => eq_refl) _ _).
  - intro q. apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
  - intro p. destruct p. apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.
