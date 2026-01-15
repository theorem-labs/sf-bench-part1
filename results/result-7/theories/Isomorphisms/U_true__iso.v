From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
From Stdlib.Logic Require Import ProofIrrelevance.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)


Definition imported_True : SProp := Imported.True_.

(* Construct the isomorphism between True : Prop and imported_True : SProp directly *)
Instance True_iso : (Iso True imported_True).
Proof.
  refine (@Build_Iso True imported_True 
    (fun _ => Imported.True__intro)
    (fun _ => I)
    _ _).
  - intro x. apply IsomorphismDefinitions.eq_refl.
  - intro x. 
    (* Need to show I = x which is True *)
    apply seq_of_eq.
    apply proof_irrelevance.
Defined.

Instance: KnownConstant True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.True_ := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.True_ True_iso := {}.