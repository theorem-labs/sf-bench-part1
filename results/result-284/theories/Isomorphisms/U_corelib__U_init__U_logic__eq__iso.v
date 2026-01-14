From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib.Logic Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq).

(* Helper function to build the 'to' direction *)
Definition eq_to_imported_eq {x1 x2 : Type} (hx : Iso x1 x2) 
  (x3 : x1) (x4 : x2) (h34 : rel_iso hx x3 x4)
  (x5 : x1) (x6 : x2) (h56 : rel_iso hx x5 x6)
  (H : @Corelib.Init.Logic.eq x1 x3 x5) : Imported.Corelib_Init_Logic_eq x2 x4 x6.
Proof.
  destruct H.
  unfold rel_iso in h34, h56. simpl in h34, h56.
  rewrite <- (eq_of_seq h34), <- (eq_of_seq h56).
  exact (Imported.Corelib_Init_Logic_eq_refl x2 (to hx x3)).
Defined.

(* Helper function to build the 'from' direction *)
Definition imported_eq_to_eq {x1 x2 : Type} (hx : Iso x1 x2) 
  (x3 : x1) (x4 : x2) (h34 : rel_iso hx x3 x4)
  (x5 : x1) (x6 : x2) (h56 : rel_iso hx x5 x6)
  (H : Imported.Corelib_Init_Logic_eq x2 x4 x6) : @Corelib.Init.Logic.eq x1 x3 x5.
Proof.
  unfold rel_iso in h34, h56. simpl in h34, h56.
  pose proof (eq_of_seq h34) as H34.
  pose proof (eq_of_seq h56) as H56.
  pose proof (eq_of_seq (from_to hx x3)) as FT3.
  pose proof (eq_of_seq (from_to hx x5)) as FT5.
  rewrite <- FT3, <- FT5.
  apply Corelib.Init.Logic.f_equal.
  destruct H using Imported.Corelib_Init_Logic_eq_recl.
  transitivity x4; [exact H34 | symmetry; exact H56].
Defined.

(* Build the isomorphism for eq *)
Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 h34 x5 x6 h56.
  unshelve econstructor.
  - exact (@eq_to_imported_eq x1 x2 hx x3 x4 h34 x5 x6 h56).
  - exact (@imported_eq_to_eq x1 x2 hx x3 x4 h34 x5 x6 h56).
  - (* to_from: to (from x) = x, in SProp, so trivial *)
    intro. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: from (to x) = x -- need proof irrelevance for Prop eq *)
    intro x.
    (* Both sides are proofs of x3 = x5 in Prop, use proof irrelevance *)
    apply seq_of_eq.
    apply proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.

(* Re-export the Prop version *)
From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso__U_prop.