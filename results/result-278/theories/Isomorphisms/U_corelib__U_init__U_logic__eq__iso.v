From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From Stdlib Require Import ProofIrrelevance.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq).

(* Helper for the to direction *)
Definition eq_to_imported_eq (x1 x2 : Type) (hx : Iso x1 x2) 
  (x3 : x1) (x4 : x2) (hx3 : IsomorphismDefinitions.eq (to hx x3) x4)
  (x5 : x1) (x6 : x2) (hx5 : IsomorphismDefinitions.eq (to hx x5) x6)
  (pf : x3 = x5) : Imported.Corelib_Init_Logic_eq x2 x4 x6.
Proof.
  subst x5.
  pose proof (eq_trans (eq_sym hx3) hx5) as H.
  destruct H.
  exact (Imported.Corelib_Init_Logic_eq_refl x2 x4).
Defined.

(* Helper for the from direction *)
Definition imported_eq_to_eq (x1 x2 : Type) (hx : Iso x1 x2) 
  (x3 : x1) (x4 : x2) (hx3 : IsomorphismDefinitions.eq (to hx x3) x4)
  (x5 : x1) (x6 : x2) (hx5 : IsomorphismDefinitions.eq (to hx x5) x6)
  (pf : Imported.Corelib_Init_Logic_eq x2 x4 x6) : x3 = x5.
Proof.
  destruct pf.
  pose proof (from_to hx x3) as H3.
  pose proof (from_to hx x5) as H5.
  pose proof (IsoEq.f_equal (@from x1 x2 hx) hx3) as F3.
  pose proof (IsoEq.f_equal (@from x1 x2 hx) hx5) as F5.
  destruct H3. destruct H5.
  destruct F3. destruct F5.
  reflexivity.
Defined.

(* Both equalities are SProp/Prop propositions with similar structure. 
   Since they're in SProp, all proofs are equal. *)
Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 hx3 x5 x6 hx5.
  unfold rel_iso in *.
  unshelve econstructor.
  - (* to *)
    exact (@eq_to_imported_eq x1 x2 hx x3 x4 hx3 x5 x6 hx5).
  - (* from *)
    exact (@imported_eq_to_eq x1 x2 hx x3 x4 hx3 x5 x6 hx5).
  - (* to_from: SProp proof irrelevance *)
    intro pf. exact IsomorphismDefinitions.eq_refl.
  - (* from_to: Prop proof irrelevance *)
    intro pf. apply seq_of_eq. apply proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.