From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
From Stdlib Require Import ProofIrrelevance.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq.

(* Helper to eliminate imported equality into Type *)
Definition imported_eq_elim_Type {A : Type} {x y : A} 
  (Heq : Imported.Corelib_Init_Logic_eq A x y) 
  (P : A -> Type) (Hx : P x) : P y :=
  Imported.Corelib_Init_Logic_eq_recl A x (fun z _ => P z) Hx y Heq.

(* Build the isomorphism with explicit functions *)
Definition eq_to_imported_eq {x1 x2 : Type} (hx : Iso x1 x2) 
  {x3 : x1} {x4 : x2} (H34 : IsomorphismDefinitions.eq (to hx x3) x4) 
  {x5 : x1} {x6 : x2} (H56 : IsomorphismDefinitions.eq (to hx x5) x6)
  (Heq : @Corelib.Init.Logic.eq x1 x3 x5) : @imported_Corelib_Init_Logic_eq x2 x4 x6.
Proof.
  destruct Heq.
  destruct H34. destruct H56.
  apply Imported.Corelib_Init_Logic_eq_refl.
Defined.

Definition imported_eq_to_eq {x1 x2 : Type} (hx : Iso x1 x2) 
  {x3 : x1} {x4 : x2} (H34 : IsomorphismDefinitions.eq (to hx x3) x4) 
  {x5 : x1} {x6 : x2} (H56 : IsomorphismDefinitions.eq (to hx x5) x6)
  (Heq : @imported_Corelib_Init_Logic_eq x2 x4 x6) : @Corelib.Init.Logic.eq x1 x3 x5.
Proof.
  destruct H34. destruct H56.
  pose proof (from_to hx x3) as Hft3.
  pose proof (from_to hx x5) as Hft5.
  destruct Hft3. destruct Hft5.
  exact (imported_eq_elim_Type Heq (fun z => from hx (to hx x3) = from hx z) Logic.eq_refl).
Defined.

(* Since we need equality in Type but imported gives us SProp, we need to handle this carefully *)
Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  - (* to *)
    exact (eq_to_imported_eq hx H34 H56).
  - (* from *)
    exact (imported_eq_to_eq hx H34 H56).
  - (* to_from - result is in SProp *)
    intro Heq.
    exact IsomorphismDefinitions.eq_refl.
  - (* from_to - need to show from (to Heq) = Heq for equality in Prop *)
    intro Heq.
    (* Use proof irrelevance: two proofs of the same Prop are equal *)
    (* First convert to standard equality using proof_irrelevance *)
    apply seq_of_eq.
    apply proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.

(* Re-export from U_prop file so that checker can access *)
From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso__U_prop.
