From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
From Stdlib.Logic Require Import ProofIrrelevance.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq).

(* Build the isomorphism between eq (Prop) and imported_Corelib_Init_Logic_eq (SProp) *)
(* Since both are proposition-like types (Prop and SProp), we use proof irrelevance *)

(* Helper: transport along rel_iso to get imported equality from std equality *)
Definition eq_to_imported_eq {x1 x2 : Type} (hx : Iso x1 x2) 
  (x3 : x1) (x4 : x2) (h34 : @rel_iso x1 x2 hx x3 x4) 
  (x5 : x1) (x6 : x2) (h56 : @rel_iso x1 x2 hx x5 x6)
  (H : @Corelib.Init.Logic.eq x1 x3 x5) : @imported_Corelib_Init_Logic_eq x2 x4 x6.
Proof.
  destruct H.
  unfold rel_iso in h34, h56. simpl in h34, h56.
  pose proof (eq_trans (eq_sym h34) h56) as Heq.
  destruct (eq_of_seq Heq).
  exact (Imported.Corelib_Init_Logic_eq_refl _ _).
Defined.

(* Helper: transport from imported equality to std equality *)
Definition imported_eq_to_eq {x1 x2 : Type} (hx : Iso x1 x2) 
  (x3 : x1) (x4 : x2) (h34 : @rel_iso x1 x2 hx x3 x4) 
  (x5 : x1) (x6 : x2) (h56 : @rel_iso x1 x2 hx x5 x6)
  (H : @imported_Corelib_Init_Logic_eq x2 x4 x6) : @Corelib.Init.Logic.eq x1 x3 x5.
Proof.
  destruct H.
  unfold rel_iso in h34, h56. simpl in h34, h56.
  pose proof (eq_trans h34 (eq_sym h56)) as Heq.
  pose proof (f_equal (from hx) Heq) as Heq'.
  pose proof (eq_trans (eq_sym (from_to hx x3)) (eq_trans Heq' (from_to hx x5))) as Heq''.
  destruct (eq_of_seq Heq'').
  exact Corelib.Init.Logic.eq_refl.
Defined.

Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 h34 x5 x6 h56.
  refine {|
    to := @eq_to_imported_eq x1 x2 hx x3 x4 h34 x5 x6 h56;
    from := @imported_eq_to_eq x1 x2 hx x3 x4 h34 x5 x6 h56;
    to_from := _;
    from_to := _
  |}.
  - (* to_from: forall x : imported_eq, eq (to (from x)) x in SProp - trivial by SProp proof irrelevance *)
    intro pf. exact IsomorphismDefinitions.eq_refl.
  - (* from_to: forall x : Prop_eq, eq (from (to x)) x in SProp *)
    (* Need to show eq (imported_eq_to_eq (eq_to_imported_eq pf)) pf *)
    (* Both are proofs of x3 = x5 in Prop, so by proof irrelevance they're equal *)
    intro pf. 
    apply seq_of_eq.
    apply proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.