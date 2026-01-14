From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

(* Build iso between Coq nat and Imported.nat *)
Fixpoint nat_to_imported (n : nat) : Imported.nat :=
  match n with
  | O => Imported.nat_zero
  | S n' => Imported.nat_succ (nat_to_imported n')
  end.

Fixpoint imported_to_nat (n : Imported.nat) : nat :=
  match n with
  | Imported.nat_zero => O
  | Imported.nat_succ n' => S (imported_to_nat n')
  end.

(* Proof using Imported.nat_rect - using explicit Corelib.Init.Logic.eq (Prop) *)
Definition nat_to_from : forall n, @Corelib.Init.Logic.eq _ (nat_to_imported (imported_to_nat n)) n :=
  Imported.nat_rect 
    (fun n => @Corelib.Init.Logic.eq _ (nat_to_imported (imported_to_nat n)) n)
    (@Corelib.Init.Logic.eq_refl _ _)
    (fun n' (IHn : @Corelib.Init.Logic.eq _ (nat_to_imported (imported_to_nat n')) n') =>
       @Corelib.Init.Logic.eq_ind_r _ n' (fun x => @Corelib.Init.Logic.eq _ (Imported.nat_succ x) (Imported.nat_succ n')) 
         (@Corelib.Init.Logic.eq_refl _ _) _ IHn).

Definition nat_from_to : forall n, @Corelib.Init.Logic.eq _ (imported_to_nat (nat_to_imported n)) n :=
  nat_rect 
    (fun n => @Corelib.Init.Logic.eq _ (imported_to_nat (nat_to_imported n)) n)
    (@Corelib.Init.Logic.eq_refl _ _)
    (fun n' (IHn : @Corelib.Init.Logic.eq _ (imported_to_nat (nat_to_imported n')) n') =>
       @Corelib.Init.Logic.eq_ind_r _ n' (fun x => @Corelib.Init.Logic.eq _ (S x) (S n')) 
         (@Corelib.Init.Logic.eq_refl _ _) _ IHn).

Instance nat_iso : Iso nat imported_nat.
Proof.
  refine (Build_Iso nat_to_imported imported_to_nat _ _).
  - intro n. apply seq_of_eq. apply nat_to_from.
  - intro n. apply seq_of_eq. apply nat_from_to.
Defined.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.