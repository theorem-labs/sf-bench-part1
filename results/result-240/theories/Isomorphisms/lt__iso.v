From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From Stdlib.Logic Require Import Classical_Prop.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_lt : imported_nat -> imported_nat -> SProp := Imported.lt.

(* Convert Peano.le to Imported.le *)
Fixpoint le_to_imported (n m : Datatypes.nat) (p : Peano.le n m) {struct p} : Imported.le (nat_to_imported n) (nat_to_imported m).
Proof.
  destruct p.
  - exact (Imported.le_le_n (nat_to_imported n)).
  - exact (Imported.le_le_S (nat_to_imported n) (nat_to_imported m) (le_to_imported n m p)).
Defined.

(* Use le_sind to eliminate the SProp to SProp *)
Definition le_to_sinhabited' (n : Imported.nat) : forall m : Imported.nat, 
  Imported.le n m -> SInhabited (Peano.le (imported_to_nat n) (imported_to_nat m)).
Proof.
  apply Imported.le_sind.
  { apply sinhabits. apply Peano.le_n. }
  { intros m _ IH.
    simpl.
    apply sinhabits.
    apply Peano.le_S.
    apply sinhabitant.
    exact IH. }
Defined.

(* Now we can define le_from_imported without admitting *)
Definition le_from_imported (n m : Datatypes.nat) 
  (p : Imported.le (nat_to_imported n) (nat_to_imported m)) : Peano.le n m.
Proof.
  apply sinhabitant.
  pose proof (@le_to_sinhabited' (nat_to_imported n) (nat_to_imported m) p) as H.
  simpl in H.
  rewrite nat_round_trip in H.
  rewrite nat_round_trip in H.
  exact H.
Defined.

Instance lt_iso : (forall (x1 : Datatypes.nat) (x2 : imported_nat) (h1 : @rel_iso Datatypes.nat imported_nat nat_iso x1 x2) (x3 : Datatypes.nat) (x4 : imported_nat) (h2 : @rel_iso Datatypes.nat imported_nat nat_iso x3 x4), Iso (Peano.lt x1 x3) (imported_lt x2 x4)).
Proof.
  intros x1 x2 h1 x3 x4 h2.
  unfold rel_iso in h1, h2. simpl in h1, h2.
  unfold Peano.lt, imported_lt, Imported.lt.
  unshelve eapply Build_Iso.
  - (* to : (S x1 <= x3) -> Imported.le (Imported.nat_S x2) x4 *)
    intro p.
    pose proof (@le_to_imported (S x1) x3 p) as q.
    pose proof (f_equal Imported.nat_S h1) as h1'.
    exact (eq_srect_nodep (fun a => Imported.le a x4) (eq_srect_nodep (Imported.le (Imported.nat_S (nat_to_imported x1))) q h2) h1').
  - (* from : Imported.le (Imported.nat_S x2) x4 -> (S x1 <= x3) *)
    intro p.
    pose proof (f_equal Imported.nat_S h1) as h1'.
    pose proof (eq_srect_nodep (fun a => Imported.le a (nat_to_imported x3)) 
                               (eq_srect_nodep (Imported.le (Imported.nat_S x2)) p (eq_sym h2)) 
                               (eq_sym h1')) as q.
    exact (@le_from_imported (S x1) x3 q).
  - (* to_from : forall x, eq (to (from x)) x -- x is in SProp so eq_refl works *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to : forall x, eq (from (to x)) x -- x is in Prop, use proof irrelevance *)
    intro x. 
    (* Since both sides are proofs of the same Prop (S x1 <= x3), they're equal by proof irrelevance *)
    apply seq_of_peq_t.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.
Instance: KnownConstant lt := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.lt := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor lt lt_iso := {}.
Instance: IsoStatementProofBetween lt Imported.lt lt_iso := {}.