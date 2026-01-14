From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r' : imported_nat -> SProp := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r'.

(* The original is Prop, the imported is SProp *)
(* Use the fact that n * 0 = 0 is provable *)

Lemma mul_0_r_original : forall n : Datatypes.nat, PeanoNat.Nat.mul n Datatypes.O = Datatypes.O.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. exact IHn'.
Qed.

(* The imported definition is: fun _ => myeq nat nat_O nat_O
   which is always inhabited by myeq_refl nat nat_O *)
Definition imported_P_m0r'_proof : forall n : Imported.nat, Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r' n :=
  fun _ => Imported.myeq_refl Imported.nat Imported.nat_O.

Require Import Stdlib.Logic.ProofIrrelevance.

Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r'_iso : forall (x1 : Datatypes.nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> Iso (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.P_m0r' x1) (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r' x2).
Proof.
  intros x1 x2 Hrel.
  unfold Original.LF_DOT_IndPrinciples.LF.IndPrinciples.P_m0r'.
  unfold imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r'.
  unfold Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r'.
  (* The original is: x1 * 0 = 0 (Prop)
     The imported is: Imported.myeq Imported.nat Imported.nat_O Imported.nat_O (SProp) *)
  (* Both are inhabited propositions (SProp/Prop), we can build the Iso directly *)
  apply Build_Iso with (to := fun _ => Imported.myeq_refl Imported.nat Imported.nat_O) (from := fun _ => mul_0_r_original x1).
  - intro. apply IsomorphismDefinitions.eq_refl.
  - intro x. 
    (* Need to show: mul_0_r_original x1 = x in SProp eq *)
    (* Use proof irrelevance: any two proofs of the same Prop are equal *)
    apply seq_of_eq.
    apply proof_irrelevance.
Defined.
Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.P_m0r' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.P_m0r' Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.P_m0r' Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r' Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r'_iso := {}.