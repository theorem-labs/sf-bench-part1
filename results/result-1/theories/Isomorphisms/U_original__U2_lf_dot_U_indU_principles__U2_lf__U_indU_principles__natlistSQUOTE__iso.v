From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Monomorphic Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist' : Type := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'.

Fixpoint natlist'_to (l : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist') : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist' :=
  match l with
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.nnil' => Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_nnil'
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.nsnoc l' n => 
      Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_nsnoc (natlist'_to l') (nat_to_imported n)
  end.

Fixpoint natlist'_from (l : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist') : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist' :=
  match l with
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_nnil' => Original.LF_DOT_IndPrinciples.LF.IndPrinciples.nnil'
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_nsnoc l' n => 
      Original.LF_DOT_IndPrinciples.LF.IndPrinciples.nsnoc (natlist'_from l') (imported_to_nat n)
  end.

Lemma natlist'_to_from : forall x, IsomorphismDefinitions.eq (natlist'_to (natlist'_from x)) x.
Proof.
  intro x. induction x as [|l' n IH] using Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_indl; simpl.
  - exact IsomorphismDefinitions.eq_refl.
  - apply (f_equal2 Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_nsnoc).
    + exact IH.
    + apply seq_of_eq. apply imported_nat_roundtrip.
Defined.

Lemma natlist'_from_to : forall x, IsomorphismDefinitions.eq (natlist'_from (natlist'_to x)) x.
Proof.
  intro x. induction x as [|l' IH n]; simpl.
  - exact IsomorphismDefinitions.eq_refl.
  - apply (f_equal2 Original.LF_DOT_IndPrinciples.LF.IndPrinciples.nsnoc).
    + exact IH.
    + apply seq_of_eq. apply nat_roundtrip.
Defined.

Monomorphic Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_iso : Iso Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist' imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'.
Proof.
  exact {| to := natlist'_to; from := natlist'_from; to_from := natlist'_to_from; from_to := natlist'_from_to |}.
Defined.
Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist' Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist' Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist' Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_iso := {}.