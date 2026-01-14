From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* First, we need an isomorphism between standard nat and Imported.nat *)
Fixpoint nat_to_imported (n : nat) : Imported.nat :=
  match n with
  | O => Imported.nat_O
  | S n' => Imported.nat_S (nat_to_imported n')
  end.

Fixpoint imported_to_nat (n : Imported.nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S n' => S (imported_to_nat n')
  end.

Lemma nat_iso_roundtrip1 : forall n, imported_to_nat (nat_to_imported n) = n.
Proof.
  induction n; simpl; auto.
Qed.

Lemma nat_iso_roundtrip2 : forall n, nat_to_imported (imported_to_nat n) = n.
Proof.
  fix IH 1.
  intro n. destruct n; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

(* Now define the isomorphism for natlist' *)
Fixpoint natlist'_to_imported (l : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist') 
  : Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist' :=
  match l with
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.nnil' => 
      Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_nnil'
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.nsnoc l' n => 
      Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_nsnoc 
        (natlist'_to_imported l') 
        (nat_to_imported n)
  end.

Fixpoint imported_to_natlist' (l : Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist') 
  : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist' :=
  match l with
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_nnil' => 
      Original.LF_DOT_IndPrinciples.LF.IndPrinciples.nnil'
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_nsnoc l' n => 
      Original.LF_DOT_IndPrinciples.LF.IndPrinciples.nsnoc 
        (imported_to_natlist' l') 
        (imported_to_nat n)
  end.

Lemma natlist'_iso_roundtrip1 : forall l, imported_to_natlist' (natlist'_to_imported l) = l.
Proof.
  induction l; simpl.
  - reflexivity.
  - f_equal; [apply IHl | apply nat_iso_roundtrip1].
Qed.

Lemma natlist'_iso_roundtrip2 : forall l, natlist'_to_imported (imported_to_natlist' l) = l.
Proof.
  fix IH 1.
  intro l. destruct l; simpl.
  - reflexivity.
  - f_equal; [apply IH | apply nat_iso_roundtrip2].
Qed.

Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist' : Type := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'.

(* We need to convert the standard equality proofs to IsomorphismDefinitions.eq *)
Lemma natlist'_to_from : forall x, IsomorphismDefinitions.eq (natlist'_to_imported (imported_to_natlist' x)) x.
Proof.
  intro x.
  rewrite natlist'_iso_roundtrip2.
  apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma natlist'_from_to : forall x, IsomorphismDefinitions.eq (imported_to_natlist' (natlist'_to_imported x)) x.
Proof.
  intro x.
  rewrite natlist'_iso_roundtrip1.
  apply IsomorphismDefinitions.eq_refl.
Qed.

Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_iso : Iso Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist' imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'.
Proof.
  exact {|
    to := natlist'_to_imported;
    from := imported_to_natlist';
    to_from := natlist'_to_from;
    from_to := natlist'_from_to
  |}.
Defined.

Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist' Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist' Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist' Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_iso := {}.