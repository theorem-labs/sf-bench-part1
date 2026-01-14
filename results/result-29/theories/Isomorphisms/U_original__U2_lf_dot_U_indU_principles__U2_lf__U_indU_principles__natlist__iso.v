From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Use IsomorphismDefinitions.eq as = in type_scope *)
#[local] Notation "x = y" := (IsomorphismDefinitions.eq x y) : type_scope.

(* First, we need an isomorphism between nat and Lean.Nat *)
Fixpoint nat_to_Lean_Nat (n : nat) : Lean.Nat :=
  match n with
  | O => Lean.Nat_zero
  | S m => Lean.Nat_succ (nat_to_Lean_Nat m)
  end.

Fixpoint Lean_Nat_to_nat (n : Lean.Nat) : nat :=
  match n with
  | Lean.Nat_zero => O
  | Lean.Nat_succ m => S (Lean_Nat_to_nat m)
  end.

Lemma nat_to_from : forall x, nat_to_Lean_Nat (Lean_Nat_to_nat x) = x.
Proof.
  fix IH 1.
  destruct x; simpl.
  - exact IsomorphismDefinitions.eq_refl.
  - exact (f_equal _ (IH x)).
Qed.

Lemma nat_from_to : forall x, Lean_Nat_to_nat (nat_to_Lean_Nat x) = x.
Proof.
  fix IH 1.
  destruct x; simpl.
  - exact IsomorphismDefinitions.eq_refl.
  - exact (f_equal _ (IH x)).
Qed.

Definition nat_Lean_Nat_iso : Iso nat Lean.Nat :=
  {| to := nat_to_Lean_Nat;
     from := Lean_Nat_to_nat;
     to_from := nat_to_from;
     from_to := nat_from_to |}.

(* Imported.nat = Lean.Nat *)
Definition nat_imported_nat_iso : Iso nat Imported.nat := nat_Lean_Nat_iso.

(* Now we define the isomorphism for natlist *)
Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist : Type := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist.

Fixpoint natlist_to (l : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist) : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist :=
  match l with
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.nnil => Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist_nnil
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.ncons n rest => 
      Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist_ncons (nat_to_Lean_Nat n) (natlist_to rest)
  end.

Fixpoint natlist_from (l : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist) : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist :=
  match l with
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist_nnil => Original.LF_DOT_IndPrinciples.LF.IndPrinciples.nnil
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist_ncons n rest => 
      Original.LF_DOT_IndPrinciples.LF.IndPrinciples.ncons (Lean_Nat_to_nat n) (natlist_from rest)
  end.

Lemma natlist_to_from : forall x, natlist_to (natlist_from x) = x.
Proof.
  fix IH 1.
  destruct x as [| n l]; simpl.
  - exact IsomorphismDefinitions.eq_refl.
  - exact (f_equal2 _ (nat_to_from n) (IH l)).
Qed.

Lemma natlist_from_to : forall x, natlist_from (natlist_to x) = x.
Proof.
  fix IH 1.
  destruct x as [| n l]; simpl.
  - exact IsomorphismDefinitions.eq_refl.
  - exact (f_equal2 _ (nat_from_to n) (IH l)).
Qed.

Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist_iso : Iso Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist :=
  {| to := natlist_to;
     from := natlist_from;
     to_from := natlist_to_from;
     from_to := natlist_from_to |}.

Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist_iso := {}.