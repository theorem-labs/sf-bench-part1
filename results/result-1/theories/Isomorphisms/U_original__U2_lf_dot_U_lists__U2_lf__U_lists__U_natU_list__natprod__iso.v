From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Typeclasses Opaque rel_iso. *)

From IsomorphismChecker Require Export Isomorphisms.nat__iso.

(* Aliases for consistency *)
Definition nat_from_imported := imported_to_nat.
Definition nat_to_from := imported_nat_roundtrip. (* nat_to_imported (imported_to_nat n) = n *)
Definition nat_from_to := nat_roundtrip. (* imported_to_nat (nat_to_imported n) = n *)

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod : Type := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natprod.

(* Map from Original natprod to Imported natprod *)
Definition natprod_to_imported (p : Original.LF_DOT_Lists.LF.Lists.NatList.natprod) 
  : Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natprod :=
  match p with
  | Original.LF_DOT_Lists.LF.Lists.NatList.pair n1 n2 => 
      Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natprod_pair 
        (nat_to_imported n1) (nat_to_imported n2)
  end.

(* Map from Imported natprod to Original natprod *)
Definition natprod_from_imported (p : Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natprod) 
  : Original.LF_DOT_Lists.LF.Lists.NatList.natprod :=
  Original.LF_DOT_Lists.LF.Lists.NatList.pair 
    (nat_from_imported (Imported.Original_LF__DOT__Lists_LF_Lists_NatList_fst p))
    (nat_from_imported (Imported.Original_LF__DOT__Lists_LF_Lists_NatList_snd p)).

Lemma natprod_to_from : forall p : Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natprod,
  natprod_to_imported (natprod_from_imported p) = p.
Proof.
  intro p. destruct p. unfold natprod_from_imported, natprod_to_imported.
  simpl. f_equal; apply nat_to_from.
Qed.

Lemma natprod_from_to : forall p : Original.LF_DOT_Lists.LF.Lists.NatList.natprod,
  natprod_from_imported (natprod_to_imported p) = p.
Proof.
  intro p. destruct p. unfold natprod_from_imported, natprod_to_imported.
  simpl. f_equal; apply nat_from_to.
Qed.

Instance Original_LF__DOT__Lists_LF_Lists_NatList_natprod_iso : Iso Original.LF_DOT_Lists.LF.Lists.NatList.natprod imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod.
Proof.
  apply (Build_Iso natprod_to_imported natprod_from_imported).
  - intro p. apply seq_of_eq. apply natprod_to_from.
  - intro p. apply seq_of_eq. apply natprod_from_to.
Defined.

Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.natprod := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natprod := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.natprod Original_LF__DOT__Lists_LF_Lists_NatList_natprod_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.natprod Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natprod Original_LF__DOT__Lists_LF_Lists_NatList_natprod_iso := {}.
