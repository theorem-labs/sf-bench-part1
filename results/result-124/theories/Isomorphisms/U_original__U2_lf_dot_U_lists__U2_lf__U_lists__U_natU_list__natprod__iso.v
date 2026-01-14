From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
From IsomorphismChecker Require Isomorphisms.nat__iso.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod : Type := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natprod.

(* Convert original natprod to imported *)
Definition natprod_to_lean (p : Original.LF_DOT_Lists.LF.Lists.NatList.natprod) : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod :=
  match p with
  | Original.LF_DOT_Lists.LF.Lists.NatList.pair n1 n2 =>
      Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natprod_pair 
        (Isomorphisms.nat__iso.nat_to_lean n1) 
        (Isomorphisms.nat__iso.nat_to_lean n2)
  end.

(* Convert imported natprod to original *)
Definition lean_to_natprod (p : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod) : Original.LF_DOT_Lists.LF.Lists.NatList.natprod :=
  Original.LF_DOT_Lists.LF.Lists.NatList.pair 
    (Isomorphisms.nat__iso.lean_to_nat (Imported.a____at___U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__sndSQUOTE__iso__hyg9 p))
    (Isomorphisms.nat__iso.lean_to_nat (Imported.a____at___U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__sndSQUOTE__iso__hyg11 p)).

Lemma natprod_roundtrip1 : forall p : Original.LF_DOT_Lists.LF.Lists.NatList.natprod, 
    IsomorphismDefinitions.eq (lean_to_natprod (natprod_to_lean p)) p.
Proof.
  intros [n1 n2]. simpl.
  apply (IsoEq.f_equal2 Original.LF_DOT_Lists.LF.Lists.NatList.pair).
  - apply Isomorphisms.nat__iso.nat_roundtrip1.
  - apply Isomorphisms.nat__iso.nat_roundtrip1.
Qed.

Lemma natprod_roundtrip2 : forall p : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod, 
    IsomorphismDefinitions.eq (natprod_to_lean (lean_to_natprod p)) p.
Proof.
  intros p. destruct p as [n1 n2]. simpl.
  apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natprod_pair).
  - apply Isomorphisms.nat__iso.nat_roundtrip2.
  - apply Isomorphisms.nat__iso.nat_roundtrip2.
Qed.

Instance Original_LF__DOT__Lists_LF_Lists_NatList_natprod_iso : Iso Original.LF_DOT_Lists.LF.Lists.NatList.natprod imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod.
Proof.
  apply (Build_Iso (A:=Original.LF_DOT_Lists.LF.Lists.NatList.natprod) (B:=imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod) natprod_to_lean lean_to_natprod).
  - intro x. apply natprod_roundtrip2.
  - intro x. apply natprod_roundtrip1.
Defined.

Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.natprod := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natprod := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.natprod Original_LF__DOT__Lists_LF_Lists_NatList_natprod_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.natprod Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natprod Original_LF__DOT__Lists_LF_Lists_NatList_natprod_iso := {}.