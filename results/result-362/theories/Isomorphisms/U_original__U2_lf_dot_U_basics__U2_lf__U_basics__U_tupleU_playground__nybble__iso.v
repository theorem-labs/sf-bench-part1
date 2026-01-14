From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_tupleU_playground__bit__iso.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Definition imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble : Type := Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble.

(* Import the bit conversion functions *)
Definition bit_to := Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_tupleU_playground__bit__iso.bit_to_imported.
Definition bit_from := Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_tupleU_playground__bit__iso.bit_from_imported.

Definition nybble_to_imported (n : Original.LF_DOT_Basics.LF.Basics.TuplePlayground.nybble) : imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble :=
  match n with
  | Original.LF_DOT_Basics.LF.Basics.TuplePlayground.bits b0 b1 b2 b3 =>
      Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble_bits
        (bit_to b0) (bit_to b1) (bit_to b2) (bit_to b3)
  end.

Definition nybble_from_imported (n : imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble) : Original.LF_DOT_Basics.LF.Basics.TuplePlayground.nybble :=
  Original.LF_DOT_Basics.LF.Basics.TuplePlayground.bits
    (bit_from (Imported.a____at___U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_tupleU_playground__all____zero__iso__hyg29 n))
    (bit_from (Imported.a____at___U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_tupleU_playground__all____zero__iso__hyg31 n))
    (bit_from (Imported.a____at___U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_tupleU_playground__all____zero__iso__hyg33 n))
    (bit_from (Imported.a____at___U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_tupleU_playground__all____zero__iso__hyg35 n)).

Lemma nybble_to_from : forall x : imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble,
  IsomorphismDefinitions.eq (nybble_to_imported (nybble_from_imported x)) x.
Proof.
  intro x. unfold nybble_to_imported, nybble_from_imported, bit_to, bit_from.
  destruct x as [b0 b1 b2 b3].
  simpl.
  destruct b0, b1, b2, b3; apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma nybble_from_to : forall x : Original.LF_DOT_Basics.LF.Basics.TuplePlayground.nybble,
  IsomorphismDefinitions.eq (nybble_from_imported (nybble_to_imported x)) x.
Proof.
  intro x. unfold nybble_to_imported, nybble_from_imported, bit_to, bit_from.
  destruct x as [b0 b1 b2 b3].
  simpl.
  destruct b0, b1, b2, b3; apply IsomorphismDefinitions.eq_refl.
Qed.

Instance Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble_iso : Iso Original.LF_DOT_Basics.LF.Basics.TuplePlayground.nybble imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble :=
  Build_Iso nybble_to_imported nybble_from_imported nybble_to_from nybble_from_to.

Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.TuplePlayground.nybble := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.TuplePlayground.nybble Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.TuplePlayground.nybble Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble_iso := {}.