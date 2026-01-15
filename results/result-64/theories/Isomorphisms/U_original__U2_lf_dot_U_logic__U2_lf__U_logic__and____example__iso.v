From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_nat__mul__iso Isomorphisms.U_s__iso Isomorphisms.and__iso.

(* Define imported nat values *)
Definition nat_2 : Datatypes.nat := 2.
Definition nat_2_imported : imported_nat := nat_to_imported nat_2.
Definition nat_3 : Datatypes.nat := 3.
Definition nat_3_imported : imported_nat := nat_to_imported nat_3.
Definition nat_4 : Datatypes.nat := 4.
Definition nat_4_imported : imported_nat := nat_to_imported nat_4.
Definition nat_7 : Datatypes.nat := 7.
Definition nat_7_imported : imported_nat := nat_to_imported nat_7.

Lemma nat_2_rel : rel_iso nat_iso nat_2 nat_2_imported.
Proof. constructor. reflexivity. Defined.
Lemma nat_3_rel : rel_iso nat_iso nat_3 nat_3_imported.
Proof. constructor. reflexivity. Defined.
Lemma nat_4_rel : rel_iso nat_iso nat_4 nat_4_imported.
Proof. constructor. reflexivity. Defined.
Lemma nat_7_rel : rel_iso nat_iso nat_7 nat_7_imported.
Proof. constructor. reflexivity. Defined.

(* and_example : 3 + 4 = 7 /\ 2 * 2 = 4 *)
Monomorphic Definition imported_Original_LF__DOT__Logic_LF_Logic_and__example : imported_and
    (imported_Corelib_Init_Logic_eq (imported_Nat_add nat_3_imported nat_4_imported) nat_7_imported)
    (imported_Corelib_Init_Logic_eq (imported_Nat_mul nat_2_imported nat_2_imported) nat_4_imported) := Imported.Original_LF__DOT__Logic_LF_Logic_and__example.

Monomorphic Instance Original_LF__DOT__Logic_LF_Logic_and__example_iso : rel_iso
    (relax_Iso_Ts_Ps
       (and_iso
          (Corelib_Init_Logic_eq_iso (Nat_add_iso nat_3_rel nat_4_rel) nat_7_rel)
          (Corelib_Init_Logic_eq_iso (Nat_mul_iso nat_2_rel nat_2_rel) nat_4_rel)))
    Original.LF_DOT_Logic.LF.Logic.and_example imported_Original_LF__DOT__Logic_LF_Logic_and__example.
Admitted.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.and_example := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_and__example := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.and_example Original_LF__DOT__Logic_LF_Logic_and__example_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.and_example Imported.Original_LF__DOT__Logic_LF_Logic_and__example Original_LF__DOT__Logic_LF_Logic_and__example_iso := {}.
