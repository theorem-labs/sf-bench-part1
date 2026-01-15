From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__even__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Isomorphisms.U_s__iso Isomorphisms.U_nat__mul__iso.

(* nat1001 = S nat1000 = S (100 * 10) *)
Definition imported_nat1001 : imported_nat := Imported.nat1001.

Monomorphic Definition imported_Original_LF__DOT__Logic_LF_Logic_not__even__1001 : Imported.Corelib_Init_Logic_eq Imported.Original_LF__DOT__Basics_LF_Basics_bool (Imported.Original_LF__DOT__Basics_LF_Basics_even imported_nat1001)
    imported_Original_LF__DOT__Basics_LF_Basics_false := Imported.Original_LF__DOT__Logic_LF_Logic_not__even__1001.

Monomorphic Instance Original_LF__DOT__Logic_LF_Logic_not__even__1001_iso : rel_iso
    (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_even_iso (S_iso (Nat_mul_iso (Nat_mul_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))))) (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))))))) (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))))))))
       Original_LF__DOT__Basics_LF_Basics_false_iso)
    Original.LF_DOT_Logic.LF.Logic.not_even_1001 imported_Original_LF__DOT__Logic_LF_Logic_not__even__1001.
Proof.
  constructor.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.not_even_1001 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_not__even__1001 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.not_even_1001 Original_LF__DOT__Logic_LF_Logic_not__even__1001_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.not_even_1001 Imported.Original_LF__DOT__Logic_LF_Logic_not__even__1001 Original_LF__DOT__Logic_LF_Logic_not__even__1001_iso := {}.