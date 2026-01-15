From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__even__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Isomorphisms.U_s__iso Isomorphisms.U_nat__mul__iso.

(* 1000 = 100 * 10 where 10 = S^10 O and 100 = 10*10 *)
Definition imported_nat1000 : imported_nat := Imported.nat1000.

Monomorphic Definition imported_Original_LF__DOT__Logic_LF_Logic_even__1000' : Imported.Corelib_Init_Logic_eq Imported.Original_LF__DOT__Basics_LF_Basics_bool (Imported.Original_LF__DOT__Basics_LF_Basics_even imported_nat1000)
    imported_Original_LF__DOT__Basics_LF_Basics_true := Imported.Original_LF__DOT__Logic_LF_Logic_even__1000'.

Monomorphic Instance Original_LF__DOT__Logic_LF_Logic_even__1000'_iso : rel_iso
    (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_even_iso (Nat_mul_iso (Nat_mul_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))))) (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))))))) (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))))))))
       Original_LF__DOT__Basics_LF_Basics_true_iso)
    Original.LF_DOT_Logic.LF.Logic.even_1000' imported_Original_LF__DOT__Logic_LF_Logic_even__1000'.
Proof.
  constructor.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.even_1000' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_even__1000' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.even_1000' Original_LF__DOT__Logic_LF_Logic_even__1000'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.even_1000' Imported.Original_LF__DOT__Logic_LF_Logic_even__1000' Original_LF__DOT__Logic_LF_Logic_even__1000'_iso := {}.