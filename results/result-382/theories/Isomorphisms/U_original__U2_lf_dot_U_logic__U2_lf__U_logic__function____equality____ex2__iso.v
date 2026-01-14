From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__plus__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_function__equality__ex2 : imported_Corelib_Init_Logic_eq (fun x2 : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_plus x2 (imported_S imported_0))
    (fun x2 : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_plus (imported_S imported_0) x2) := Imported.Original_LF__DOT__Logic_LF_Logic_function__equality__ex2.
Instance Original_LF__DOT__Logic_LF_Logic_function__equality__ex2_iso : @rel_iso ((fun x : nat => Original.LF_DOT_Basics.LF.Basics.plus x 1) = (fun x : nat => Original.LF_DOT_Basics.LF.Basics.plus 1 x))
    (@imported_Corelib_Init_Logic_eq (imported_nat -> imported_nat) (fun x2 : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_plus x2 (imported_S imported_0))
       (fun x2 : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_plus (imported_S imported_0) x2))
    (@relax_Iso_Ts_Ps ((fun x : nat => Original.LF_DOT_Basics.LF.Basics.plus x 1) = (fun x : nat => Original.LF_DOT_Basics.LF.Basics.plus 1 x))
       (@imported_Corelib_Init_Logic_eq (imported_nat -> imported_nat) (fun x2 : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_plus x2 (imported_S imported_0))
          (fun x2 : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_plus (imported_S imported_0) x2))
       (@Corelib_Init_Logic_eq_iso (nat -> nat) (imported_nat -> imported_nat) (@IsoArrow nat imported_nat nat_iso nat imported_nat nat_iso) (fun x : nat => Original.LF_DOT_Basics.LF.Basics.plus x 1)
          (fun x2 : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_plus x2 (imported_S imported_0))
          (@IsoFunND nat imported_nat nat_iso nat imported_nat nat_iso (fun x : nat => Original.LF_DOT_Basics.LF.Basics.plus x 1)
             (fun x2 : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_plus x2 (imported_S imported_0))
             (fun (x1 : nat) (x2 : imported_nat) (hx : @rel_iso nat imported_nat nat_iso x1 x2) =>
              @Original_LF__DOT__Basics_LF_Basics_plus_iso x1 x2 hx 1 (imported_S imported_0) (@S_iso 0 imported_0 _0_iso)))
          (fun x : nat => Original.LF_DOT_Basics.LF.Basics.plus 1 x) (fun x2 : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_plus (imported_S imported_0) x2)
          (@IsoFunND nat imported_nat nat_iso nat imported_nat nat_iso (fun x : nat => Original.LF_DOT_Basics.LF.Basics.plus 1 x)
             (fun x2 : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_plus (imported_S imported_0) x2)
             (fun (x1 : nat) (x2 : imported_nat) (hx : @rel_iso nat imported_nat nat_iso x1 x2) =>
              @Original_LF__DOT__Basics_LF_Basics_plus_iso 1 (imported_S imported_0) (@S_iso 0 imported_0 _0_iso) x1 x2 hx))))
    Original.LF_DOT_Logic.LF.Logic.function_equality_ex2 imported_Original_LF__DOT__Logic_LF_Logic_function__equality__ex2.
Proof.
  unfold relax_Iso_Ts_Ps, rel_iso.
  simpl.
  unfold imported_Original_LF__DOT__Logic_LF_Logic_function__equality__ex2.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.function_equality_ex2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_function__equality__ex2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.function_equality_ex2 Original_LF__DOT__Logic_LF_Logic_function__equality__ex2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.function_equality_ex2 Imported.Original_LF__DOT__Logic_LF_Logic_function__equality__ex2 Original_LF__DOT__Logic_LF_Logic_function__equality__ex2_iso := {}.