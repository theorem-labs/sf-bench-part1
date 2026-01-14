From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso Isomorphisms.U_s__iso.

Lemma n1000_eq : Imported.n1000 = (imported_S (imported_S (imported_S (iterate1 imported_S 997 imported_0)))).
Proof. reflexivity. Qed.

Definition imported_Original_LF__DOT__Logic_LF_Logic_even__1000 : imported_Original_LF__DOT__Logic_LF_Logic_Even (imported_S (imported_S (imported_S (iterate1 imported_S 997 imported_0)))).
Proof.
  unfold imported_Original_LF__DOT__Logic_LF_Logic_Even.
  rewrite <- n1000_eq.
  exact Imported.Original_LF__DOT__Logic_LF_Logic_even__1000.
Defined.

Definition the_iso := Original_LF__DOT__Logic_LF_Logic_Even_iso (S_iso (S_iso (S_iso (iterate1D2 Datatypes.S imported_S S_iso 997 O imported_0 _0_iso)))).

Instance Original_LF__DOT__Logic_LF_Logic_even__1000_iso : rel_iso
    {|
      to := Original_LF__DOT__Logic_LF_Logic_Even_iso (S_iso (S_iso (S_iso (iterate1D2 Datatypes.S imported_S S_iso 997 O imported_0 _0_iso))));
      from := from (Original_LF__DOT__Logic_LF_Logic_Even_iso (S_iso (S_iso (S_iso (iterate1D2 Datatypes.S imported_S S_iso 997 O imported_0 _0_iso)))));
      to_from :=
        fun x : imported_Original_LF__DOT__Logic_LF_Logic_Even (imported_S (imported_S (imported_S (iterate1 imported_S 997 imported_0)))) =>
        to_from (Original_LF__DOT__Logic_LF_Logic_Even_iso (S_iso (S_iso (S_iso (iterate1D2 Datatypes.S imported_S S_iso 997 O imported_0 _0_iso))))) x;
      from_to :=
        fun x : Original.LF_DOT_Logic.LF.Logic.Even 1000 =>
        seq_p_of_t (from_to (Original_LF__DOT__Logic_LF_Logic_Even_iso (S_iso (S_iso (S_iso (iterate1D2 Datatypes.S imported_S S_iso 997 O imported_0 _0_iso))))) x)
    |} Original.LF_DOT_Logic.LF.Logic.even_1000 imported_Original_LF__DOT__Logic_LF_Logic_even__1000.
Proof.
  unfold rel_iso.
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.even_1000 := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_even__1000 := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.even_1000 Original_LF__DOT__Logic_LF_Logic_even__1000_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.even_1000 Imported.Original_LF__DOT__Logic_LF_Logic_even__1000 Original_LF__DOT__Logic_LF_Logic_even__1000_iso := {}.
