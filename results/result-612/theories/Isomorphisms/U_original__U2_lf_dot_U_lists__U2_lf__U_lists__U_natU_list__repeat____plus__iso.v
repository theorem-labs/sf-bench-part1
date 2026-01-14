From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__app__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__repeat__iso.

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_repeat__plus : forall x x0 x1 : imported_nat,
  imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Lists_LF_Lists_NatList_app (imported_Original_LF__DOT__Lists_LF_Lists_NatList_repeat x1 x) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_repeat x1 x0))
    (imported_Original_LF__DOT__Lists_LF_Lists_NatList_repeat x1 (imported_Nat_add x x0)) := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_repeat__plus.

(* The repeat_plus theorem is Admitted in Original.v so we use iso_SInhabited to prove the isomorphism *)
Instance Original_LF__DOT__Lists_LF_Lists_NatList_repeat__plus_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6),
  rel_iso
    (relax_Iso_Ts_Ps
       (Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Lists_LF_Lists_NatList_app_iso (Original_LF__DOT__Lists_LF_Lists_NatList_repeat_iso hx1 hx) (Original_LF__DOT__Lists_LF_Lists_NatList_repeat_iso hx1 hx0))
          (Original_LF__DOT__Lists_LF_Lists_NatList_repeat_iso hx1 (Nat_add_iso hx hx0))))
    (Original.LF_DOT_Lists.LF.Lists.NatList.repeat_plus x1 x3 x5) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_repeat__plus x2 x4 x6).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 hx1.
  unfold rel_iso at 1.
  simpl.
  (* We need to prove an equality in SProp between two SProp equalities *)
  (* Since both sides are proofs of SProp equalities, we can use proof irrelevance *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.repeat_plus := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_repeat__plus := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.repeat_plus Original_LF__DOT__Lists_LF_Lists_NatList_repeat__plus_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.repeat_plus Imported.Original_LF__DOT__Lists_LF_Lists_NatList_repeat__plus Original_LF__DOT__Lists_LF_Lists_NatList_repeat__plus_iso := {}.