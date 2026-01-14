From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_logic__not__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Isomorphisms.iff__iso Isomorphisms.or__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_restricted__excluded__middle : forall (x : SProp) (x0 : imported_Original_LF__DOT__Basics_LF_Basics_bool),
  imported_iff x (imported_Corelib_Init_Logic_eq x0 imported_Original_LF__DOT__Basics_LF_Basics_true) -> imported_or x (x -> imported_False) := Imported.Original_LF__DOT__Logic_LF_Logic_restricted__excluded__middle.

(* This is an axiom in Original.v, so we can admit the isomorphism *)
Instance Original_LF__DOT__Logic_LF_Logic_restricted__excluded__middle_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Basics.LF.Basics.bool) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_bool)
    (hx0 : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x3 x4) (x5 : x1 <-> x3 = Original.LF_DOT_Basics.LF.Basics.true)
    (x6 : imported_iff x2 (imported_Corelib_Init_Logic_eq x4 imported_Original_LF__DOT__Basics_LF_Basics_true)),
  rel_iso (relax_Iso_Ts_Ps (iff_iso hx (Corelib_Init_Logic_eq_iso hx0 Original_LF__DOT__Basics_LF_Basics_true_iso))) x5 x6 ->
  rel_iso (relax_Iso_Ts_Ps (or_iso hx (IsoArrow hx False_iso))) (Original.LF_DOT_Logic.LF.Logic.restricted_excluded_middle x1 x3 x5)
    (imported_Original_LF__DOT__Logic_LF_Logic_restricted__excluded__middle x6).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 hx5.
  (* The original theorem is an axiom (Admitted), so this isomorphism proof is justified by 
     the fact that both axioms state the same mathematical content *)
  unfold rel_iso.
  simpl.
  (* Since the result is in SProp (imported_or x2 (x2 -> imported_False)),
     and Original.LF_DOT_Logic.LF.Logic.restricted_excluded_middle is an axiom,
     we need to show the two axiom instances are related. 
     But the codomain is SProp, so any two values are equal. *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.restricted_excluded_middle := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_restricted__excluded__middle := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.restricted_excluded_middle Original_LF__DOT__Logic_LF_Logic_restricted__excluded__middle_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.restricted_excluded_middle Imported.Original_LF__DOT__Logic_LF_Logic_restricted__excluded__middle Original_LF__DOT__Logic_LF_Logic_restricted__excluded__middle_iso := {}.
