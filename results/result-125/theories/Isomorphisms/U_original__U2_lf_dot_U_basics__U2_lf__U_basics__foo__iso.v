From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_foo : imported_Original_LF__DOT__Basics_LF_Basics_bool := Imported.Original_LF__DOT__Basics_LF_Basics_foo.
Instance Original_LF__DOT__Basics_LF_Basics_foo_iso : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso Original.LF_DOT_Basics.LF.Basics.foo imported_Original_LF__DOT__Basics_LF_Basics_foo.
Proof.
  unfold rel_iso.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_foo.
  unfold Imported.Original_LF__DOT__Basics_LF_Basics_foo.
  simpl.
  apply IsomorphismDefinitions.eq_refl.
Qed.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.foo := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_foo := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.foo Original_LF__DOT__Basics_LF_Basics_foo_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.foo Imported.Original_LF__DOT__Basics_LF_Basics_foo Original_LF__DOT__Basics_LF_Basics_foo_iso := {}.