From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_negb : imported_Original_LF__DOT__Basics_LF_Basics_bool -> imported_Original_LF__DOT__Basics_LF_Basics_bool := Imported.Original_LF__DOT__Basics_LF_Basics_negb.
Instance Original_LF__DOT__Basics_LF_Basics_negb_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.bool) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bool),
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x1 x2 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.negb x1) (imported_Original_LF__DOT__Basics_LF_Basics_negb x2).
Proof.
  intros x1 x2 Hx.
  unfold rel_iso in *.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_negb, imported_Original_LF__DOT__Basics_LF_Basics_bool in *.
  simpl in *.
  destruct x1; simpl.
  - (* x1 = true, so Hx : Imported.true = x2 *)
    (* Goal: Imported.false = Imported.negb x2 *)
    (* f_equal gives: negb(Imported.true) = negb(x2) *)
    (* i.e., Imported.false = negb(x2), which is exactly what we need *)
    exact (IsoEq.f_equal Imported.Original_LF__DOT__Basics_LF_Basics_negb Hx).
  - (* x1 = false, so Hx : Imported.false = x2 *)
    (* Goal: Imported.true = Imported.negb x2 *)
    exact (IsoEq.f_equal Imported.Original_LF__DOT__Basics_LF_Basics_negb Hx).
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.negb := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_negb := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.negb Original_LF__DOT__Basics_LF_Basics_negb_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.negb Imported.Original_LF__DOT__Basics_LF_Basics_negb Original_LF__DOT__Basics_LF_Basics_negb_iso := {}.