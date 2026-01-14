From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> SProp := (@Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3).

(* Helper to convert Original.Perm3 to Imported.Perm3 *)
Fixpoint to_perm3 {X1 X2 : Type} (hx : Iso X1 X2) 
  {l1 l2 : Original.LF_DOT_Poly.LF.Poly.list X1}
  (H : Original.LF_DOT_IndProp.LF.IndProp.Perm3Reminder.Perm3 l1 l2) {struct H}
  : Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 X2 
      (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l1)
      (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l2) :=
  match H with
  | Original.LF_DOT_IndProp.LF.IndProp.Perm3Reminder.perm3_swap12 a b c =>
      Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3_perm3_swap12 X2 (to hx a) (to hx b) (to hx c)
  | Original.LF_DOT_IndProp.LF.IndProp.Perm3Reminder.perm3_swap23 a b c =>
      Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3_perm3_swap23 X2 (to hx a) (to hx b) (to hx c)
  | Original.LF_DOT_IndProp.LF.IndProp.Perm3Reminder.perm3_trans _ _ _ H1 H2 =>
      Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3_perm3_trans X2 _ _ _ (to_perm3 hx H1) (to_perm3 hx H2)
  end.

(* Helper to convert Imported.Perm3 to Original.Perm3 using fix and the _indl principle *)
(* We use the SProp elimination to SProp and then extract via sinhabitant *)
Definition from_perm3_aux {X1 X2 : Type} (hx : Iso X1 X2)
  (l1 l2 : imported_Original_LF__DOT__Poly_LF_Poly_list X2)
  (H : Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 X2 l1 l2)
  : SInhabited (Original.LF_DOT_IndProp.LF.IndProp.Perm3Reminder.Perm3
      (from (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l1)
      (from (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l2)).
Proof.
  revert H.
  apply (Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3_indl X2 
    (fun l1 l2 _ => SInhabited (Original.LF_DOT_IndProp.LF.IndProp.Perm3Reminder.Perm3
      (from (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l1)
      (from (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l2)))).
  - (* perm3_swap12 case *)
    intros a b c.
    apply sinhabits.
    apply Original.LF_DOT_IndProp.LF.IndProp.Perm3Reminder.perm3_swap12.
  - (* perm3_swap23 case *)
    intros a b c.
    apply sinhabits.
    apply Original.LF_DOT_IndProp.LF.IndProp.Perm3Reminder.perm3_swap23.
  - (* perm3_trans case *)
    intros l1' l2' l3' H12 H23 IH12 IH23.
    apply sinhabits.
    apply (Original.LF_DOT_IndProp.LF.IndProp.Perm3Reminder.perm3_trans _ _ _ (sinhabitant IH12) (sinhabitant IH23)).
Defined.

Definition from_perm3 {X1 X2 : Type} (hx : Iso X1 X2)
  {l1 l2 : imported_Original_LF__DOT__Poly_LF_Poly_list X2}
  (H : Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 X2 l1 l2)
  : Original.LF_DOT_IndProp.LF.IndProp.Perm3Reminder.Perm3
      (from (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l1)
      (from (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l2)
  := sinhabitant (@from_perm3_aux X1 X2 hx l1 l2 H).

Instance Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4 ->
  forall (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6 ->
  Iso (Original.LF_DOT_IndProp.LF.IndProp.Perm3Reminder.Perm3 x3 x5) (imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 x4 x6).
Admitted.
Instance: KnownConstant (@Original.LF_DOT_IndProp.LF.IndProp.Perm3Reminder.Perm3) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_IndProp.LF.IndProp.Perm3Reminder.Perm3) Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_IndProp.LF.IndProp.Perm3Reminder.Perm3) (@Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3) Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3_iso := {}.