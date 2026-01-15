From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(*Typeclasses Opaque rel_iso.*) (* for speed *)

(* Import the bool isomorphism *)
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.

Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree : Type := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree.

(* Now we prove the booltree isomorphism *)
Fixpoint booltree_to_imported (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree) : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree :=
  match t with
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.bt_empty => Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_bt_empty
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.bt_leaf b => Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_bt_leaf (to Original_LF__DOT__Basics_LF_Basics_bool_iso b)
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.bt_branch b t1 t2 => 
      Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_bt_branch (to Original_LF__DOT__Basics_LF_Basics_bool_iso b) (booltree_to_imported t1) (booltree_to_imported t2)
  end.

Fixpoint imported_to_booltree (t : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree) : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree :=
  match t with
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_bt_empty => Original.LF_DOT_IndPrinciples.LF.IndPrinciples.bt_empty
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_bt_leaf b => Original.LF_DOT_IndPrinciples.LF.IndPrinciples.bt_leaf (IsomorphismDefinitions.from Original_LF__DOT__Basics_LF_Basics_bool_iso b)
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_bt_branch b t1 t2 => 
      Original.LF_DOT_IndPrinciples.LF.IndPrinciples.bt_branch (IsomorphismDefinitions.from Original_LF__DOT__Basics_LF_Basics_bool_iso b) (imported_to_booltree t1) (imported_to_booltree t2)
  end.

Fixpoint to_from_booltree (t : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree) : 
    IsomorphismDefinitions.eq (booltree_to_imported (imported_to_booltree t)) t :=
  match t with
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_bt_empty => IsomorphismDefinitions.eq_refl
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_bt_leaf b => 
      match b return IsomorphismDefinitions.eq (booltree_to_imported (imported_to_booltree (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_bt_leaf b))) (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_bt_leaf b) with
      | Imported.Original_LF__DOT__Basics_LF_Basics_bool_true => IsomorphismDefinitions.eq_refl
      | Imported.Original_LF__DOT__Basics_LF_Basics_bool_false => IsomorphismDefinitions.eq_refl
      end
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_bt_branch b t1 t2 =>
      match b as b0 return 
        (IsomorphismDefinitions.eq (booltree_to_imported (imported_to_booltree t1)) t1) ->
        (IsomorphismDefinitions.eq (booltree_to_imported (imported_to_booltree t2)) t2) ->
        IsomorphismDefinitions.eq (booltree_to_imported (imported_to_booltree (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_bt_branch b0 t1 t2))) (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_bt_branch b0 t1 t2) with
      | Imported.Original_LF__DOT__Basics_LF_Basics_bool_true => 
          fun IH1 IH2 => f_equal2 (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_bt_branch Imported.Original_LF__DOT__Basics_LF_Basics_bool_true) IH1 IH2
      | Imported.Original_LF__DOT__Basics_LF_Basics_bool_false => 
          fun IH1 IH2 => f_equal2 (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_bt_branch Imported.Original_LF__DOT__Basics_LF_Basics_bool_false) IH1 IH2
      end (to_from_booltree t1) (to_from_booltree t2)
  end.

Fixpoint from_to_booltree (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree) : 
    IsomorphismDefinitions.eq (imported_to_booltree (booltree_to_imported t)) t :=
  match t with
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.bt_empty => IsomorphismDefinitions.eq_refl
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.bt_leaf b =>
      match b return IsomorphismDefinitions.eq (imported_to_booltree (booltree_to_imported (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.bt_leaf b))) (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.bt_leaf b) with
      | Original.LF_DOT_Basics.LF.Basics.true => IsomorphismDefinitions.eq_refl
      | Original.LF_DOT_Basics.LF.Basics.false => IsomorphismDefinitions.eq_refl
      end
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.bt_branch b t1 t2 =>
      match b as b0 return 
        (IsomorphismDefinitions.eq (imported_to_booltree (booltree_to_imported t1)) t1) ->
        (IsomorphismDefinitions.eq (imported_to_booltree (booltree_to_imported t2)) t2) ->
        IsomorphismDefinitions.eq (imported_to_booltree (booltree_to_imported (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.bt_branch b0 t1 t2))) (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.bt_branch b0 t1 t2) with
      | Original.LF_DOT_Basics.LF.Basics.true => 
          fun IH1 IH2 => f_equal2 (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.bt_branch Original.LF_DOT_Basics.LF.Basics.true) IH1 IH2
      | Original.LF_DOT_Basics.LF.Basics.false => 
          fun IH1 IH2 => f_equal2 (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.bt_branch Original.LF_DOT_Basics.LF.Basics.false) IH1 IH2
      end (from_to_booltree t1) (from_to_booltree t2)
  end.

Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_iso : Iso Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree.
Proof.
  apply Build_Iso with (to := booltree_to_imported) (from := imported_to_booltree).
  - exact to_from_booltree.
  - exact from_to_booltree.
Defined.

Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_iso := {}.