From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist.

(* Build the isomorphism between natlist and Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist *)
Fixpoint natlist_to_imported (l : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) : Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  match l with
  | Original.LF_DOT_Lists.LF.Lists.NatList.nil => Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist_nil
  | Original.LF_DOT_Lists.LF.Lists.NatList.cons n l' => 
      Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist_cons (nat_to_imported n) (natlist_to_imported l')
  end.

Fixpoint imported_to_natlist (l : Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist) : Original.LF_DOT_Lists.LF.Lists.NatList.natlist :=
  match l with
  | Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist_nil => Original.LF_DOT_Lists.LF.Lists.NatList.nil
  | Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist_cons n l' => 
      Original.LF_DOT_Lists.LF.Lists.NatList.cons (imported_to_nat n) (imported_to_natlist l')
  end.

(* to_from: natlist_to_imported (imported_to_natlist x) = x *)
Fixpoint natlist_to_from_proof (l : Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist) 
  : IsomorphismDefinitions.eq (natlist_to_imported (imported_to_natlist l)) l :=
  match l return IsomorphismDefinitions.eq (natlist_to_imported (imported_to_natlist l)) l with
  | Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist_nil => IsomorphismDefinitions.eq_refl
  | Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist_cons n l' => 
      f_equal2 Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist_cons 
               (to_from_proof n) 
               (natlist_to_from_proof l')
  end.

(* from_to: imported_to_natlist (natlist_to_imported x) = x *)
Fixpoint natlist_from_to_proof (l : Original.LF_DOT_Lists.LF.Lists.NatList.natlist)
  : IsomorphismDefinitions.eq (imported_to_natlist (natlist_to_imported l)) l :=
  match l return IsomorphismDefinitions.eq (imported_to_natlist (natlist_to_imported l)) l with
  | Original.LF_DOT_Lists.LF.Lists.NatList.nil => IsomorphismDefinitions.eq_refl
  | Original.LF_DOT_Lists.LF.Lists.NatList.cons n l' =>
      f_equal2 Original.LF_DOT_Lists.LF.Lists.NatList.cons
               (from_to_proof n)
               (natlist_from_to_proof l')
  end.

Instance Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso : Iso Original.LF_DOT_Lists.LF.Lists.NatList.natlist imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  @Build_Iso _ _ natlist_to_imported imported_to_natlist natlist_to_from_proof natlist_from_to_proof.

Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.natlist := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.natlist Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.natlist Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso := {}.