From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso Isomorphisms.U_string__string__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_aexp : Type := Imported.Original_LF__DOT__Imp_LF_Imp_aexp.

Fixpoint aexp_to_imported (a : Original.LF_DOT_Imp.LF.Imp.aexp) : Imported.Original_LF__DOT__Imp_LF_Imp_aexp :=
  match a with
  | Original.LF_DOT_Imp.LF.Imp.ANum n => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_ANum (to nat_iso n)
  | Original.LF_DOT_Imp.LF.Imp.AId x => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AId (to String_string_iso x)
  | Original.LF_DOT_Imp.LF.Imp.APlus a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_APlus (aexp_to_imported a1) (aexp_to_imported a2)
  | Original.LF_DOT_Imp.LF.Imp.AMinus a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMinus (aexp_to_imported a1) (aexp_to_imported a2)
  | Original.LF_DOT_Imp.LF.Imp.AMult a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMult (aexp_to_imported a1) (aexp_to_imported a2)
  end.

Fixpoint imported_to_aexp (a : Imported.Original_LF__DOT__Imp_LF_Imp_aexp) : Original.LF_DOT_Imp.LF.Imp.aexp :=
  match a with
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_ANum n => Original.LF_DOT_Imp.LF.Imp.ANum (from nat_iso n)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AId x => Original.LF_DOT_Imp.LF.Imp.AId (from String_string_iso x)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_APlus a1 a2 => Original.LF_DOT_Imp.LF.Imp.APlus (imported_to_aexp a1) (imported_to_aexp a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMinus a1 a2 => Original.LF_DOT_Imp.LF.Imp.AMinus (imported_to_aexp a1) (imported_to_aexp a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMult a1 a2 => Original.LF_DOT_Imp.LF.Imp.AMult (imported_to_aexp a1) (imported_to_aexp a2)
  end.

(* Use sprop_eq_eq to convert IsomorphismDefinitions.eq to Logic.eq *)
Definition sprop_to_prop {A : Type} {x y : A} (H : IsomorphismDefinitions.eq x y) : @Logic.eq A x y :=
  match H in IsomorphismDefinitions.eq _ z return @Logic.eq A x z with
  | IsomorphismDefinitions.eq_refl => Logic.eq_refl
  end.

Definition aexp_roundtrip1 : forall a, @Logic.eq _ (imported_to_aexp (aexp_to_imported a)) a.
Proof.
  induction a; simpl.
  - exact (Logic.f_equal Original.LF_DOT_Imp.LF.Imp.ANum (sprop_to_prop (@from_to _ _ nat_iso n))).
  - exact (Logic.f_equal Original.LF_DOT_Imp.LF.Imp.AId (sprop_to_prop (@from_to _ _ String_string_iso x))).
  - exact (Logic.f_equal2 Original.LF_DOT_Imp.LF.Imp.APlus IHa1 IHa2).
  - exact (Logic.f_equal2 Original.LF_DOT_Imp.LF.Imp.AMinus IHa1 IHa2).
  - exact (Logic.f_equal2 Original.LF_DOT_Imp.LF.Imp.AMult IHa1 IHa2).
Defined.

Definition aexp_roundtrip2 : forall a, @Logic.eq _ (aexp_to_imported (imported_to_aexp a)) a.
Proof.
  fix IH 1.
  intros a; destruct a as [n | s | a1 a2 | a1 a2 | a1 a2]; simpl.
  - exact (Logic.f_equal Imported.Original_LF__DOT__Imp_LF_Imp_aexp_ANum (sprop_to_prop (@to_from _ _ nat_iso n))).
  - exact (Logic.f_equal Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AId (sprop_to_prop (@to_from _ _ String_string_iso s))).
  - exact (Logic.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_aexp_APlus (IH a1) (IH a2)).
  - exact (Logic.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMinus (IH a1) (IH a2)).
  - exact (Logic.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMult (IH a1) (IH a2)).
Defined.

Instance Original_LF__DOT__Imp_LF_Imp_aexp_iso : Iso Original.LF_DOT_Imp.LF.Imp.aexp imported_Original_LF__DOT__Imp_LF_Imp_aexp.
Proof.
  exact (Build_Iso aexp_to_imported imported_to_aexp
    (fun a => seq_of_eq (aexp_roundtrip2 a))
    (fun a => seq_of_eq (aexp_roundtrip1 a))).
Defined.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.aexp := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_aexp := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.aexp Original_LF__DOT__Imp_LF_Imp_aexp_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.aexp Imported.Original_LF__DOT__Imp_LF_Imp_aexp Original_LF__DOT__Imp_LF_Imp_aexp_iso := {}.