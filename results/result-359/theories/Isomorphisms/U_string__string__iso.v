From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
From Stdlib Require Import Ascii String.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_String_string : Type := Imported.String_string.

(* bool <-> mybool *)
Definition bool_to_mybool (b : bool) : Imported.mybool :=
  match b with
  | true => Imported.mybool_true
  | false => Imported.mybool_false
  end.

Definition mybool_to_bool (b : Imported.mybool) : bool :=
  match b with
  | Imported.mybool_true => true
  | Imported.mybool_false => false
  end.

(* ascii <-> Ascii_ascii *)
Definition ascii_to_Ascii (a : Ascii.ascii) : Imported.Ascii_ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Imported.Ascii_ascii_Ascii
      (bool_to_mybool b0) (bool_to_mybool b1) (bool_to_mybool b2) (bool_to_mybool b3)
      (bool_to_mybool b4) (bool_to_mybool b5) (bool_to_mybool b6) (bool_to_mybool b7)
  end.

Definition Ascii_to_ascii (a : Imported.Ascii_ascii) : Ascii.ascii :=
  Ascii.Ascii
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__manual____grade____for____U_r____provability__iso__hyg28 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__manual____grade____for____U_r____provability__iso__hyg30 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__manual____grade____for____U_r____provability__iso__hyg32 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__manual____grade____for____U_r____provability__iso__hyg34 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__manual____grade____for____U_r____provability__iso__hyg36 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__manual____grade____for____U_r____provability__iso__hyg38 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__manual____grade____for____U_r____provability__iso__hyg40 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__manual____grade____for____U_r____provability__iso__hyg42 a)).

(* string <-> String_string *)
Fixpoint string_to_String (s : String.string) : imported_String_string :=
  match s with
  | String.EmptyString => Imported.String_string_EmptyString
  | String.String a s' => Imported.String_string_String (ascii_to_Ascii a) (string_to_String s')
  end.

Fixpoint String_to_string (s : imported_String_string) : String.string :=
  match s with
  | Imported.String_string_EmptyString => String.EmptyString
  | Imported.String_string_String a s' => String.String (Ascii_to_ascii a) (String_to_string s')
  end.

Lemma bool_mybool_roundtrip : forall b, mybool_to_bool (bool_to_mybool b) = b.
Proof. destruct b; reflexivity. Qed.

Lemma mybool_bool_roundtrip : forall b, bool_to_mybool (mybool_to_bool b) = b.
Proof. destruct b; reflexivity. Qed.

Definition mybool_roundtrip (b : Imported.mybool) :
    IsomorphismDefinitions.eq (bool_to_mybool (mybool_to_bool b)) b :=
  match b with
  | Imported.mybool_true => IsomorphismDefinitions.eq_refl
  | Imported.mybool_false => IsomorphismDefinitions.eq_refl
  end.

Definition bool_roundtrip (b : bool) : IsomorphismDefinitions.eq (mybool_to_bool (bool_to_mybool b)) b :=
  match b with
  | true => IsomorphismDefinitions.eq_refl
  | false => IsomorphismDefinitions.eq_refl
  end.

Definition Ascii_ascii_roundtrip (a : Imported.Ascii_ascii) :
    IsomorphismDefinitions.eq (ascii_to_Ascii (Ascii_to_ascii a)) a :=
  match a with
  | Imported.Ascii_ascii_Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    f_equal2 (fun x01 x23 => 
      match x01, x23 with
      | (x0, x1), (x2, x3) =>
        match x0, x1, x2, x3 with
        | (a0, a1), (a2, a3), (a4, a5), (a6, a7) =>
          Imported.Ascii_ascii_Ascii a0 a1 a2 a3 a4 a5 a6 a7
        end
      end)
      (f_equal2 pair
        (f_equal2 pair (mybool_roundtrip b0) (mybool_roundtrip b1))
        (f_equal2 pair (mybool_roundtrip b2) (mybool_roundtrip b3)))
      (f_equal2 pair
        (f_equal2 pair (mybool_roundtrip b4) (mybool_roundtrip b5))
        (f_equal2 pair (mybool_roundtrip b6) (mybool_roundtrip b7)))
  end.

Definition ascii_Ascii_roundtrip (a : Ascii.ascii) :
    IsomorphismDefinitions.eq (Ascii_to_ascii (ascii_to_Ascii a)) a :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    f_equal2 (fun x01 x23 => 
      match x01, x23 with
      | (x0, x1), (x2, x3) =>
        match x0, x1, x2, x3 with
        | (a0, a1), (a2, a3), (a4, a5), (a6, a7) =>
          Ascii.Ascii a0 a1 a2 a3 a4 a5 a6 a7
        end
      end)
      (f_equal2 pair
        (f_equal2 pair (bool_roundtrip b0) (bool_roundtrip b1))
        (f_equal2 pair (bool_roundtrip b2) (bool_roundtrip b3)))
      (f_equal2 pair
        (f_equal2 pair (bool_roundtrip b4) (bool_roundtrip b5))
        (f_equal2 pair (bool_roundtrip b6) (bool_roundtrip b7)))
  end.

Fixpoint String_string_to_from (s : imported_String_string) :
    IsomorphismDefinitions.eq (string_to_String (String_to_string s)) s :=
  match s with
  | Imported.String_string_EmptyString => IsomorphismDefinitions.eq_refl
  | Imported.String_string_String a s' =>
      f_equal2 Imported.String_string_String (Ascii_ascii_roundtrip a) (String_string_to_from s')
  end.

Fixpoint string_String_from_to (s : String.string) :
    IsomorphismDefinitions.eq (String_to_string (string_to_String s)) s :=
  match s with
  | String.EmptyString => IsomorphismDefinitions.eq_refl
  | String.String a s' =>
      f_equal2 String.String (ascii_Ascii_roundtrip a) (string_String_from_to s')
  end.

Instance String_string_iso : Iso String.string imported_String_string.
Proof.
  unshelve eapply Build_Iso.
  - exact string_to_String.
  - exact String_to_string.
  - exact String_string_to_from.
  - exact string_String_from_to.
Defined.
Instance: KnownConstant String.string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.String_string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor String.string String_string_iso := {}.
Instance: IsoStatementProofBetween String.string Imported.String_string String_string_iso := {}.