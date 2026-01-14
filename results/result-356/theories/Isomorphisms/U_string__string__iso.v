From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_String_string : Type := Imported.String_string.

(* First we need to convert bool <-> mybool *)
Definition bool_to_mybool (b : bool) : Imported.mybool :=
  match b with
  | true => Imported.mybool_mytrue
  | false => Imported.mybool_myfalse
  end.

Definition mybool_to_bool (b : Imported.mybool) : bool :=
  match b with
  | Imported.mybool_mytrue => true
  | Imported.mybool_myfalse => false
  end.

Lemma bool_to_from : forall b, IsomorphismDefinitions.eq (bool_to_mybool (mybool_to_bool b)) b.
Proof. destruct b; apply IsomorphismDefinitions.eq_refl. Qed.

Lemma bool_from_to : forall b, IsomorphismDefinitions.eq (mybool_to_bool (bool_to_mybool b)) b.
Proof. destruct b; apply IsomorphismDefinitions.eq_refl. Qed.

(* Now ascii <-> Imported.ascii *)
Definition ascii_to_imported (a : Ascii.ascii) : Imported.ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Imported.ascii_Ascii
      (bool_to_mybool b0) (bool_to_mybool b1) (bool_to_mybool b2) (bool_to_mybool b3)
      (bool_to_mybool b4) (bool_to_mybool b5) (bool_to_mybool b6) (bool_to_mybool b7)
  end.

Definition ascii_from_imported (a : Imported.ascii) : Ascii.ascii :=
  match a with
  | Imported.ascii_Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Ascii.Ascii
      (mybool_to_bool b0) (mybool_to_bool b1) (mybool_to_bool b2) (mybool_to_bool b3)
      (mybool_to_bool b4) (mybool_to_bool b5) (mybool_to_bool b6) (mybool_to_bool b7)
  end.

Lemma ascii_to_from : forall a, IsomorphismDefinitions.eq (ascii_to_imported (ascii_from_imported a)) a.
Proof.
  intro a. destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold ascii_from_imported, ascii_to_imported.
  pose proof (bool_to_from b0) as H0.
  pose proof (bool_to_from b1) as H1.
  pose proof (bool_to_from b2) as H2.
  pose proof (bool_to_from b3) as H3.
  pose proof (bool_to_from b4) as H4.
  pose proof (bool_to_from b5) as H5.
  pose proof (bool_to_from b6) as H6.
  pose proof (bool_to_from b7) as H7.
  (* Apply f_equal step by step *)
  apply (IsoEq.eq_trans (y := Imported.ascii_Ascii b0 
     (bool_to_mybool (mybool_to_bool b1))
     (bool_to_mybool (mybool_to_bool b2))
     (bool_to_mybool (mybool_to_bool b3))
     (bool_to_mybool (mybool_to_bool b4))
     (bool_to_mybool (mybool_to_bool b5))
     (bool_to_mybool (mybool_to_bool b6))
     (bool_to_mybool (mybool_to_bool b7)))).
  - apply (IsoEq.f_equal (fun x => Imported.ascii_Ascii x _ _ _ _ _ _ _) H0).
  - apply (IsoEq.eq_trans (y := Imported.ascii_Ascii b0 b1 
       (bool_to_mybool (mybool_to_bool b2))
       (bool_to_mybool (mybool_to_bool b3))
       (bool_to_mybool (mybool_to_bool b4))
       (bool_to_mybool (mybool_to_bool b5))
       (bool_to_mybool (mybool_to_bool b6))
       (bool_to_mybool (mybool_to_bool b7)))).
    + apply (IsoEq.f_equal (fun x => Imported.ascii_Ascii _ x _ _ _ _ _ _) H1).
    + apply (IsoEq.eq_trans (y := Imported.ascii_Ascii b0 b1 b2 
         (bool_to_mybool (mybool_to_bool b3))
         (bool_to_mybool (mybool_to_bool b4))
         (bool_to_mybool (mybool_to_bool b5))
         (bool_to_mybool (mybool_to_bool b6))
         (bool_to_mybool (mybool_to_bool b7)))).
      * apply (IsoEq.f_equal (fun x => Imported.ascii_Ascii _ _ x _ _ _ _ _) H2).
      * apply (IsoEq.eq_trans (y := Imported.ascii_Ascii b0 b1 b2 b3 
           (bool_to_mybool (mybool_to_bool b4))
           (bool_to_mybool (mybool_to_bool b5))
           (bool_to_mybool (mybool_to_bool b6))
           (bool_to_mybool (mybool_to_bool b7)))).
        -- apply (IsoEq.f_equal (fun x => Imported.ascii_Ascii _ _ _ x _ _ _ _) H3).
        -- apply (IsoEq.eq_trans (y := Imported.ascii_Ascii b0 b1 b2 b3 b4 
             (bool_to_mybool (mybool_to_bool b5))
             (bool_to_mybool (mybool_to_bool b6))
             (bool_to_mybool (mybool_to_bool b7)))).
           ++ apply (IsoEq.f_equal (fun x => Imported.ascii_Ascii _ _ _ _ x _ _ _) H4).
           ++ apply (IsoEq.eq_trans (y := Imported.ascii_Ascii b0 b1 b2 b3 b4 b5 
                (bool_to_mybool (mybool_to_bool b6))
                (bool_to_mybool (mybool_to_bool b7)))).
              ** apply (IsoEq.f_equal (fun x => Imported.ascii_Ascii _ _ _ _ _ x _ _) H5).
              ** apply (IsoEq.eq_trans (y := Imported.ascii_Ascii b0 b1 b2 b3 b4 b5 b6 
                   (bool_to_mybool (mybool_to_bool b7)))).
                 --- apply (IsoEq.f_equal (fun x => Imported.ascii_Ascii _ _ _ _ _ _ x _) H6).
                 --- apply (IsoEq.f_equal (fun x => Imported.ascii_Ascii _ _ _ _ _ _ _ x) H7).
Qed.

Lemma ascii_from_to : forall a, IsomorphismDefinitions.eq (ascii_from_imported (ascii_to_imported a)) a.
Proof.
  intro a. destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold ascii_from_imported, ascii_to_imported.
  pose proof (bool_from_to b0) as H0.
  pose proof (bool_from_to b1) as H1.
  pose proof (bool_from_to b2) as H2.
  pose proof (bool_from_to b3) as H3.
  pose proof (bool_from_to b4) as H4.
  pose proof (bool_from_to b5) as H5.
  pose proof (bool_from_to b6) as H6.
  pose proof (bool_from_to b7) as H7.
  apply (IsoEq.eq_trans (y := Ascii.Ascii b0 
     (mybool_to_bool (bool_to_mybool b1))
     (mybool_to_bool (bool_to_mybool b2))
     (mybool_to_bool (bool_to_mybool b3))
     (mybool_to_bool (bool_to_mybool b4))
     (mybool_to_bool (bool_to_mybool b5))
     (mybool_to_bool (bool_to_mybool b6))
     (mybool_to_bool (bool_to_mybool b7)))).
  - apply (IsoEq.f_equal (fun x => Ascii.Ascii x _ _ _ _ _ _ _) H0).
  - apply (IsoEq.eq_trans (y := Ascii.Ascii b0 b1 
       (mybool_to_bool (bool_to_mybool b2))
       (mybool_to_bool (bool_to_mybool b3))
       (mybool_to_bool (bool_to_mybool b4))
       (mybool_to_bool (bool_to_mybool b5))
       (mybool_to_bool (bool_to_mybool b6))
       (mybool_to_bool (bool_to_mybool b7)))).
    + apply (IsoEq.f_equal (fun x => Ascii.Ascii _ x _ _ _ _ _ _) H1).
    + apply (IsoEq.eq_trans (y := Ascii.Ascii b0 b1 b2 
         (mybool_to_bool (bool_to_mybool b3))
         (mybool_to_bool (bool_to_mybool b4))
         (mybool_to_bool (bool_to_mybool b5))
         (mybool_to_bool (bool_to_mybool b6))
         (mybool_to_bool (bool_to_mybool b7)))).
      * apply (IsoEq.f_equal (fun x => Ascii.Ascii _ _ x _ _ _ _ _) H2).
      * apply (IsoEq.eq_trans (y := Ascii.Ascii b0 b1 b2 b3 
           (mybool_to_bool (bool_to_mybool b4))
           (mybool_to_bool (bool_to_mybool b5))
           (mybool_to_bool (bool_to_mybool b6))
           (mybool_to_bool (bool_to_mybool b7)))).
        -- apply (IsoEq.f_equal (fun x => Ascii.Ascii _ _ _ x _ _ _ _) H3).
        -- apply (IsoEq.eq_trans (y := Ascii.Ascii b0 b1 b2 b3 b4 
             (mybool_to_bool (bool_to_mybool b5))
             (mybool_to_bool (bool_to_mybool b6))
             (mybool_to_bool (bool_to_mybool b7)))).
           ++ apply (IsoEq.f_equal (fun x => Ascii.Ascii _ _ _ _ x _ _ _) H4).
           ++ apply (IsoEq.eq_trans (y := Ascii.Ascii b0 b1 b2 b3 b4 b5 
                (mybool_to_bool (bool_to_mybool b6))
                (mybool_to_bool (bool_to_mybool b7)))).
              ** apply (IsoEq.f_equal (fun x => Ascii.Ascii _ _ _ _ _ x _ _) H5).
              ** apply (IsoEq.eq_trans (y := Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 
                   (mybool_to_bool (bool_to_mybool b7)))).
                 --- apply (IsoEq.f_equal (fun x => Ascii.Ascii _ _ _ _ _ _ x _) H6).
                 --- apply (IsoEq.f_equal (fun x => Ascii.Ascii _ _ _ _ _ _ _ x) H7).
Qed.

(* Now String.string <-> Imported.String_string *)
Fixpoint string_to_imported (s : String.string) : Imported.String_string :=
  match s with
  | String.EmptyString => Imported.String_string_EmptyString
  | String.String c rest => Imported.String_string_String (ascii_to_imported c) (string_to_imported rest)
  end.

Fixpoint string_from_imported (s : Imported.String_string) : String.string :=
  match s with
  | Imported.String_string_EmptyString => String.EmptyString
  | Imported.String_string_String c rest => String.String (ascii_from_imported c) (string_from_imported rest)
  end.

Lemma string_to_from : forall s, IsomorphismDefinitions.eq (string_to_imported (string_from_imported s)) s.
Proof.
  fix IH 1.
  intro s. destruct s.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl.
    apply (IsoEq.f_equal2 Imported.String_string_String (ascii_to_from _) (IH s)).
Qed.

Lemma string_from_to : forall s, IsomorphismDefinitions.eq (string_from_imported (string_to_imported s)) s.
Proof.
  fix IH 1.
  intro s. destruct s.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl.
    apply (IsoEq.f_equal2 String.String (ascii_from_to _) (IH s)).
Qed.

Instance String_string_iso : Iso String.string imported_String_string.
Proof.
  unshelve eapply Build_Iso.
  - exact string_to_imported.
  - exact string_from_imported.
  - intro s. apply string_to_from.
  - intro s. apply string_from_to.
Defined.

Instance: KnownConstant String.string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.String_string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor String.string String_string_iso := {}.
Instance: IsoStatementProofBetween String.string Imported.String_string String_string_iso := {}.
