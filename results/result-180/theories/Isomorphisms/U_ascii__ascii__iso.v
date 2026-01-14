From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.bool__iso.

Definition imported_Ascii_ascii : Type := Imported.Ascii_ascii.

Definition imported_to_ascii (a : Imported.Ascii_ascii) : Ascii.ascii :=
  Ascii.Ascii 
    (imported_to_bool (Imported.a____at___Solution__hyg174 a))
    (imported_to_bool (Imported.a____at___Solution__hyg176 a))
    (imported_to_bool (Imported.a____at___Solution__hyg178 a))
    (imported_to_bool (Imported.a____at___Solution__hyg180 a))
    (imported_to_bool (Imported.a____at___Solution__hyg182 a))
    (imported_to_bool (Imported.a____at___Solution__hyg184 a))
    (imported_to_bool (Imported.a____at___Solution__hyg186 a))
    (imported_to_bool (Imported.a____at___Solution__hyg188 a)).

Definition ascii_to_imported (a : Ascii.ascii) : Imported.Ascii_ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Imported.Ascii_Ascii
      (bool_to_imported b0) (bool_to_imported b1) (bool_to_imported b2) (bool_to_imported b3)
      (bool_to_imported b4) (bool_to_imported b5) (bool_to_imported b6) (bool_to_imported b7)
  end.

Instance Ascii_ascii_iso : Iso Ascii.ascii imported_Ascii_ascii.
Proof.
  apply Build_Iso with (to := ascii_to_imported) (from := imported_to_ascii).
  - intro a. 
    unfold imported_to_ascii, ascii_to_imported. simpl.
    set (b0 := Imported.a____at___Solution__hyg174 a).
    set (b1 := Imported.a____at___Solution__hyg176 a).
    set (b2 := Imported.a____at___Solution__hyg178 a).
    set (b3 := Imported.a____at___Solution__hyg180 a).
    set (b4 := Imported.a____at___Solution__hyg182 a).
    set (b5 := Imported.a____at___Solution__hyg184 a).
    set (b6 := Imported.a____at___Solution__hyg186 a).
    set (b7 := Imported.a____at___Solution__hyg188 a).
    pose proof (bool_to_from b0) as H0.
    pose proof (bool_to_from b1) as H1.
    pose proof (bool_to_from b2) as H2.
    pose proof (bool_to_from b3) as H3.
    pose proof (bool_to_from b4) as H4.
    pose proof (bool_to_from b5) as H5.
    pose proof (bool_to_from b6) as H6.
    pose proof (bool_to_from b7) as H7.
    apply (eq_trans (y := Imported.Ascii_Ascii b0 (bool_to_imported (imported_to_bool b1)) (bool_to_imported (imported_to_bool b2)) (bool_to_imported (imported_to_bool b3)) (bool_to_imported (imported_to_bool b4)) (bool_to_imported (imported_to_bool b5)) (bool_to_imported (imported_to_bool b6)) (bool_to_imported (imported_to_bool b7)))).
    + apply (f_equal (fun x => Imported.Ascii_Ascii x _ _ _ _ _ _ _) H0).
    + apply (eq_trans (y := Imported.Ascii_Ascii b0 b1 (bool_to_imported (imported_to_bool b2)) (bool_to_imported (imported_to_bool b3)) (bool_to_imported (imported_to_bool b4)) (bool_to_imported (imported_to_bool b5)) (bool_to_imported (imported_to_bool b6)) (bool_to_imported (imported_to_bool b7)))).
      * apply (f_equal (fun x => Imported.Ascii_Ascii _ x _ _ _ _ _ _) H1).
      * apply (eq_trans (y := Imported.Ascii_Ascii b0 b1 b2 (bool_to_imported (imported_to_bool b3)) (bool_to_imported (imported_to_bool b4)) (bool_to_imported (imported_to_bool b5)) (bool_to_imported (imported_to_bool b6)) (bool_to_imported (imported_to_bool b7)))).
        -- apply (f_equal (fun x => Imported.Ascii_Ascii _ _ x _ _ _ _ _) H2).
        -- apply (eq_trans (y := Imported.Ascii_Ascii b0 b1 b2 b3 (bool_to_imported (imported_to_bool b4)) (bool_to_imported (imported_to_bool b5)) (bool_to_imported (imported_to_bool b6)) (bool_to_imported (imported_to_bool b7)))).
           ++ apply (f_equal (fun x => Imported.Ascii_Ascii _ _ _ x _ _ _ _) H3).
           ++ apply (eq_trans (y := Imported.Ascii_Ascii b0 b1 b2 b3 b4 (bool_to_imported (imported_to_bool b5)) (bool_to_imported (imported_to_bool b6)) (bool_to_imported (imported_to_bool b7)))).
              ** apply (f_equal (fun x => Imported.Ascii_Ascii _ _ _ _ x _ _ _) H4).
              ** apply (eq_trans (y := Imported.Ascii_Ascii b0 b1 b2 b3 b4 b5 (bool_to_imported (imported_to_bool b6)) (bool_to_imported (imported_to_bool b7)))).
                 --- apply (f_equal (fun x => Imported.Ascii_Ascii _ _ _ _ _ x _ _) H5).
                 --- apply (eq_trans (y := Imported.Ascii_Ascii b0 b1 b2 b3 b4 b5 b6 (bool_to_imported (imported_to_bool b7)))).
                     +++ apply (f_equal (fun x => Imported.Ascii_Ascii _ _ _ _ _ _ x _) H6).
                     +++ apply (eq_trans (y := Imported.Ascii_Ascii b0 b1 b2 b3 b4 b5 b6 b7)).
                         *** apply (f_equal (fun x => Imported.Ascii_Ascii _ _ _ _ _ _ _ x) H7).
                         *** apply IsomorphismDefinitions.eq_refl.
  - intro a. destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
    unfold ascii_to_imported, imported_to_ascii. simpl.
    pose proof (bool_from_to b0) as H0.
    pose proof (bool_from_to b1) as H1.
    pose proof (bool_from_to b2) as H2.
    pose proof (bool_from_to b3) as H3.
    pose proof (bool_from_to b4) as H4.
    pose proof (bool_from_to b5) as H5.
    pose proof (bool_from_to b6) as H6.
    pose proof (bool_from_to b7) as H7.
    apply (eq_trans (y := Ascii.Ascii b0 (imported_to_bool (bool_to_imported b1)) (imported_to_bool (bool_to_imported b2)) (imported_to_bool (bool_to_imported b3)) (imported_to_bool (bool_to_imported b4)) (imported_to_bool (bool_to_imported b5)) (imported_to_bool (bool_to_imported b6)) (imported_to_bool (bool_to_imported b7)))).
    + apply (f_equal (fun x => Ascii.Ascii x _ _ _ _ _ _ _) H0).
    + apply (eq_trans (y := Ascii.Ascii b0 b1 (imported_to_bool (bool_to_imported b2)) (imported_to_bool (bool_to_imported b3)) (imported_to_bool (bool_to_imported b4)) (imported_to_bool (bool_to_imported b5)) (imported_to_bool (bool_to_imported b6)) (imported_to_bool (bool_to_imported b7)))).
      * apply (f_equal (fun x => Ascii.Ascii _ x _ _ _ _ _ _) H1).
      * apply (eq_trans (y := Ascii.Ascii b0 b1 b2 (imported_to_bool (bool_to_imported b3)) (imported_to_bool (bool_to_imported b4)) (imported_to_bool (bool_to_imported b5)) (imported_to_bool (bool_to_imported b6)) (imported_to_bool (bool_to_imported b7)))).
        -- apply (f_equal (fun x => Ascii.Ascii _ _ x _ _ _ _ _) H2).
        -- apply (eq_trans (y := Ascii.Ascii b0 b1 b2 b3 (imported_to_bool (bool_to_imported b4)) (imported_to_bool (bool_to_imported b5)) (imported_to_bool (bool_to_imported b6)) (imported_to_bool (bool_to_imported b7)))).
           ++ apply (f_equal (fun x => Ascii.Ascii _ _ _ x _ _ _ _) H3).
           ++ apply (eq_trans (y := Ascii.Ascii b0 b1 b2 b3 b4 (imported_to_bool (bool_to_imported b5)) (imported_to_bool (bool_to_imported b6)) (imported_to_bool (bool_to_imported b7)))).
              ** apply (f_equal (fun x => Ascii.Ascii _ _ _ _ x _ _ _) H4).
              ** apply (eq_trans (y := Ascii.Ascii b0 b1 b2 b3 b4 b5 (imported_to_bool (bool_to_imported b6)) (imported_to_bool (bool_to_imported b7)))).
                 --- apply (f_equal (fun x => Ascii.Ascii _ _ _ _ _ x _ _) H5).
                 --- apply (eq_trans (y := Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 (imported_to_bool (bool_to_imported b7)))).
                     +++ apply (f_equal (fun x => Ascii.Ascii _ _ _ _ _ _ x _) H6).
                     +++ apply (eq_trans (y := Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7)).
                         *** apply (f_equal (fun x => Ascii.Ascii _ _ _ _ _ _ _ x) H7).
                         *** apply IsomorphismDefinitions.eq_refl.
Qed.

Instance: KnownConstant Ascii.ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Ascii_ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Ascii.ascii Ascii_ascii_iso := {}.
Instance: IsoStatementProofBetween Ascii.ascii Imported.Ascii_ascii Ascii_ascii_iso := {}.