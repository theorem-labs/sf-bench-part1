From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

(* First, define the isomorphism between nat and the imported nat type *)
Fixpoint nat_to_imported_nat (n : nat) : Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_nat :=
  match n with
  | O => Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_nat_O
  | S n' => Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_nat_S (nat_to_imported_nat n')
  end.

Fixpoint imported_nat_to_nat (n : Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_nat) : nat :=
  match n with
  | Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_nat_O => O
  | Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_nat_S n' => S (imported_nat_to_nat n')
  end.

Fixpoint nat_roundtrip1 (n : nat) : Logic.eq (imported_nat_to_nat (nat_to_imported_nat n)) n :=
  match n with
  | O => Logic.eq_refl
  | S n' => Logic.f_equal S (nat_roundtrip1 n')
  end.

Fixpoint nat_roundtrip2 (n : Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_nat) 
  : Logic.eq (nat_to_imported_nat (imported_nat_to_nat n)) n :=
  match n with
  | Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_nat_O => Logic.eq_refl
  | Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_nat_S n' => 
      Logic.f_equal Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_nat_S (nat_roundtrip2 n')
  end.

(* Now define the isomorphism between mumble and imported mumble *)
Fixpoint mumble_to_imported (m : Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.mumble) 
  : Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble :=
  match m with
  | Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.a => 
      Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_a
  | Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.b x y => 
      Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_b 
        (mumble_to_imported x) (nat_to_imported_nat y)
  | Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.c => 
      Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_c
  end.

Fixpoint imported_to_mumble (m : Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble)
  : Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.mumble :=
  match m with
  | Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_a => 
      Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.a
  | Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_b x y => 
      Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.b 
        (imported_to_mumble x) (imported_nat_to_nat y)
  | Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_c => 
      Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.c
  end.

(* Helper for congruence on b constructor *)
Definition b_cong (m1 m2 : Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.mumble) (n1 n2 : nat)
  (Hm : Logic.eq m1 m2) (Hn : Logic.eq n1 n2) 
  : Logic.eq (Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.b m1 n1)
             (Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.b m2 n2) :=
  match Hm in Logic.eq _ m2' return Logic.eq _ (Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.b m2' n2) with
  | Logic.eq_refl => 
    match Hn in Logic.eq _ n2' return Logic.eq _ (Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.b m1 n2') with
    | Logic.eq_refl => Logic.eq_refl
    end
  end.

Fixpoint mumble_roundtrip1 (m : Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.mumble) 
  : Logic.eq (imported_to_mumble (mumble_to_imported m)) m :=
  match m return Logic.eq (imported_to_mumble (mumble_to_imported m)) m with
  | Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.a => Logic.eq_refl
  | Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.b x y => 
      @b_cong (imported_to_mumble (mumble_to_imported x)) x 
              (imported_nat_to_nat (nat_to_imported_nat y)) y 
              (mumble_roundtrip1 x) (nat_roundtrip1 y)
  | Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.c => Logic.eq_refl
  end.

(* Helper for congruence on imported b constructor *)
Definition b_cong2 (m1 m2 : Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble)
  (n1 n2 : Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_nat)
  (Hm : Logic.eq m1 m2) (Hn : Logic.eq n1 n2) 
  : Logic.eq (Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_b m1 n1)
             (Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_b m2 n2) :=
  match Hm in Logic.eq _ m2' return Logic.eq _ (Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_b m2' n2) with
  | Logic.eq_refl => 
    match Hn in Logic.eq _ n2' return Logic.eq _ (Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_b m1 n2') with
    | Logic.eq_refl => Logic.eq_refl
    end
  end.

Fixpoint mumble_roundtrip2 (m : Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble)
  : Logic.eq (mumble_to_imported (imported_to_mumble m)) m :=
  match m return Logic.eq (mumble_to_imported (imported_to_mumble m)) m with
  | Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_a => Logic.eq_refl
  | Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_b x y => 
      @b_cong2 (mumble_to_imported (imported_to_mumble x)) x 
               (nat_to_imported_nat (imported_nat_to_nat y)) y 
               (mumble_roundtrip2 x) (nat_roundtrip2 y)
  | Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_c => Logic.eq_refl
  end.

(* Convert from Logic.eq to SProp eq *)
Definition mumble_roundtrip1_sprop (m : Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.mumble) 
  : IsomorphismDefinitions.eq (imported_to_mumble (mumble_to_imported m)) m :=
  IsoEq.seq_of_eq (mumble_roundtrip1 m).

Definition mumble_roundtrip2_sprop (m : Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble)
  : IsomorphismDefinitions.eq (mumble_to_imported (imported_to_mumble m)) m :=
  IsoEq.seq_of_eq (mumble_roundtrip2 m).

Definition imported_Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble : Type := Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble.

Instance Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_iso : Iso Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.mumble imported_Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble :=
  @Build_Iso Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.mumble 
             imported_Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble
             mumble_to_imported 
             imported_to_mumble 
             mumble_roundtrip2_sprop 
             mumble_roundtrip1_sprop.

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.mumble := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.mumble Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.mumble Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_iso := {}.
