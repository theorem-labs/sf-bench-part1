From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat : Type := Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat.

Instance Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat_iso : Iso Original.LF_DOT_Basics.LF.Basics.NatPlayground.nat imported_Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat.
Proof.
  unshelve eapply Build_Iso.
  - (* to: Original.nat -> Imported.nat *)
    exact (fix to_nat (n : Original.LF_DOT_Basics.LF.Basics.NatPlayground.nat) : imported_Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat :=
      match n with
      | Original.LF_DOT_Basics.LF.Basics.NatPlayground.O => Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat_O
      | Original.LF_DOT_Basics.LF.Basics.NatPlayground.S n' => Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat_S (to_nat n')
      end).
  - (* from: Imported.nat -> Original.nat *)
    exact (fix from_nat (n : imported_Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat) : Original.LF_DOT_Basics.LF.Basics.NatPlayground.nat :=
      match n with
      | Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat_O => Original.LF_DOT_Basics.LF.Basics.NatPlayground.O
      | Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat_S n' => Original.LF_DOT_Basics.LF.Basics.NatPlayground.S (from_nat n')
      end).
  - (* to_from *)
    intro n.
    induction n as [|n' IH].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl.
      apply (IsoEq.f_equal Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat_S IH).
  - (* from_to *)
    intro n.
    induction n as [|n' IH].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl.
      apply (IsoEq.f_equal Original.LF_DOT_Basics.LF.Basics.NatPlayground.S IH).
Defined.

Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.NatPlayground.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.NatPlayground.nat Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.NatPlayground.nat Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat_iso := {}.