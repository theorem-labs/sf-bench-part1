From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Import the list isomorphism *)
From IsomorphismChecker.Isomorphisms Require U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo' : Type -> Type := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo'.

Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo'_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.foo' x1) (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo' x2).
Proof.
  intros x1 x2 Hx.
  (* Get the list isomorphism *)
  pose proof (U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Original_LF__DOT__Poly_LF_Poly_list_iso Hx) as Hlist.
  unshelve eapply Build_Iso.
  - (* to: Original.foo' x1 -> Imported.foo' x2 *)
    exact (fix to_foo (f : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.foo' x1) : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo' x2 :=
      match f with
      | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.C1 _ l f' => 
          Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo'_C1 x2 (to Hlist l) (to_foo f')
      | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.C2 _ => 
          Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo'_C2 x2
      end).
  - (* from: Imported.foo' x2 -> Original.foo' x1 *)
    exact (fix from_foo (f : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo' x2) : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.foo' x1 :=
      match f with
      | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo'_C1 _ l f' => 
          Original.LF_DOT_IndPrinciples.LF.IndPrinciples.C1 x1 (from Hlist l) (from_foo f')
      | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo'_C2 _ => 
          Original.LF_DOT_IndPrinciples.LF.IndPrinciples.C2 x1
      end).
  - (* to_from *)
    intro f.
    induction f as [l f' IH | ].
    + simpl.
      apply (IsoEq.f_equal2 (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo'_C1 x2) (to_from Hlist l) IH).
    + apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro f.
    induction f as [l f' IH | ].
    + simpl.
      apply (IsoEq.f_equal2 (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.C1 x1) (from_to Hlist l) IH).
    + apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.foo' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.foo' Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.foo' Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo' Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo'_iso := {}.