From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_or : SProp -> SProp -> SProp := Imported.or.

(* Convert from Coq's or to imported or *)
Definition or_to_imported (A B : Prop) (A' B' : SProp) (isoA : Iso A A') (isoB : Iso B B') 
  (x : or A B) : imported_or A' B' :=
  match x with
  | or_introl a => Imported.or_or_introl A' B' (to isoA a)
  | or_intror b => Imported.or_or_intror A' B' (to isoB b)
  end.

(* Convert from imported or to Coq's or using sinhabitant and or_indl *)
Definition imported_to_or (A B : Prop) (A' B' : SProp) (isoA : Iso A A') (isoB : Iso B B')
  (x : imported_or A' B') : or A B :=
  sinhabitant (Imported.or_indl A' B' (fun _ => SInhabited (or A B))
    (fun a' => sinhabits (or_introl (from isoA a')))
    (fun b' => sinhabits (or_intror (from isoB b')))
    x).

(* Round-trip in SProp direction is trivial by eq_refl since all SProp proofs are equal *)
Definition or_to_from (A B : Prop) (A' B' : SProp) (isoA : Iso A A') (isoB : Iso B B')
  (x : imported_or A' B') : IsomorphismDefinitions.eq (@or_to_imported A B A' B' isoA isoB (@imported_to_or A B A' B' isoA isoB x)) x :=
  IsomorphismDefinitions.eq_refl.

(* Round-trip in Prop direction uses proof irrelevance *)
Definition or_from_to (A B : Prop) (A' B' : SProp) (isoA : Iso A A') (isoB : Iso B B')
  (x : or A B) : IsomorphismDefinitions.eq (@imported_to_or A B A' B' isoA isoB (@or_to_imported A B A' B' isoA isoB x)) x :=
  seq_of_peq_t (ProofIrrelevance.proof_irrelevance _ _ _).

Instance or_iso : (forall (x1 : Prop) (x2 : SProp) (hx1 : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx3 : Iso x3 x4), Iso (or x1 x3) (imported_or x2 x4)) :=
  fun A A' isoA B B' isoB => @Build_Iso (or A B) (imported_or A' B')
    (@or_to_imported A B A' B' isoA isoB)
    (@imported_to_or A B A' B' isoA isoB)
    (@or_to_from A B A' B' isoA isoB)
    (@or_from_to A B A' B' isoA isoB).

Instance: KnownConstant or := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.or := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor or or_iso := {}.
Instance: IsoStatementProofBetween or Imported.or or_iso := {}.