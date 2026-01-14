From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_better__t__tree__ind__type : SProp := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_better__t__tree__ind__type.

(* Both the original and imported are axioms (Admitted). They are both propositions with no structure.
   We prove the isomorphism as follows: elements of Prop and SProp are proof-irrelevant, so
   we just need functions between them. Since both are axioms/opaque, we use the fact that
   an isomorphism between two propositions (as types) is trivial if we have inhabitants of both.
   However, we don't have inhabitants. So we use the allowed axiom for this isomorphism. *)
   
Axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_better__t__tree__ind__type_iso : Iso Original.LF_DOT_IndPrinciples.LF.IndPrinciples.better_t_tree_ind_type imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_better__t__tree__ind__type.
Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.better_t_tree_ind_type := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_better__t__tree__ind__type := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.better_t_tree_ind_type Original_LF__DOT__IndPrinciples_LF_IndPrinciples_better__t__tree__ind__type_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.better_t_tree_ind_type Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_better__t__tree__ind__type Original_LF__DOT__IndPrinciples_LF_IndPrinciples_better__t__tree__ind__type_iso := {}.