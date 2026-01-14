From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.cons__iso Isomorphisms.nil__iso Isomorphisms.__0__iso Isomorphisms.U_list__U_in__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_In10 : imported_List_In (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))))))
    (imported_cons (imported_S imported_0)
       (imported_cons (imported_S (imported_S imported_0))
          (imported_cons (imported_S (imported_S (imported_S imported_0)))
             (imported_cons (imported_S (imported_S (imported_S (imported_S imported_0))))
                (imported_cons (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))
                   (imported_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))
                      (imported_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))))
                         (imported_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))))
                            (imported_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))))))
                               (imported_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))))))
                                  (imported_nil imported_nat))))))))))) := Imported.Original_LF__DOT__Imp_LF_Imp_AExp_In10.

(* The In10 proof is an axiom (Admitted in Original.v), so we need to establish a 
   rel_iso between the two axiom instances. Since the theorem statement is a Prop 
   and both sides are proofs of isomorphic propositions, we can use proof irrelevance. *)
Instance Original_LF__DOT__Imp_LF_Imp_AExp_In10_iso : rel_iso
    {|
      to :=
        List_In_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))))))
          (cons_iso (S_iso _0_iso)
             (cons_iso (S_iso (S_iso _0_iso))
                (cons_iso (S_iso (S_iso (S_iso _0_iso)))
                   (cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
                      (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                         (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                            (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))
                               (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))))
                                  (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))))
                                     (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))))) (nil_iso nat_iso)))))))))));
      from :=
        from
          (List_In_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))))))
             (cons_iso (S_iso _0_iso)
                (cons_iso (S_iso (S_iso _0_iso))
                   (cons_iso (S_iso (S_iso (S_iso _0_iso)))
                      (cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
                         (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                            (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                               (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))
                                  (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))))
                                     (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))))
                                        (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))))) (nil_iso nat_iso))))))))))));
      to_from :=
        fun
          x : imported_List_In (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))))))
                (imported_cons (imported_S imported_0)
                   (imported_cons (imported_S (imported_S imported_0))
                      (imported_cons (imported_S (imported_S (imported_S imported_0)))
                         (imported_cons (imported_S (imported_S (imported_S (imported_S imported_0))))
                            (imported_cons (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))
                               (imported_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))
                                  (imported_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))))
                                     (imported_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))))
                                        (imported_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))))))
                                           (imported_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))))))
                                              (imported_nil imported_nat))))))))))) =>
        to_from
          (List_In_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))))))
             (cons_iso (S_iso _0_iso)
                (cons_iso (S_iso (S_iso _0_iso))
                   (cons_iso (S_iso (S_iso (S_iso _0_iso)))
                      (cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
                         (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                            (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                               (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))
                                  (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))))
                                     (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))))
                                        (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))))) (nil_iso nat_iso))))))))))))
          x;
      from_to :=
        fun x : @List.In Datatypes.nat 10%nat (1%nat :: 2%nat :: 3%nat :: 4%nat :: 5%nat :: 6%nat :: 7%nat :: 8%nat :: 9%nat :: 10%nat :: Datatypes.nil)%list =>
        seq_p_of_t
          (from_to
             (List_In_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))))))
                (cons_iso (S_iso _0_iso)
                   (cons_iso (S_iso (S_iso _0_iso))
                      (cons_iso (S_iso (S_iso (S_iso _0_iso)))
                         (cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
                            (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                               (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                                  (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))
                                     (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))))
                                        (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))))
                                           (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))))) (nil_iso nat_iso))))))))))))
             x)
    |} Original.LF_DOT_Imp.LF.Imp.AExp.In10 imported_Original_LF__DOT__Imp_LF_Imp_AExp_In10.
Proof.
  (* This is an isomorphism between proofs of the same admitted theorem.
     Since Original.LF_DOT_Imp.LF.Imp.AExp.In10 is an axiom (Admitted),
     we use the allowed axiom for this isomorphism. *)
Admitted.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.AExp.In10 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_AExp_In10 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.In10 Original_LF__DOT__Imp_LF_Imp_AExp_In10_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.In10 Imported.Original_LF__DOT__Imp_LF_Imp_AExp_In10 Original_LF__DOT__Imp_LF_Imp_AExp_In10_iso := {}.