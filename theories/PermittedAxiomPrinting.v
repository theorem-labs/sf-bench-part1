(* This file replicates the module structure of axioms that we permit, to ensure that when we print assumptions, we get fully qualified names only. *)
Module Export Coq.
  Module Export Init.
    Module Export Logic.
      Definition eq := I.
    End Logic.
  End Init.

  Module Export Strings.
    Module PrimStringAxioms.
      Definition of_to_list := I.
      Definition to_list_length := I.
      Definition to_list_char63_valid := I.
      Definition length_spec := I.
      Definition get_spec := I.
      Definition make_spec := I.
      Definition sub_spec := I.
      Definition cat_spec := I.
      Definition compare_spec := I.
    End PrimStringAxioms.
  End Strings.

  Module Export Numbers.
    Module Export Cyclic.
      Module Export Int63.
        Module Uint63Axioms.
          Definition of_to_Z := I.
          Definition lsl_spec := I.
          Definition lsr_spec := I.
          Definition land_spec := I.
          Definition lor_spec := I.
          Definition lxor_spec := I.
          Definition add_spec := I.
          Definition sub_spec := I.
          Definition mul_spec := I.
          Definition mulc_spec := I.
          Definition div_spec := I.
          Definition mod_spec := I.
          Definition eqb_correct := I.
          Definition eqb_refl := I.
          Definition ltb_spec := I.
          Definition leb_spec := I.
          Definition compare_def_spec := I.
          Definition head0_spec := I.
          Definition tail0_spec := I.
          Definition addc_def_spec := I.
          Definition addcarryc_def_spec := I.
          Definition subc_def_spec := I.
          Definition subcarryc_def_spec := I.
          Definition diveucl_def_spec := I.
          Definition diveucl_21_spec := I.
          Definition addmuldiv_def_spec := I.
        End Uint63Axioms.
        Module Sint63Axioms.
          Definition asr_spec := I.
          Definition div_spec := I.
          Definition mod_spec := I.
          Definition ltb_spec := I.
          Definition leb_spec := I.
          Definition compare_spec := I.
        End Sint63Axioms.
        Module PrimInt63.
          Definition int := I.
          Definition lsl := I.
          Definition lsr := I.
          Definition land := I.
          Definition lor := I.
          Definition lxor := I.
          Definition asr := I.
          Definition add := I.
          Definition sub := I.
          Definition mul := I.
          Definition mulc := I.
          Definition div := I.
          Definition mod := I.
          Definition divs := I.
          Definition mods := I.
          Definition eqb := I.
          Definition ltb := I.
          Definition leb := I.
          Definition ltsb := I.
          Definition lesb := I.
          Definition addc := I.
          Definition addcarryc := I.
          Definition subc := I.
          Definition subcarryc := I.
          Definition diveucl := I.
          Definition diveucl_21 := I.
          Definition addmuldiv := I.
          Definition compare := I.
          Definition compares := I.
          Definition head0 := I.
          Definition tail0 := I.
        End PrimInt63.
      End Int63.
    End Cyclic.

    Module Export Natural.
      Module Export Abstract.
        Module NAxioms.
          Definition pred_0 := I.
          Definition mod_upper_bound := I.
          Definition recursion_0 := I.
          Definition recursion_succ := I.
        End NAxioms.
      End Abstract.
    End Natural.

    Module Export NatInt.
      Module NZLog.
        Definition log2_spec := I.
        Definition log2_nonpos := I.
      End NZLog.
      Module NZGcd.
        Definition gcd_divide_l := I.
        Definition gcd_divide_r := I.
        Definition gcd_greatest := I.
        Definition gcd_nonneg := I.
      End NZGcd.
      Module NZDiv.
        Definition div_mod := I.
        Definition mod_bound_pos := I.
        Definition div_0_r := I.
        Definition mod_0_r := I.
      End NZDiv.
      Module NZAxioms.
        Definition pred_succ := I.
        Definition bi_induction := I.
        Definition one_succ := I.
        Definition two_succ := I.
        Definition add_0_l := I.
        Definition add_succ_l := I.
        Definition sub_0_r := I.
        Definition sub_succ_r := I.
        Definition mul_0_l := I.
        Definition mul_succ_l := I.
        Definition lt_eq_cases := I.
        Definition lt_irrefl := I.
        Definition lt_succ_r := I.
        Definition square_spec := I.
      End NZAxioms.
      Module NZPow.
        Definition pow_0_r := I.
        Definition pow_succ_r := I.
        Definition pow_neg_r := I.
      End NZPow.
      Module NZSqrt.
        Definition sqrt_spec := I.
        Definition sqrt_neg := I.
      End NZSqrt.
      Module NZParity.
        Definition even_spec := I.
        Definition odd_spec := I.
      End NZParity.
      Module NZBits.
        Definition testbit_odd_0 := I.
        Definition testbit_even_0 := I.
        Definition testbit_odd_succ := I.
        Definition testbit_even_succ := I.
        Definition testbit_neg_r := I.
        Definition shiftr_spec := I.
        Definition shiftl_spec_high := I.
        Definition shiftl_spec_low := I.
        Definition land_spec := I.
        Definition lor_spec := I.
        Definition ldiff_spec := I.
        Definition lxor_spec := I.
        Definition div2_spec := I.
      End NZBits.
    End NatInt.

    Module Export Integer.
      Module Export Abstract.
        Module ZAxioms.
          Definition succ_pred := I.
          Definition opp_0 := I.
          Definition opp_succ := I.
          Definition abs_eq := I.
          Definition abs_neq := I.
          Definition sgn_null := I.
          Definition sgn_pos := I.
          Definition sgn_neg := I.
          Definition mod_pos_bound := I.
          Definition mod_neg_bound := I.
          Definition quot_rem := I.
          Definition rem_bound_pos := I.
          Definition rem_opp_l := I.
          Definition rem_opp_r := I.
        End ZAxioms.
        Module ZDivEucl.
          Definition mod_always_pos := I.
        End ZDivEucl.
      End Abstract.
    End Integer.
  End Numbers.

  Module Export Array.
    Module ArrayAxioms.
      Definition get_out_of_bounds := I.
      Definition get_set_same := I.
      Definition get_set_other := I.
      Definition default_set := I.
      Definition get_make := I.
      Definition leb_length := I.
      Definition length_make := I.
      Definition length_set := I.
      Definition get_copy := I.
      Definition length_copy := I.
      Definition array_ext := I.
    End ArrayAxioms.
  End Array.

  Module Export Floats.
    Module FloatAxioms.
      Definition Prim2SF_valid := I.
      Definition SF2Prim_Prim2SF := I.
      Definition Prim2SF_SF2Prim := I.
      Definition opp_spec := I.
      Definition abs_spec := I.
      Definition eqb_spec := I.
      Definition ltb_spec := I.
      Definition leb_spec := I.
      Definition compare_spec := I.
      Definition classify_spec := I.
      Definition mul_spec := I.
      Definition add_spec := I.
      Definition sub_spec := I.
      Definition div_spec := I.
      Definition sqrt_spec := I.
      Definition of_uint63_spec := I.
      Definition normfr_mantissa_spec := I.
      Definition frshiftexp_spec := I.
      Definition ldshiftexp_spec := I.
      Definition next_up_spec := I.
      Definition next_down_spec := I.
    End FloatAxioms.
    Module PrimFloat.
      Definition float := I.
      Definition classify := I.
      Definition abs := I.
      Definition sqrt := I.
      Definition opp := I.
      Definition eqb := I.
      Definition ltb := I.
      Definition leb := I.
      Definition compare := I.
      Definition mul := I.
      Definition add := I.
      Definition sub := I.
      Definition div := I.
      Definition of_uint63 := I.
      Definition normfr_mantissa := I.
      Definition frshiftexp := I.
      Definition ldshiftexp := I.
      Definition next_up := I.
      Definition next_down := I.
      Module Leibniz.
        Definition eqb := I.
      End Leibniz.
    End PrimFloat.
  End Floats.

  Module Export FSets.
    Module FMapInterface.
      Definition eq_refl := I.
      Definition eq_sym := I.
      Definition eq_trans := I.
      Definition lt_trans := I.
      Definition lt_not_eq := I.
    End FMapInterface.
  End FSets.

  Module Export Compat.
    Module AdmitAxiom.
      Definition proof_admitted := I.
    End AdmitAxiom.
  End Compat.

  Module Export Structures.
    Module OrderedType.
      Definition eq_refl := I.
      Definition eq_sym := I.
      Definition eq_trans := I.
      Definition lt_trans := I.
      Definition lt_not_eq := I.
    End OrderedType.
    Module Orders.
      Definition le_lteq := I.
      Definition compare_spec := I.
      Definition lt_total := I.
      Definition leb_total := I.
      Definition leb_trans := I.
    End Orders.
    Module OrderedTypeEx.
      Definition lt_trans := I.
      Definition lt_not_eq := I.
    End OrderedTypeEx.
    Module Equalities.
      Definition eq_refl := I.
      Definition eq_sym := I.
      Definition eq_trans := I.
    End Equalities.
    Module OrdersFacts.
      Definition compare_eq_iff := I.
      Definition compare_lt_iff := I.
      Definition compare_le_iff := I.
      Definition compare_antisym := I.
    End OrdersFacts.
  End Structures.

  Module Export Logic.
    Module Epsilon.
      Definition epsilon_statement := I.
    End Epsilon.
    Module FunctionalExtensionality.
      Definition functional_extensionality_dep := I.
    End FunctionalExtensionality.
    Module ProofIrrelevance.
      Definition proof_irrelevance := I.
      Module PI.
        Definition proof_irrelevance := I.
      End PI.
    End ProofIrrelevance.
    Module Eqdep_dec.
      Definition eq_dec := I.
    End Eqdep_dec.
    Module EqdepFacts.
      Definition eq_rect_eq := I.
    End EqdepFacts.
    Module Description.
      Definition constructive_definite_description := I.
    End Description.
    Module IndefiniteDescription.
      Definition constructive_indefinite_description := I.
    End IndefiniteDescription.
    Module RelationalChoice.
      Definition relational_choice := I.
    End RelationalChoice.
    Module PropExtensionality.
      Definition propositional_extensionality := I.
    End PropExtensionality.
    Module ExtensionalFunctionRepresentative.
      Definition extensional_function_representative := I.
    End ExtensionalFunctionRepresentative.
    Module ProofIrrelevanceFacts.
      Definition proof_irrelevance := I.
    End ProofIrrelevanceFacts.
    Module ClassicalEpsilon.
      Definition constructive_indefinite_description := I.
    End ClassicalEpsilon.
    Module Eqdep.
      Definition eq_rect_eq := I.
    End Eqdep.
    Module Classical_Prop.
      Definition classic := I.
    End Classical_Prop.
    Module ClassicalUniqueChoice.
      Definition dependent_unique_choice := I.
    End ClassicalUniqueChoice.
  End Logic.

  Module Export Reals.
    Module ClassicalDedekindReals.
      Definition sig_forall_dec := I.
      Definition sig_not_dec := I.
    End ClassicalDedekindReals.
    Module Rdefinitions.
      Definition Rabst := I.
      Definition Rrepr := I.
      Definition Rquot1 := I.
      Definition Rquot2 := I.
    End Rdefinitions.
  End Reals.

  Module Export Sets.
    Module Ensembles.
      Definition Extensionality_Ensembles := I.
    End Ensembles.
  End Sets.

  Module Export ZArith.
    Module Int.
      Definition eqb := I.
      Definition ltb := I.
      Definition leb := I.
      Definition gt_le_dec := I.
      Definition ge_lt_dec := I.
      Definition eq_dec := I.
      Definition i2z_eq := I.
      Definition i2z_0 := I.
      Definition i2z_1 := I.
      Definition i2z_2 := I.
      Definition i2z_3 := I.
      Definition i2z_add := I.
      Definition i2z_opp := I.
      Definition i2z_sub := I.
      Definition i2z_mul := I.
      Definition i2z_max := I.
      Definition i2z_eqb := I.
      Definition i2z_ltb := I.
      Definition i2z_leb := I.
    End Int.
  End ZArith.

  Module Export MSets.
    Module MSetRBT.
      Definition remove_min_spec1 := I.
      Definition remove_min_spec2 := I.
    End MSetRBT.
  End MSets.
End Coq.

Module Stdlib := Coq.
Module Corelib := Coq.

Module Export IsomorphismChecker.
  Module IsomorphismDefinitions.
    Definition eq := I.
  End IsomorphismDefinitions.
  Module Export EqualityLemmas.
    Definition SInhabited_Prop_injective := I.
    Definition sinhabitant := I.
    Definition eq_SInhabited_inhabited := I.
    Module Export IsoEq.
      Definition functional_extensionality_dep := I.
    End IsoEq.
  End EqualityLemmas.
End IsomorphismChecker.
