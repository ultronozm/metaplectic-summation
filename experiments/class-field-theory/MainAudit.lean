import MetaplecticSummation
import Mathlib.Util.AssertNoSorry
import Lean

-- The defining integral at a finite place is independent of Archimedean inversion.
assert_no_sorry MetaplecticPoisson.existsUnique_hilbert
assert_no_sorry MetaplecticPoisson.Datum.finite_symbol_power
assert_no_sorry MetaplecticPoisson.Datum.marginal_root_formula_finite_on_test
assert_no_sorry MetaplecticPoisson.Datum.reverse_marginal_finite
assert_no_sorry MetaplecticPoisson.Datum.arch_root_sum
assert_no_sorry MetaplecticPoisson.Datum.tested_marginal_slice_on_test
assert_no_sorry MetaplecticPoisson.Datum.arch_integral_chartDifference_bound
assert_no_sorry MetaplecticPoisson.Datum.kubota_projection
assert_no_sorry MetaplecticPoisson.Datum.hasLocalEvaluationLifts
assert_no_sorry MetaplecticPoisson.Datum.integrable_arch_shear
assert_no_sorry MetaplecticPoisson.Datum.reverse_marginal_on_test
assert_no_sorry MetaplecticPoisson.Datum.fourier_root_kernel
assert_no_sorry MetaplecticPoisson.Datum.fourier_mass
assert_no_sorry MetaplecticPoisson.Datum.schwartz_inversion
assert_no_sorry MetaplecticPoisson.Datum.poisson
assert_no_sorry MetaplecticPoisson.Datum.lineSummation
assert_no_sorry MetaplecticPoisson.Datum.twistedGaussSummation
assert_no_sorry MetaplecticPoisson.ChartFamilyContinuousAt.upper
assert_no_sorry MetaplecticPoisson.ChartFamilyContinuousAt.lower
assert_no_sorry MetaplecticPoisson.Datum.unfolding

assert_no_sorry MetaplecticPoisson.rightCoset_map_restrict_eq
assert_no_sorry MetaplecticPoisson.exists_rationalSL_domain
assert_no_sorry MetaplecticPoisson.rationalUnipotentDomain_unique
assert_no_sorry MetaplecticPoisson.lintegral_arithmeticOrbitSum
assert_no_sorry MetaplecticPoisson.integral_arithmeticOrbitSum
assert_no_sorry MetaplecticPoisson.integrable_iff_arithmeticOrbitSum_norm

assert_no_sorry MetaplecticPoisson.measurePreserving_unipotentTranslate
assert_no_sorry MetaplecticPoisson.range_unipotentFiber
assert_no_sorry MetaplecticPoisson.unipotentFiber_injective
assert_no_sorry MetaplecticPoisson.lintegral_unipotentFiber
assert_no_sorry MetaplecticPoisson.integrable_unipotentFiberIntegral
assert_no_sorry MetaplecticPoisson.integral_unipotentFiber
assert_no_sorry MetaplecticPoisson.integral_arithmeticOrbitSum_eq_fiberIntegral
assert_no_sorry MetaplecticPoisson.eq_zero_of_unipotentFiber_cancellation

assert_no_sorry MetaplecticPoisson.exists_compact_idele_representatives
assert_no_sorry MetaplecticPoisson.cuspIdele_module
assert_no_sorry MetaplecticPoisson.cuspIdele_haarModule
assert_no_sorry MetaplecticPoisson.exists_compact_diagonal_representatives
assert_no_sorry MetaplecticPoisson.diagonalSL_mul_adelicUpper
assert_no_sorry MetaplecticPoisson.map_cusp_shear_measure

assert_no_sorry MetaplecticPoisson.exists_local_iwasawa
assert_no_sorry MetaplecticPoisson.exists_integral_local_iwasawa
assert_no_sorry MetaplecticPoisson.isCompact_boundedAdelicMatrices
assert_no_sorry MetaplecticPoisson.exists_adelic_iwasawa
assert_no_sorry MetaplecticPoisson.exists_integer_cusp_cover
assert_no_sorry MetaplecticPoisson.measurePreserving_triangularRow
assert_no_sorry MetaplecticPoisson.exists_uniform_small_row
assert_no_sorry MetaplecticPoisson.exists_natural_cusp_cover
assert_no_sorry MetaplecticPoisson.exists_siegel_integral_bound
assert_no_sorry MetaplecticPoisson.finiteVolume_slQuotient
assert_no_sorry MetaplecticPoisson.exists_compact_row_modulus_bounds

assert_no_sorry MetaplecticPoisson.Datum.sectionNorm_of_projection
assert_no_sorry MetaplecticPoisson.Datum.weighted_section_bounds
assert_no_sorry MetaplecticPoisson.cusp_row_bounds_on_compact
assert_no_sorry MetaplecticPoisson.Datum.cusp_majorant_sum

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let roots := [
    ``MetaplecticPoisson.existsUnique_hilbert,
    ``MetaplecticPoisson.Datum.finite_symbol_power,
    ``MetaplecticPoisson.Datum.reverse_marginal_finite,
    ``MetaplecticPoisson.Datum.reverse_marginal_on_test,
    ``MetaplecticPoisson.IsHilbertFamily.unique,
    ``MetaplecticPoisson.Datum.arch_difference_pair_integrable,
    ``MetaplecticPoisson.Datum.arch_linearFactor_integral,
    ``MetaplecticPoisson.Datum.arch_linearFactor,
    ``MetaplecticPoisson.Datum.marginalDifference_arch_integrable,
    ``MetaplecticPoisson.Datum.arch_root_contribution,
    ``MetaplecticPoisson.Datum.arch_root_sum_of_right_kernel,
    ``MetaplecticPoisson.Datum.complex_root_sum,
    ``MetaplecticPoisson.Datum.arch_root_sum,
    ``MetaplecticPoisson.Datum.marginal_root_formula_finite_on_test,
    ``MetaplecticPoisson.Datum.marginal_root_formula_finite,
    ``MetaplecticPoisson.Datum.localRootsEquiv,
    ``MetaplecticPoisson.Datum.symbol_power_of_local_right_kernel,
    ``MetaplecticPoisson.Datum.finite_reverse_marginal_on_test,
    ``MetaplecticPoisson.Datum.tame_reverse_marginal_on_test,
    ``MetaplecticPoisson.Datum.localClassPairing_right_kernel,
    ``MetaplecticPoisson.Datum.adelicClass_eq_one_of_local,
    ``MetaplecticPoisson.Datum.rationalClass_le_orthogonal,
    ``MetaplecticPoisson.Datum.mem_rationalClass_iff_eventually,
    ``MetaplecticPoisson.Datum.eq_one_of_orthogonal_of_principal_sIntegers,
    ``MetaplecticPoisson.Datum.card_powerClass_mul_modulus,
    ``MetaplecticPoisson.Datum.involutive_normalized_powerClassTransform,
    ``MetaplecticPoisson.Datum.eventually_powerClassTransform_unitClassTest,
    ``MetaplecticPoisson.Datum.exists_finite_support_detecting_orthogonal,
    ``MetaplecticPoisson.Datum.rationalOrthogonal_eq_of_sUnit_card,
    ``MetaplecticPoisson.Datum.card_sUnitClassImage_on_kummerSupport,
    ``MetaplecticPoisson.Datum.rationalOrthogonal_eq,
    ``MetaplecticPoisson.Datum.rationalClassMap_injective,
    ``MetaplecticPoisson.Datum.powerClass_poisson_finite_support,
    ``MetaplecticPoisson.Datum.axisClassIntegral_sum_eq_axisLine_zero,
    ``MetaplecticPoisson.Datum.adelicTensor_axisLine,
    ``MetaplecticPoisson.Datum.axisLine_poisson,
    ``MetaplecticPoisson.Datum.axisDensity_poisson,
    ``MetaplecticPoisson.Datum.summable_rational_marginal,
    ``MetaplecticPoisson.Datum.constantTerm_identity,
    ``MetaplecticPoisson.Datum.translated_constant_coefficients_eq,
    ``MetaplecticPoisson.Datum.coefficient_eq_slope_integrals,
    ``MetaplecticPoisson.Datum.slope_integral_factorization,
    ``MetaplecticPoisson.Datum.unfolding,
    ``MetaplecticPoisson.Datum.translated_constantTerm_difference,
    ``MetaplecticPoisson.Datum.exists_rational_lift,
    ``MetaplecticPoisson.Datum.coverAction_fourier,
    ``MetaplecticPoisson.Datum.quotient_thetaDifference_mk,
    ``MetaplecticPoisson.Datum.theta_coset_expansion,
    ``MetaplecticPoisson.Datum.exists_theta_coset_lifts,
    ``MetaplecticPoisson.Datum.powerClass_poisson,
    ``MetaplecticPoisson.Datum.weighted_cusp_theta,
    ``MetaplecticPoisson.Datum.cusp_theta_growth,
    ``MetaplecticPoisson.Datum.cusp_offAxis_decay,
    ``MetaplecticPoisson.Datum.cusp_thetaDifference_decay,
    ``MetaplecticPoisson.Datum.exists_integral_lift,
    ``MetaplecticPoisson.Datum.exists_restricted_lift,
    ``MetaplecticPoisson.Datum.coverAction_scalar_of_same_projection,
    ``MetaplecticPoisson.Datum.compact_theta_majorant,
    ``MetaplecticPoisson.Datum.quotientThetaBounds_mk,
    ``MetaplecticPoisson.Datum.quotientThetaBounds_bounded,
    ``MetaplecticPoisson.Datum.arithmeticOrbitSum_thetaDifference,
    ``MetaplecticPoisson.Datum.arithmeticOrbitSum_enorm_le,
    ``MetaplecticPoisson.Datum.integral_thetaOrbitIntegrand_fiber,
    ``MetaplecticPoisson.Datum.thetaDifference_eq_zero_of_quotient_regularity,
    ``MetaplecticPoisson.Datum.thetaDifference_eq_zero_of_continuous_evaluation_products,
    ``MetaplecticPoisson.Datum.local_evaluation_representatives,
    ``MetaplecticPoisson.Datum.thetaDifference_eq_zero_of_local_evaluation_lifts,
    ``MetaplecticPoisson.Datum.hasLocalEvaluationLifts,
    ``MetaplecticPoisson.Datum.thetaDifference_vanishing,
    ``MetaplecticPoisson.Datum.poisson,
    ``MetaplecticPoisson.Datum.lineSummation,
    ``MetaplecticPoisson.Datum.twistedGaussSummation]
  for root in roots do
    logInfo m!"Checking {root}"
    let mut todo := [root]
    let mut seen : NameSet := {}
    repeat
      let n :: ns := todo | break
      todo := ns
      if seen.contains n then continue
      seen := seen.insert n
      let some c := env.find? n | continue
      if root == ``MetaplecticPoisson.Datum.thetaDifference_eq_zero_of_local_evaluation_lifts &&
          n == ``MetaplecticPoisson.Datum.thetaDifference_vanishing then
        throwError "The reduction of Proposition B.6 uses its conclusion"
      let ds := c.getUsedConstantsAsSet
      if ds.contains ``sorryAx then
        if n == ``MetaplecticPoisson.Datum.thetaDifference_vanishing then
          throwError "The proof of Proposition B.6 contains an admission"
        if [``MetaplecticPoisson.Datum.poisson, ``MetaplecticPoisson.Datum.lineSummation,
            ``MetaplecticPoisson.Datum.twistedGaussSummation].contains root &&
            n != ``MetaplecticPoisson.Datum.arch_reverse_marginal_on_test then
          throwError "Unexpected admission {n} in {root}"
        logInfo m!"{n}"
      for k in ds do
        if (k.toString.contains "MetaplecticPoisson") then todo := k :: todo

#print axioms MetaplecticPoisson.Datum.arch_difference_pair_integrable
#print axioms MetaplecticPoisson.Datum.arch_linearFactor_integral
#print axioms MetaplecticPoisson.Datum.arch_linearFactor
#print axioms MetaplecticPoisson.Datum.marginalDifference_arch_integrable
#print axioms MetaplecticPoisson.Datum.arch_root_contribution
#print axioms MetaplecticPoisson.Datum.arch_root_sum_of_right_kernel
#print axioms MetaplecticPoisson.Datum.complex_root_sum
#print axioms MetaplecticPoisson.Datum.localRootsEquiv
#print axioms MetaplecticPoisson.Datum.symbol_power_of_local_right_kernel
#print axioms MetaplecticPoisson.Datum.poisson
#print axioms MetaplecticPoisson.Datum.lineSummation
#print axioms MetaplecticPoisson.Datum.twistedGaussSummation
#print axioms MetaplecticPoisson.IsHilbertFamily.unique

#print axioms MetaplecticPoisson.existsUnique_hilbert
#print axioms MetaplecticPoisson.Datum.finite_symbol_power
#print axioms MetaplecticPoisson.Datum.finite_reverse_marginal_on_test
#print axioms MetaplecticPoisson.Datum.reverse_marginal_on_test
#print axioms MetaplecticPoisson.Datum.reverse_marginal_finite
#print axioms MetaplecticPoisson.Datum.arch_root_sum

#print axioms MetaplecticPoisson.Datum.marginal_root_formula_finite

#print axioms MetaplecticPoisson.Datum.marginal_root_formula_finite_on_test

#print axioms MetaplecticPoisson.Datum.localClassPairing_right_kernel
#print axioms MetaplecticPoisson.Datum.adelicClass_eq_one_of_local
#print axioms MetaplecticPoisson.Datum.rationalClass_le_orthogonal
#print axioms MetaplecticPoisson.Datum.mem_rationalClass_iff_eventually
#print axioms MetaplecticPoisson.Datum.eq_one_of_orthogonal_of_principal_sIntegers
#print axioms MetaplecticPoisson.Datum.card_powerClass_mul_modulus
#print axioms MetaplecticPoisson.Datum.involutive_normalized_powerClassTransform
#print axioms MetaplecticPoisson.Datum.eventually_powerClassTransform_unitClassTest

#print axioms MetaplecticPoisson.Datum.exists_finite_support_detecting_orthogonal
#print axioms MetaplecticPoisson.Datum.rationalOrthogonal_eq_of_sUnit_card
#print axioms MetaplecticPoisson.Datum.card_sUnitClassImage_on_kummerSupport
#print axioms MetaplecticPoisson.Datum.rationalOrthogonal_eq

#print axioms MetaplecticPoisson.Datum.rationalClassMap_injective

#print axioms MetaplecticPoisson.Datum.powerClass_poisson

#print axioms MetaplecticPoisson.Datum.powerClass_poisson_finite_support

#print axioms MetaplecticPoisson.Datum.powerClassTransform_axisClassIntegral
#print axioms MetaplecticPoisson.Datum.axisClassIntegral_sum_eq_axisLine_zero

#print axioms MetaplecticPoisson.Datum.integrable_axis
#print axioms MetaplecticPoisson.Datum.axisClassIntegral_eq_integral_density
#print axioms MetaplecticPoisson.Datum.axisClassIntegral_basic
#print axioms MetaplecticPoisson.Datum.eventually_axisClassIntegral_basic
#print axioms MetaplecticPoisson.Datum.axisLine_basic
#print axioms MetaplecticPoisson.Datum.eventually_axisLine_basic
#print axioms MetaplecticPoisson.Datum.hasSum_powerClass_representatives
#print axioms MetaplecticPoisson.Datum.summable_rational_axis
#print axioms MetaplecticPoisson.Datum.axisDensity_hat_zero_sum_eq_axisLine_zero
#print axioms MetaplecticPoisson.Datum.diagonal_sqrt_modulus_product
#print axioms MetaplecticPoisson.Datum.hat_scaled
#print axioms MetaplecticPoisson.Datum.tsum_hat_scaled
#print axioms GroundTheory.Global.existsUnique_eq_adelicChar_mul
#print axioms GroundTheory.Global.tsum_algebraMap_eq_tsum_adelicFourier
#print axioms MetaplecticPoisson.Character.existsUnique_trace_parameter
#print axioms MetaplecticPoisson.Character.adelic_poisson
#print axioms MetaplecticPoisson.Datum.finiteTensor_mem_schwartzBruhat
#print axioms MetaplecticPoisson.Datum.finiteTensor_axisLine
#print axioms MetaplecticPoisson.Datum.finiteTensor_axisDensity
#print axioms MetaplecticPoisson.Datum.hasSum_axis_powerClasses
#print axioms MetaplecticPoisson.Character.localValue_trace_finite
#print axioms MetaplecticPoisson.Character.localValue_trace_infinite
#print axioms MetaplecticPoisson.Character.finite_trace_annihilator
#print axioms MetaplecticPoisson.Datum.selfDual_volume_trace
#print axioms MetaplecticPoisson.Datum.finite_selfDual_volume_product
#print axioms MetaplecticPoisson.Datum.integral_finiteTensor
#print axioms MetaplecticPoisson.Datum.finite_character_eq_finprod
#print axioms MetaplecticPoisson.Datum.finiteFourier_factorization
#print axioms MetaplecticPoisson.schwartzProduct
#print axioms MetaplecticPoisson.exists_schwartz_tensor
#print axioms MetaplecticPoisson.Datum.exists_infiniteSchwartzTensor
#print axioms MetaplecticPoisson.Datum.adelicTensor_axisLine
#print axioms MetaplecticPoisson.Datum.adelicTensor_axisDensity
#print axioms MetaplecticPoisson.Character.adelicHat_square
#print axioms MetaplecticPoisson.Datum.adelicHat_tensor
#print axioms MetaplecticPoisson.Datum.additivePoisson_tensor
#print axioms MetaplecticPoisson.Datum.axisLine_poisson
#print axioms MetaplecticPoisson.Datum.axisDensity_poisson

#print axioms MetaplecticPoisson.Datum.rational_marginal_supported_on_finite_classes
#print axioms MetaplecticPoisson.Datum.summable_rational_marginal
#print axioms MetaplecticPoisson.Datum.constantTerm_identity

#print axioms MetaplecticPoisson.Datum.axisBoundary_eq_zero_of_local
#print axioms MetaplecticPoisson.Datum.translated_constant_coefficients_eq

#print axioms MetaplecticPoisson.Datum.quotient_measure_fundamental
#print axioms MetaplecticPoisson.Datum.measurable_of_quotientLift
#print axioms MetaplecticPoisson.Datum.integral_periodization
#print axioms MetaplecticPoisson.Datum.lintegral_enorm_periodization_le
#print axioms MetaplecticPoisson.Datum.translatedTheta_orbit_sum
#print axioms MetaplecticPoisson.Datum.measurable_adelicSlopeSlice
#print axioms MetaplecticPoisson.Datum.integral_quotientFrequency
#print axioms MetaplecticPoisson.Datum.coefficient_eq_slope_integrals

#print axioms MetaplecticPoisson.Datum.summable_slope_integrals
#print axioms MetaplecticPoisson.Datum.slope_integral_factorization
#print axioms MetaplecticPoisson.Datum.unfolding
#print axioms MetaplecticPoisson.Datum.translated_constantTerm_difference

#print axioms MetaplecticPoisson.Datum.exists_rational_lift
#print axioms MetaplecticPoisson.Datum.coverAction_fourier
#print axioms MetaplecticPoisson.Datum.quotient_thetaDifference_mk
#print axioms MetaplecticPoisson.rationalBottomRowEquiv
#print axioms MetaplecticPoisson.Datum.theta_coset_expansion
#print axioms MetaplecticPoisson.Datum.exists_theta_coset_lifts

#print axioms MetaplecticPoisson.exists_rationalSL_domain
#print axioms MetaplecticPoisson.rationalUnipotentDomain_unique
#print axioms MetaplecticPoisson.lintegral_arithmeticOrbitSum
#print axioms MetaplecticPoisson.integral_arithmeticOrbitSum
#print axioms MetaplecticPoisson.integrable_iff_arithmeticOrbitSum_norm
#print axioms MetaplecticPoisson.rightCoset_map_restrict_eq

#print axioms MetaplecticPoisson.measurePreserving_unipotentTranslate
#print axioms MetaplecticPoisson.range_unipotentFiber
#print axioms MetaplecticPoisson.unipotentFiber_injective
#print axioms MetaplecticPoisson.lintegral_unipotentFiber
#print axioms MetaplecticPoisson.integrable_unipotentFiberIntegral
#print axioms MetaplecticPoisson.integral_unipotentFiber
#print axioms MetaplecticPoisson.integral_arithmeticOrbitSum_eq_fiberIntegral
#print axioms MetaplecticPoisson.eq_zero_of_unipotentFiber_cancellation

#print axioms MetaplecticPoisson.exists_compact_idele_representatives
#print axioms MetaplecticPoisson.cuspIdele_module
#print axioms MetaplecticPoisson.cuspIdele_haarModule
#print axioms MetaplecticPoisson.exists_compact_diagonal_representatives
#print axioms MetaplecticPoisson.diagonalSL_mul_adelicUpper
#print axioms MetaplecticPoisson.map_cusp_shear_measure

#print axioms MetaplecticPoisson.exists_local_iwasawa
#print axioms MetaplecticPoisson.exists_integral_local_iwasawa
#print axioms MetaplecticPoisson.isCompact_boundedAdelicMatrices
#print axioms MetaplecticPoisson.exists_adelic_iwasawa
#print axioms MetaplecticPoisson.exists_integer_cusp_cover
#print axioms MetaplecticPoisson.measurePreserving_triangularRow
#print axioms MetaplecticPoisson.exists_uniform_small_row
#print axioms MetaplecticPoisson.exists_natural_cusp_cover
#print axioms MetaplecticPoisson.exists_siegel_integral_bound
#print axioms MetaplecticPoisson.finiteVolume_slQuotient
#print axioms MetaplecticPoisson.exists_compact_row_modulus_bounds

#print axioms MetaplecticPoisson.Datum.sectionNorm_of_projection
#print axioms MetaplecticPoisson.Datum.weighted_section_bounds
#print axioms MetaplecticPoisson.cusp_row_bounds_on_compact
#print axioms MetaplecticPoisson.Datum.cusp_majorant_sum
#print axioms MetaplecticPoisson.Datum.weighted_cusp_theta
#print axioms MetaplecticPoisson.Datum.cusp_theta_growth
#print axioms MetaplecticPoisson.Datum.cusp_offAxis_decay
#print axioms MetaplecticPoisson.Datum.cusp_thetaDifference_decay

#print axioms MetaplecticPoisson.Datum.exists_integral_lift
#print axioms MetaplecticPoisson.Datum.exists_restricted_lift
#print axioms MetaplecticPoisson.Datum.coverAction_scalar_of_same_projection
#print axioms MetaplecticPoisson.Datum.compact_theta_majorant
#print axioms MetaplecticPoisson.Datum.quotientThetaBounds_mk
#print axioms MetaplecticPoisson.Datum.quotientThetaBounds_bounded
#print axioms MetaplecticPoisson.Datum.arithmeticOrbitSum_thetaDifference
#print axioms MetaplecticPoisson.Datum.arithmeticOrbitSum_enorm_le
#print axioms MetaplecticPoisson.Datum.integral_thetaOrbitIntegrand_fiber
#print axioms MetaplecticPoisson.Datum.thetaDifference_eq_zero_of_quotient_regularity
#print axioms MetaplecticPoisson.Datum.thetaDifference_eq_zero_of_continuous_evaluation_products
#print axioms MetaplecticPoisson.Datum.local_evaluation_representatives
#print axioms MetaplecticPoisson.Datum.thetaDifference_eq_zero_of_local_evaluation_lifts

#print axioms MetaplecticPoisson.Datum.kubota_projection
#print axioms MetaplecticPoisson.Datum.hasLocalEvaluationLifts
#print axioms MetaplecticPoisson.Datum.thetaDifference_vanishing
