import MetaplecticSummation
import Lean
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
    ``MetaplecticPoisson.Datum.powerClass_poisson,
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
      let ds := c.getUsedConstantsAsSet
      if ds.contains ``sorryAx then logInfo m!"{n}"
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
