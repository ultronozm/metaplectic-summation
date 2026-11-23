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
    ``MetaplecticPoisson.Datum.localRootsEquiv,
    ``MetaplecticPoisson.Datum.symbol_power_of_local_right_kernel,
    ``MetaplecticPoisson.Datum.finite_reverse_marginal_on_test,
    ``MetaplecticPoisson.Datum.tame_reverse_marginal_on_test,
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
