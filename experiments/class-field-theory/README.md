# Hilbert symbols and Appendix A

The original project at `30f6008` uses Lean v4.32.2 and Mathlib `905b95818eb32af7874a58b427f50c1711a5e96c`. The experiment uses the ClassFieldTheory sources under `DedekindZetaZeroFree/vendor/class-field-theory` at parent commit `09afbb4ce6570c1615d58509dc197fc9f0956b7d`. Its package pins Lean v4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. All dependency tests used separate copies.

## What the pins support

* **ClassFieldTheory on v4.32.2.** Building the three imports in [Audit.lean](Audit.lean) fails. The first independent failures include the import of `Mathlib.Basic.Denumerable` in `DiscreteValuationField/IwasawaIndexing.lean` and `MonoidHom.domRestrict` in `DiscreteValuationField/Units.lean`, line 698.
* **ClassFieldTheory on v4.35.0-rc2.** The two Kummer modules build as vendored. The global import also traverses files the parent project edited for rc3. On rc2, `LiesOver.continuous_completionMap` has implicit place arguments, and `HeightOneSpectrum.valuation_liesOver` uses `ramificationIdx'`. The four-file [compatibility patch](class-field-theory-rc2.patch) restores the rc2 proof steps in the scratch copy.
* **MetaplecticSummation on v4.35.0-rc2.** Starting at `30f6008`, a [four-file patch](metaplectic-arithmetic-rc2.patch) builds `MetaplecticSummation.Arithmetic`. This lets the experiment use the actual project types `LocalField`, `diagonal`, and `Mu`. A full forward build still fails, including in `LocalCharacterScaling.lean` at lines 50–51 and `ArchimedeanFourierDecay.lean` at line 48.

## Integrated rc2 results

The project theorem `MetaplecticPoisson.existsUnique_hilbert` now combines the constructed family with weak approximation. The proof of uniqueness imports only the local arithmetic and the definition of a normalized family. [Arithmetic.lean](../../MetaplecticSummation/Arithmetic.lean) · [HilbertUniqueness.lean](../../MetaplecticSummation/HilbertUniqueness.lean)

For the project's chosen symbol, `Datum.finite_symbol_power` identifies its right radical using the injective complex embedding. The unconditional theorem `Datum.reverse_marginal_finite` proves Lemma A.2 for arbitrary finite primes, including wild ones. The all-place statement specializes to that theorem at finite places. On the vendored rc2 build Lean reports only the standard axioms for existence and uniqueness and for the unconditional finite marginal. At infinite places the proof of the full reverse marginal is still open. [RootSum.lean](../../MetaplecticSummation/Marginals/RootSum.lean) · [FiniteTestInversion.lean](../../MetaplecticSummation/Marginals/FiniteTestInversion.lean) · [TestInversion.lean](../../MetaplecticSummation/Marginals/TestInversion.lean)

## The arithmetic comparison

Write $B$ for Yamaguchi's pairing and $q$ for the residue-field cardinality. His exponent with a valuation-ring unit $u$ in the first slot is $-\operatorname{valuationMap}(x)$. His inverse uniformizer has value $+1$. For an ordinary uniformizer $\pi$ of norm $q^{-1}$, this gives $B(u,\pi)$ equal to the unique lift of $\bar u^{(q-1)/n}$. By skew-symmetry the paper's symbol is $B(a,b)^{-1}=B(b,a)$. Inverting the values while retaining the order also retains the **right** kernel. [TameConvention.lean](TameConvention.lean)

At a finite place the candidate uses the concrete `finitePlaceAdicHilbertPairingFamily`, transported from the absolute-value completion to the adic completion used by this project. If $e_v:\mu_n(F)\simeq\mu_n(F_v)$ is induced by the diagonal embedding, its value is $e_v^{-1}(B_v([a],[b])^{-1})$. The primitive root in $F$ makes $e_v$ onto all local roots. The right-kernel test for this candidate works for every finite place, including those above $n$. [PairBridge.lean](PairBridge.lean)

The infinite factor is $-1$ precisely when $n=2$, the place is real, and both real coordinates are negative. It is $1$ otherwise. Inversion fixes both signs. In the combined rc2 experiment, Lean checks the value on the diagonal for every infinite place, the diagonal finite values, finite support, and the resulting product formula. [GlobalBridge.lean](GlobalBridge.lean)

On the project pin, `IsHilbertFamily.unique` proves uniqueness of a family satisfying the stated normalization and reciprocity. Tame reduction first fixes the uniformizer–unit value, then bilinearity, skew-symmetry and the value on $(a,-a)$ give equality on all tame pairs. At the remaining finitely many places, simultaneous weak approximation and continuity isolate the ratio of the two symbols one place at a time. [HilbertUniqueness.lean](../../MetaplecticSummation/HilbertUniqueness.lean)

On rc2, the tame comparison now holds on arbitrary completion units. The proof pulls both arguments back along `relativeFinitePlaceCompletionAlgEquiv`, compares the norm of a uniformizer with the discrete valuation, identifies the residue-field cardinality with the ideal norm, and converts residue equality into the strict norm inequality required by `IsHilbertFamily.tame_uniformizer`. It also proves the unit–unit law and the relation on $(a,-a)$. [CompletionTame.lean](CompletionTame.lean)

The finite symbol factors through the power classes. Openness of the subgroup of powers gives local constancy in each pair of inputs, including at the primes above the degree. On the infinite side, the real sign is locally constant on the units. Together with the product formula, these facts prove every field of the project's `IsHilbertFamily` structure in the combined rc2 experiment. The kernel audit of `MetaplecticBridge.family_spec` lists only `propext`, `Classical.choice`, and `Quot.sound`. [FiniteLaws.lean](FiniteLaws.lean) · [InfiniteLaws.lean](InfiniteLaws.lean) · [HilbertExistence.lean](HilbertExistence.lean)

## Archimedean integrals

For real and complex Schwartz functions, `arch_difference_pair_integrable` proves absolute integrability of $h(t)(f((t-a)u)-f(u))$ against $d^\times u\,dt$. The Lipschitz estimate gives $O(\|u\|)$ at zero. Changing additive variables gives the reciprocal normalized modulus in the first tail term, and Schwartz decay bounds the other term by $O(\|u\|^{-1})$. The modulus is the square of the Euclidean norm at a complex place. The admission-free theorem `arch_linearFactor_integral` moves Fourier transformation across the affine pairing and evaluates the dual integral. `arch_root_contribution` sums the identity over the distinct roots of an $n$-th power for a Schwartz frequency test compactly supported away from zero. Its specialization `arch_linearFactor` to the paper’s Hilbert-twisted difference uses `existsUnique_hilbert` to evaluate the symbol on an $n$-th power. The joint chart integral and recovery of the pointwise marginal are further steps in Lemma A.2. [ArchimedeanDifference.lean](../../MetaplecticSummation/ArchimedeanDifference.lean)

## Original v4.32.2 build and admission audit

The project build on v4.32.2 and the three external import targets on rc2 completed. The declarations in [Audit.lean](Audit.lean), the sign calculation, the coherent candidate's right kernel, and its normalized product use only `propext`, `Classical.choice`, and `Quot.sound`. The same holds in the main project for `IsHilbertFamily.unique`, `arch_difference_pair_integrable`, and `arch_linearFactor_integral`.

| Main theorem | Reachable project declarations with a direct admission |
| --- | --- |
| `Datum.poisson` | `existsUnique_hilbert`, `reverse_marginal_on_test`, `thetaDifference_vanishing` |
| `Datum.lineSummation` | The same three and `unfolding` |
| `Datum.twistedGaussSummation` | The same three and `unfolding` |

Before the rc2 integration there were 12 direct admissions in the library. The other eight are `kubota_projection`, `fourier_mass`, `fourier_root_kernel`, `arch_integrableOn_shear_vertical`, `mellin_dual`, `powerClass_poisson`, `constantTerm_identity`, and `boundary_degree_one`. The all-place statement of Lemma A.2 remains in `Marginals/TestInversion.lean`.

To reproduce the main audit from the project root, run `lake build` and `lake env lean experiments/class-field-theory/MainAudit.lean`. The file traces direct uses of `sorryAx` through project declarations and also runs `#print axioms` on the three public theorems.

To reproduce the external experiment, make sibling scratch directories named `native` and `forward`. Put the vendor package in `native` and check out MetaplecticSummation at `30f6008` in `forward`. Apply the corresponding compatibility patch to each. Use the vendor's rc2 toolchain and Mathlib commit above in both scratch projects, refresh the forward manifest, and build `MetaplecticSummation.Arithmetic`, `MetaplecticSummation.FinitePlaceNorm`, and `MetaplecticSummation.PowerSubgroup` in `forward`. Copy the experiment Lean files from this directory to `native`. From that directory run

```sh
lake build ClassFieldTheory.LocalClassFieldTheory.Kummer.MathlibHilbertPairing \
  ClassFieldTheory.LocalClassFieldTheory.Kummer.PowerResidueTameFormula \
  ClassFieldTheory.Theorems.HilbertSymbols.PowerClassEqOneIff \
  ClassFieldTheory.Theorems.HilbertSymbols.HilbertProductFormula \
  ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity
lake env lean Audit.lean
lake env lean TameConvention.lean
lake env sh -ec '
  export LEAN_PATH=".:../forward/.lake/build/lib/lean:$LEAN_PATH"
  for m in PairBridge GlobalBridge CompletionTame FiniteLaws InfiniteLaws HilbertExistence; do
    lean -o "$m.olean" "$m.lean"
  done'
```

## Proposition B.6

Put $G=\mathrm{SL}_2$, $\Gamma=G(F)$, and let $N$ be the upper unipotent subgroup. Fix the idele $z$ with $z_w=\varpi_w^{-1}$ at one finite place and $1$ elsewhere. Equation `eq:siegel` in the paper needs a compact $\Omega\subset G(\mathbb A)$, a finite measure $\nu$ on $\Omega$, and a constant $C$ with both of the following properties.

1. Every adelic matrix is $\gamma n(u)h(z^k)\omega$ with $\gamma\in\Gamma$, $u\in\mathbb A$, $k\ge0$, and $\omega\in\Omega$.
2. For every nonnegative measurable function $f$ on $\Gamma\backslash G(\mathbb A)$ the quotient Haar integral is bounded by
   $$
   C\sum_{k\ge0}|z|^{-2k}\int_{\mathbb A/F}\int_\Omega
      f(n(u)h(z^k)\omega)\,d\nu(\omega)\,du.
   $$
   The exponent comes from the action of $h(z^k)$ on upper unipotents. A covering alone gives no measure bound.

The second required quotient statement unfolds the orbit of $(0,1)$, whose rational stabilizer is $N(F)$. For $D=\Theta-\Theta\circ\mathcal F$, after proving absolute integrability of the majorant $\theta\,\delta$, the identity is

$$
\int_{\Gamma\backslash G(\mathbb A)}\Theta(g\Psi)\overline{D(g\Phi)}\,dm
=
\int_{N(\mathbb A)\backslash G(\mathbb A)}
 (g\Psi)(0,1)\int_{\mathbb A/F}\overline{D(n(u)g\Phi)}\,du\,dm .
$$

Here $g$ is any lift of $m$. The two quotient integrations must use compatible measures. The first unfolding is to $N(F)\backslash G(\mathbb A)$, followed by integration along $N(F)\backslash N(\mathbb A)$. The inner integral is the translated constant term.

Yamaguchi's `Idele/NormOneCompact.lean` gives `compactNormOneClassCover` and its image in the idele class group. AutomorphicLean's `LocalGL2.exists_iwasawa` factors a local $\mathrm{GL}_2$ matrix as upper triangular times integral. Tau Ceti's `CanonicalEmbedding/PoissonSummation.lean` proves `tsum_idealLattice_eq_tsum_mixedDual_mixedFourier` for an invertible fractional ideal. The multiplicative Poisson step needs a separate proof that the image $\Delta$ of rational power classes in $\mathbb A^\times/\mathbb A^{\times n}$ satisfies $\Delta^\perp=\Delta$. Reciprocity gives the inclusion $\Delta\subseteq\Delta^\perp$.
