# Metaplectic summation

Lean statements accompanying the number-field case of *A Schwartz space for the
n-fold cover of SL₂*. The Poisson formula is stated in
[`MetaplecticPoisson.Datum.poisson`](MetaplecticSummation/Poisson.lean),
Theorem 9.1. For the global Gauss-sum formulas, start with
[`twistedGaussSummation`, `quadraticDual`, and `sextic_to_quadratic`](MetaplecticSummation/Gauss.lean).
Open the project with Lean v4.32.2 and run `lake build`.

The inputs are a number field, a positive cover degree, a primitive root, an
embedding of its group of roots of unity in the complex units, and a nontrivial
continuous additive character of the adeles trivial on the diagonal field.
The test spaces, transform, leading term, basic vectors, restricted tensor
products and rational evaluations all depend on these inputs.

| File | Mathematical content |
| --- | --- |
| [Arithmetic](MetaplecticSummation/Arithmetic.lean) | Completions, local characters, normalized modulus, self-dual measures and the Hilbert symbol |
| [Core](MetaplecticSummation/Core.lean) | The two chart integrals in Definition 4.4, normalized ray limits and maps of restricted tensor products |
| [Schwartz](MetaplecticSummation/Schwartz.lean) | Local test functions, the span of test functions and their transforms, and the good-place basic vector |
| [SymbolOnLines](MetaplecticSummation/SymbolOnLines.lean) | Equality of the two integrands up to the chart multiplier on every line, from the Steinberg relation |
| [LocalSymbols](MetaplecticSummation/LocalSymbols.lean) | Continuity and unitarity of the complex symbol from the stated arithmetic characterization |
| [LineMeasures](MetaplecticSummation/LineMeasures.lean) | Affine change of variables and equality of the normalized Radon charts |
| [ArchimedeanLines](MetaplecticSummation/ArchimedeanLines.lean) | The infinite-place modulus and Steinberg relation |
| [FiniteHaar](MetaplecticSummation/FiniteHaar.lean) | The finite residue field, compact ring of integers and the equality of the Haar modulus and the adic norm |
| [PowerSubgroup](MetaplecticSummation/PowerSubgroup.lean) | Openness of the nonzero n-th powers when n is nonzero in the local field |
| [TameSymbols](MetaplecticSummation/TameSymbols.lean) | Principal units are n-th powers at tame places, giving the tame Steinberg relation |
| [WildSymbols](MetaplecticSummation/WildSymbols.lean) | Steinberg at the wild places by reciprocity, Lemma 4.2(ii) at every place, and gluing of every Schwartz section |
| [FiniteLines](MetaplecticSummation/FiniteLines.lean) | Absolute convergence, joint continuity and uniform vanishing for large line parameter on finite-place test functions in Lemma 4.2 |
| [Poisson](MetaplecticSummation/Poisson.lean) | The adelic spaces and maps, rational evaluation, Theorem 9.1, Corollary 9.2 and the degree-one boundary value |
| [Shears](MetaplecticSummation/Shears.lean) | Proved chart gluing, additive composition and the two Radon and Fourier identities of Lemma 5.2 |
| [Inversion](MetaplecticSummation/Inversion.lean) | The root kernel, the local cover acting on Schwartz functions, Fourier inversion, equivariance and Plancherel (Theorem 7.1) |
| [Jacquet](MetaplecticSummation/Jacquet.lean) | Jacquet integrals, the explicit dual weight (Proposition 10.8), and adelic summation with its power-class main term (Theorem 10.16) |
| [Gauss](MetaplecticSummation/Gauss.lean) | Power residue symbols, Gauss sums and their divisor sums over S-integers, the twisted formula (Theorem 10.34), and quadratic duals (Corollary 10.40) |
| [LocalWeights](MetaplecticSummation/LocalWeights.lean) | Mellin factors, transforms of basic and character weights, the Gauss-sum expression for ε, and the intertwining operator on leading terms |
| [FourierCoefficients](MetaplecticSummation/FourierCoefficients.lean) | Unfolding at frequencies zero and one, the two local marginal identities, Poisson on power classes and the constant-term identity |

## Conventions and proof status

At a finite place of norm q prime to n, the symbol of a uniformizer and a unit u
reduces to u^((q−1)/n). Bimultiplicativity, continuity and global reciprocity,
together with the tame normalization, characterize the symbol family. Weak
approximation isolates each exceptional place modulo n-th powers. The
existence and uniqueness theorem for this characterization is admitted.
This keeps the statement on Mathlib. A future class-field-theoretic proof can
compare Tau Ceti's Kummer-cup invariant to the tame normalization.
Tau Ceti proves the Steinberg relation for its local symbol in
`TauCeti.ClassFieldTheory.localSymbol_kummerClass_eq_zero_of_add_eq_one`.
This project's proof of Steinberg uses the arithmetic characterization directly.
Hensel lifting treats principal units at tame places. At the remaining finite
places weak approximation and reciprocity isolate the desired symbol.
`Datum.radon_glues` uses these results with the normalized Haar measures.
It proves chart compatibility for Lean's totalized integrals. Absolute
convergence is a separate assertion, currently proved on finite-place test functions.

The local Fourier and leading-term maps are chosen from stated existence
lemmas prescribing their values by the integrals and ray limits. At the
finitely many places without a basic vector, the restricted tensor construction
uses zero as an arbitrary reference value. Local factors at these places vary
freely. The boundary space is the restricted tensor product of the **local
images** of the leading-term maps.

The main theorem and the arithmetic and analytic inputs still have `sorry`
proofs. Corollary 9.2 is deduced from Theorem 9.1 in Lean. To list the current
proof obligations, run `rg -n '\bsorry\b' MetaplecticSummation`.


## Reading the Gauss-sum formulas

`lineSummation` chooses one family of coefficients for all test weights at a
fixed set of places. Its outer sums run over nonzero field elements.
`twistedGaussSummation` assumes the S-integers form a PID and sums over their
nonzero **elements**. Only the inner divisor sum in `normalizedGauss` runs over
associates. With empty twist set, `mainTerm` forms both the coefficients and the
multiplicative measures using the scaled character. With nonempty twist set,
the dual sum retains both residue symbols.

The scope is the principal formulas over number fields and their completions.
The local estimates, illustrative examples and intermediate proof lemmas do
not have individual Lean statements throughout.
