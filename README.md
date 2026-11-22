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
| [Schwartz/Basic](MetaplecticSummation/Schwartz/Basic.lean) | Local test functions, the span of test functions and their transforms, and the good-place basic vector |
| [Schwartz](MetaplecticSummation/Schwartz.lean) | The leading-term map and its values on both types of generator at finite places |
| [SymbolOnLines](MetaplecticSummation/SymbolOnLines.lean) | Equality of the two integrands up to the chart multiplier on every line, from the Steinberg relation |
| [LocalSymbols](MetaplecticSummation/LocalSymbols.lean) | Continuity and unitarity of the complex symbol from the stated arithmetic characterization |
| [LineMeasures](MetaplecticSummation/LineMeasures.lean) | Affine change of variables and equality of the normalized Radon charts |
| [ArchimedeanLines](MetaplecticSummation/ArchimedeanLines.lean) | The infinite-place modulus and Steinberg relation |
| [FiniteHaar](MetaplecticSummation/FiniteHaar.lean) | The finite residue field, compact ring of integers and the equality of the Haar modulus and the adic norm |
| [PowerSubgroup](MetaplecticSummation/PowerSubgroup.lean) | Openness of the nonzero n-th powers and finiteness of the power-class group over a proper complete local field when the exponent is nonzero in the field |
| [TameSymbols](MetaplecticSummation/TameSymbols.lean) | Principal units are n-th powers at tame places, giving the tame Steinberg relation |
| [WildSymbols](MetaplecticSummation/WildSymbols.lean) | Steinberg at the wild places by reciprocity, Lemma 4.2(ii) at every place, and gluing of every Schwartz section |
| [FiniteLines](MetaplecticSummation/FiniteLines.lean) | Absolute convergence, joint continuity and uniform vanishing for large line parameter on finite-place test functions in Lemma 4.2 |
| [SmoothFiniteLines](MetaplecticSummation/SmoothFiniteLines.lean) | Joint local constancy of both finite-place Radon charts and uniform Schwartz–Bruhat bounds for the line slices over compact sets of output vectors |
| [LocalCharacters](MetaplecticSummation/LocalCharacters.lean) | Continuity, additivity and unitarity of the restrictions of the adelic character |
| [FiniteTransform](MetaplecticSummation/FiniteTransform.lean) | Absolute convergence of the outer transform integral on finite-place test sections and local constancy of both charts of every finite-place Schwartz section |
| [FiniteSchwartzLines](MetaplecticSummation/FiniteSchwartzLines.lean) | Absolute convergence of both line integrals on the full Schwartz space at every finite place for nonzero line parameters |
| [TransformLinearity](MetaplecticSummation/TransformLinearity.lean) | Scalar linearity of the chart integrals and additivity at finite places under absolute convergence |
| [RayFourier](MetaplecticSummation/RayFourier.lean) | The normalized transform on each power ray as a one-dimensional Fourier integral, at every place |
| [FiniteLeading](MetaplecticSummation/FiniteLeading.lean) | Construction of the leading-term map on the full finite-place Schwartz space and its formula at frequency zero |
| [FiniteRayFourier](MetaplecticSummation/FiniteRayFourier.lean) | Local constancy and nontriviality of finite-place additive characters, and uniform Schwartz–Bruhat bounds after one-dimensional Fourier transformation |
| [FiniteRays](MetaplecticSummation/FiniteRays.lean) | Bounded families of normalized ray extensions for every finite-place Schwartz section in §8 |
| [FiniteGerms](MetaplecticSummation/FiniteGerms.lean) | Local constancy and homogeneity of the leading term, compact support in the plane, agreement with the leading term near zero, and identification of its kernel with the test sections |
| [AdelicCharacters](MetaplecticSummation/AdelicCharacters.lean) | Convergence of the sum of the single-place components of an adele and the product formula for its additive character |
| [RationalEvaluation](MetaplecticSummation/RationalEvaluation.lean) | The product formula for the normalized modulus, adelic chart evaluations on the restricted tensor product, and agreement at rational points by Hilbert reciprocity |
| [Poisson](MetaplecticSummation/Poisson.lean) | The adelic Fourier and leading-term maps, Theorem 9.1, Corollary 9.2 including its local vanishing criterion, and the degree-one boundary value |
| [Shears](MetaplecticSummation/Shears.lean) | Proved chart gluing, additive composition and the two Radon and Fourier identities of Lemma 5.2 |
| [RapidCharts](MetaplecticSummation/RapidCharts.lean) | Rapid derivative estimates under real-linear changes of variables and local changes of chart |
| [ArchimedeanShears](MetaplecticSummation/ArchimedeanShears.lean) | Preservation of the real and complex test spaces by both shear operators |
| [Cover](MetaplecticSummation/Cover.lean) | Construction of the unique upper and lower shear automorphisms of the full local Schwartz space, equivariance, and the statement of the Kubota projection |
| [FourierOrthogonality](MetaplecticSummation/FourierOrthogonality.lean) | Fourier transform of additive subgroup indicators and the volume of the annihilator of a compact open subgroup |
| [FiniteFourierInversion](MetaplecticSummation/FiniteFourierInversion.lean) | Ordinary Fourier inversion on finite completions with the chosen self-dual measure, and the affine pairing from Appendix A |
| [FiniteInversion](MetaplecticSummation/FiniteInversion.lean) | Composition of diagonal lifts, the metaplectic square formula from marginal and ordinary Fourier inversion, and bijectivity from the square |
| [Inversion](MetaplecticSummation/Inversion.lean) | Theorem 7.1 assembled from these results, archimedean ordinary inversion, and metaplectic Plancherel. The latter two inputs and the root-kernel integral formula are admitted |
| [Jacquet](MetaplecticSummation/Jacquet.lean) | Jacquet integrals, the explicit dual weight (Proposition 10.8), and adelic summation with its power-class main term (Theorem 10.16) |
| [SArithmetic](MetaplecticSummation/SArithmetic.lean) | Finiteness of residue rings, power residue symbols, independence of Gauss sums from residue representatives, and the divisor sum over S-integers |
| [Gauss/Setup](MetaplecticSummation/Gauss/Setup.lean) | Classical arithmetic hypotheses, twists, scaling the additive character, and its conductor |
| [Gauss](MetaplecticSummation/Gauss.lean) | Deduction of the untwisted S-integer identity from adelic line summation, the twisted formula (Theorem 10.34), and quadratic duals (Corollary 10.40) |
| [ConductorMeasure](MetaplecticSummation/ConductorMeasure.lean) | Existence of finite conductor parameters, self-dual volumes, and Fourier integrals over the local integers |
| [BasicShears](MetaplecticSummation/BasicShears.lean) | Gluing and integral shear invariance of the explicit basic vector, and determination of an invariant section by its vertical axis |
| [BasicShells](MetaplecticSummation/BasicShells.lean) | The basic-vector marginal on every nonzero vertical line (Lemma A.5) |
| [BasicFixed](MetaplecticSummation/BasicFixed.lean) | Fourier invariance of the raw unramified basic vector (Proposition 6.3(i)) |
| [TransformScaling](MetaplecticSummation/TransformScaling.lean) | The local integral transform under a change of the global additive character |
| [BasicConductor](MetaplecticSummation/BasicConductor.lean) | The explicit transform of the basic vector at a tame finite place with a prescribed local conductor (Corollary 6.5) |
| [BasicWeights](MetaplecticSummation/BasicWeights.lean) | The basic Jacquet weight at units and nonintegral arguments, vanishing outside S for nonintegral moduli, and the transformed basic Jacquet weight at general conductor |
| [LocalGauss](MetaplecticSummation/LocalGauss.lean) | Local residue rings, constancy of the Gauss phase on a unit residue class, and the integral over the primitive shell |
| [JacquetBasic](MetaplecticSummation/JacquetBasic.lean) | The Jacquet integral of the basic vector as a generating series of Gauss–Ramanujan sums for every nonzero local modulus |
| [GaussRamanujan](MetaplecticSummation/GaussRamanujan.lean) | Covariance of the local Gauss sum and basic Jacquet function under multiplication by a unit |
| [ResidueCRT](MetaplecticSummation/ResidueCRT.lean) | Chinese remainder isomorphism for the S-integer residue ring, including the unit modulus, and decomposition of the additive phase |
| [GaussFactorization](MetaplecticSummation/GaussFactorization.lean) | The global Gauss sum as the product of the local Gauss sums for the scaled character |
| [BasicProduct](MetaplecticSummation/BasicProduct.lean) | The product of basic Jacquet functions as a finite product of local series, and its evaluation for locally n-th-power-free moduli |
| [PowerDivisors](MetaplecticSummation/PowerDivisors.lean) | Classification of global power divisors up to S-units by their tuples of local exponents under the PID hypothesis |
| [GaussProduct](MetaplecticSummation/GaussProduct.lean) | The product of the basic functions outside S as a normalized global Gauss sum for arbitrary integral moduli |
| [CharacterScaling](MetaplecticSummation/CharacterScaling.lean) | Self-dual measure under scaling of the character, and the dilation and change-of-character formulas for the dual weight |
| [TwistedWeights](MetaplecticSummation/TwistedWeights.lean) | Character test weights, unit covariance of their transforms, vanishing of power-class moments, and the norm and Gauss-sum expression for ε |
| [TwistedSummation](MetaplecticSummation/TwistedSummation.lean) | Adelic line summation at S ∪ T, vanishing of the main term for nonempty T, and the product of transformed weights at the conductor primes |
| [LocalWeights](MetaplecticSummation/LocalWeights.lean) | Jacquet inversion from Schwartz inversion, Mellin factors, and the intertwining operator on leading terms |
| [AdeleLattice](MetaplecticSummation/AdeleLattice.lean) | Discreteness of the diagonal field, an additive fundamental domain in the adeles, and compactness of the Hausdorff quotient |
| [Marginals](MetaplecticSummation/Marginals.lean) | The marginal-to-axis Fourier identity, the two zero-parameter formulas, and Schwartz–Bruhat regularity of the finite-place axis density |
| [MarginalDifference](MetaplecticSummation/MarginalDifference.lean) | The cocycle for the multiplicative difference integral in Appendix A, finite-place integrability, and cancellation for a nontrivial Hilbert character |
| [MarginalRoots](MetaplecticSummation/MarginalRoots.lean) | Decomposition of the difference integral over the distinct roots of an n-th power, including the integrated identity |
| [MultiplicativeMeasure](MetaplecticSummation/MultiplicativeMeasure.lean) | Multiplicative Haar measure on the units, invariance under inversion, and the substitution t = a/u at every completion |
| [LinearFactor](MetaplecticSummation/LinearFactor.lean) | Absolute convergence and evaluation of the tested linear factor in Appendix A and the resulting sum over distinct roots at every finite place |
| [TestedMarginal](MetaplecticSummation/TestedMarginal.lean) | The scaled marginal, the change to the Y chart, and the finite-place pairing against a test frequency with its first exchange of integrals |
| [MarginalConvergence](MetaplecticSummation/MarginalConvergence.lean) | Joint absolute convergence of the subtracted integral and the tested reverse marginal identity for finite-place test sections |
| [TamePowers](MetaplecticSummation/TamePowers.lean) | Identification of the radical of the normalized tame Hilbert pairing with the subgroup of n-th powers |
| [MarginalRootFormula](MetaplecticSummation/MarginalRootFormula.lean) | The pointwise sum over roots in Appendix A for finite-place test sections, conditional on Hilbert nondegeneracy at wild places |
| [PowerJacobian](MetaplecticSummation/PowerJacobian.lean) | Bijection of sufficiently small balls under the power map, with radius scaled by the norm of its derivative |
| [PowerArea](MetaplecticSummation/PowerArea.lean) | Integrated change of variables for the power map on locally constant compactly supported functions vanishing at zero, at every finite place |
| [FiniteMarginal](MetaplecticSummation/FiniteMarginal.lean) | Reverse marginal Fourier identity and the square of the defining integral transform on tame test sections |
| [DiagonalTransform](MetaplecticSummation/DiagonalTransform.lean) | Covariance of both defining chart integrals under the diagonal lifts at every place |
| [SchwartzStability](MetaplecticSummation/SchwartzStability.lean) | Absolute convergence of the outer integral, the Fourier automorphism of the full tame Schwartz space, and its square |
| [BasicMarginals](MetaplecticSummation/BasicMarginals.lean) | The basic axis density at almost all places, its ordinary Fourier transform for an unramified character, and the basic marginal at a unit |
| [FourierCoefficients](MetaplecticSummation/FourierCoefficients.lean) | Rational products of the marginal kernels, unfolding at frequencies zero and one, Poisson on power classes and the constant-term identity |

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
At every finite place the inner line integrals converge absolutely on all
test sections and, for nonzero line parameter, on the full Schwartz space.
At tame places the outer integrals converge absolutely for every Schwartz
section at every output vector.

The uniform all-place construction of the Fourier endomorphism and the
archimedean leading-term map are admitted. At tame finite places
`tame_schwartz_inversion` constructs the Fourier automorphism independently. At a finite place the normalized ray identity
and absolute convergence give the leading term on transforms of test sections.
Test sections themselves vanish near the origin. Linearity and uniqueness of
limits extend these values to the entire finite-place Schwartz space. This
construction uses the arithmetic inputs above, including self-dual Haar measure.
The normalized rays extend to bounded Schwartz–Bruhat families over compact
sets of chart vectors. A compact annulus meets every power ray, so uniform
bounds there give compact support in the plane and equality with the leading
term near the origin.

At the finitely many places without a basic vector, the restricted tensor construction
uses zero as an arbitrary reference value. Local factors at these places vary
freely. The boundary space is the restricted tensor product of the **local
images** of the leading-term maps.

For a pure tensor, rational evaluation is the product of its local chart values.
The basic vector evaluates to one at almost every place, and Hilbert reciprocity
makes the two chart products agree when both coordinates are nonzero.
The Fourier coefficient uses the unique Haar probability measure on the compact
additive quotient. Translation by a principal adele permutes the rational points
in the theta series, so its character-weighted integrand descends to the quotient.
The marginal-to-axis identity is proved at all places from chart gluing and
the one-dimensional power-ray formula. At a finite place the axis density is
Schwartz–Bruhat for every Schwartz section. For a pure tensor at almost every
finite place it is the indicator of the local integers on the whole field.
The reverse marginal identity remains admitted. In its proof Lean establishes
absolute convergence of the multiplicative difference integral for finite-place
tests and its vanishing when the Hilbert character is nontrivial. For an n-th
power parameter the cocycle splits the integral into contributions from its
distinct roots. At every finite place the linear-factor integral is absolutely
convergent and evaluates to the axis value times the multiplicative Fourier
integral of the test. The reciprocal change of variables uses the measure
obtained by weighting additive self-dual measure by the inverse modulus.
At every finite place, for test sections, subtracting the axis value gives
joint absolute convergence and justifies the exchange of the three integrals.
At tame places the normalized Hilbert pairing detects every non-power.
Localizing the frequency test therefore gives the pointwise sum over the
roots of −sy in Appendix A. The same argument works at wild places once
the radical of the Hilbert pairing is identified with the n-th powers there.
On a sufficiently small ball around a nonzero root a, the power map is
bijective onto a ball with radius scaled by |n a^(n−1)|. Partitioning the
compact support into disjoint such balls gives the integrated change of
variables at all finite places. At tame places this proves the reverse
marginal Fourier identity on test sections. Ordinary Fourier inversion gives
the square of the defining integral transform on the vertical axis. The upper
and lower shears preserve finite-place test sections, so the equality extends
to both charts. Diagonal covariance gives the square on transforms of test sections as
well. Absolute convergence gives linearity on their span, and the square
formula gives bijectivity. This proves Theorem 7.1(i) on the entire tame
Schwartz space using two admitted project results, the normalized Hilbert
symbol family and the self-dual measure. The argument applies at a wild
place under the same radical condition.

Both shear operators preserve the local Schwartz space at every place. In
the real and complex cases local changes of chart reduce the estimates for
all derivatives to those for a real-linear coordinate change. The inverse
shear uses the negative parameter. At tame places the constructed integral
automorphism commutes with the group generated by these shears and the
central scalars (`tame_transform_equivariant`). Identifying the projection of the
resulting operator group to SL₂ and proving the Plancherel identity in
Theorem 7.1 remain open.

The global product calculations cancel the normalizing constants at rational arguments
and identify the leading-term contributions at zero. The unfolding identities
at frequencies zero and one and the global constant-term identity remain admitted.

The main theorem and the arithmetic and analytic inputs still have `sorry`
proofs. Corollary 9.2 is deduced from Theorem 9.1 in Lean. To list the current
proof obligations, run `rg -n '\bsorry\b' MetaplecticSummation`.


## Reading the Gauss-sum formulas

`lineSummation` chooses one family of coefficients for all test weights at a
fixed set of places. Its outer sums run over nonzero field elements.
`twistedGaussSummation` assumes the S-integers form a PID and sums over their
nonzero **elements**. Only the inner divisor sum in `normalizedGauss` runs over
associates. Multiplying the modulus by the n-th power of an S-unit preserves
the Gauss sum. The divisor summand therefore has the same value on every
representative of an associate class. At a finite place where the original
character is unramified, Plancherel on the indicator of the integers gives
volume |b|ᵥ^(1/2) for the measure self-dual with respect to the scaled
character. Consequently the product of basic Jacquet factors outside S
vanishes on nonintegral arguments and equals |b|ₛ^(−1/2) on S-units. The
local generating series is proved for every nonzero modulus, as is the
Chinese remainder factorization of the ordinary global Gauss sum. For an
integral modulus, the product outside S reduces to the local series at the
primes dividing the modulus. When the S-integers form a PID, the exponent tuples in these
series enumerate the global power divisors up to S-units. Matching the norm
weights and the local Gauss factors gives `product_basic` for every nonzero
field element, including integral moduli divisible by repeated n-th powers.

The residue-ring isomorphism uses only standard Lean axioms. The proof of the
ordinary Gauss-sum factorization depends on the admitted characterization of
the Hilbert symbols. The basic Jacquet formulas additionally use the admitted
self-dual measure theorem and membership of the basic vector in the Schwartz space.

At a tame finite place, the explicit charts for the basic vector satisfy gluing
and invariance under integral shears. With unramified character the integral
over a vertical line is one when the valuation of its nonzero first coordinate
is a nonnegative multiple of n, and zero otherwise. The Fourier integral on the axis then gives
the original basic vector. Changing the character gives Corollary 6.5 for a
local conductor parameter b. These calculations use the explicit charts
before passing to the Schwartz space. Proposition 6.3(ii), membership of the
basic vector in that space, remains admitted.

The untwisted S-integer summation formula follows in Lean from the adelic
line formula, the identity for the transformed basic Jacquet weight, and
`product_basic`. Lean now derives the basic-weight identity from Corollary 6.5
by changing the line variable. The adelic line formula remains admitted.
Both S-integer series converge absolutely by the summability in the adelic
line formula. The nonintegral terms vanish, and the same power-class coefficients
from the adelic formula occur in the S-integer formula.

With empty twist set, `mainTerm` forms both the coefficients and the
multiplicative measures using the scaled character. With nonempty twist set,
Lean proves that each power-class moment vanishes by translating by an n-th
power of a local unit on which the twisting character is nontrivial. This
gives the absolutely convergent adelic identity from the admitted line formula.
The epsilon norm and its Gauss-sum expression follow from the admitted local
twisted-vector evaluation. After reindexing, the product at the conductor
primes gives ε, the conjugate twisting character and the residue symbol
with denominator f. Theorem 10.34 still requires matching the remaining local
factors and the two adelic sums with the stated S-integer expressions.

The scope is the principal formulas over number fields and their completions.
The local estimates, illustrative examples and intermediate proof lemmas do
not have individual Lean statements throughout.
