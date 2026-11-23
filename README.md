# Metaplectic summation

Lean statements accompanying the number-field case of *A Schwartz space for the
n-fold cover of SL₂*. The Poisson formula is stated in
[`MetaplecticPoisson.Datum.poisson`](MetaplecticSummation/Poisson.lean),
Theorem 9.1. For the global Gauss-sum formulas, start with
[`twistedGaussSummation`, `quadraticDual`, and `sextic_to_quadratic`](MetaplecticSummation/Gauss.lean).
Open the project with Lean v4.35.0-rc2 and run `lake build`.
The [Hilbert-symbol bridge and Appendix A notes](experiments/class-field-theory/README.md)
record the pin tests, the local proofs, and the quotient estimates needed in Proposition B.6.

The inputs are a number field, a positive cover degree, a primitive root, an
embedding of its group of roots of unity in the complex units, and a nontrivial
continuous additive character of the adeles trivial on the diagonal field.
The test spaces, transform, leading term, basic vectors, restricted tensor
products and rational evaluations all depend on these inputs.

| File | Mathematical content |
| --- | --- |
| [Places](MetaplecticSummation/Places.lean), [Arithmetic](MetaplecticSummation/Arithmetic.lean) | Completions, local characters, normalized modulus, self-dual measures and the Hilbert symbol |
| [ArchimedeanPlancherel](MetaplecticSummation/ArchimedeanPlancherel.lean), [ArchimedeanSelfDual](MetaplecticSummation/ArchimedeanSelfDual.lean) | Construction of the self-dual Haar measure for the specified additive character at each real or complex place |
| [Core](MetaplecticSummation/Core.lean) | The two chart integrals in Definition 4.4, normalized ray limits and maps of restricted tensor products |
| [Schwartz/Charts](MetaplecticSummation/Schwartz/Charts.lean) and [Schwartz/Local](MetaplecticSummation/Schwartz/Local.lean) | Local test functions, the Schwartz space they span with their transforms, the basic charts, and the Fourier endomorphism |
| [Schwartz/Basic](MetaplecticSummation/Schwartz/Basic.lean) | Choice of the reference vector for the restricted tensor product and its Fourier invariance at almost every place |
| [Schwartz](MetaplecticSummation/Schwartz.lean) | The leading-term map and its values on both types of generator at every place |
| [SymbolOnLines](MetaplecticSummation/SymbolOnLines.lean) | Equality of the two integrands up to the chart multiplier on every line, from the Steinberg relation |
| [LocalSymbols](MetaplecticSummation/LocalSymbols.lean) | Continuity and unitarity of the complex symbol from the stated arithmetic characterization |
| [LineMeasures](MetaplecticSummation/LineMeasures.lean) | Affine change of variables and equality of the normalized Radon charts |
| [ArchimedeanLines](MetaplecticSummation/ArchimedeanLines.lean) | The infinite-place modulus and Steinberg relation |
| [ArchimedeanRadon](MetaplecticSummation/ArchimedeanRadon.lean) | Absolute convergence on test sections in both charts, joint continuity of the Radon integrals, and rapid decay in the line parameter uniformly on compact sets of output vectors |
| [ArchimedeanLeading](MetaplecticSummation/ArchimedeanLeading.lean) | Vanishing of the leading term on archimedean test functions, its Fourier integral at zero on transformed test functions, and construction on their span |
| [LeadingAction](MetaplecticSummation/LeadingAction.lean) | Gluing and power-dilation homogeneity, continuity of the archimedean leading charts, and the induced action of the local cover on the leading-term space |
| [FiniteHaar](MetaplecticSummation/FiniteHaar.lean) | The finite residue field, compact ring of integers and the equality of the Haar modulus and the adic norm |
| [PowerSubgroup](MetaplecticSummation/PowerSubgroup.lean) | Openness of the nonzero n-th powers and finiteness of the power-class group over a proper complete local field when the exponent is nonzero in the field |
| [TameSymbols](MetaplecticSummation/TameSymbols.lean) | Principal units are n-th powers at tame places, giving the tame Steinberg relation |
| [WildSymbols](MetaplecticSummation/WildSymbols.lean) | Steinberg at the wild places by reciprocity, Lemma 4.2(ii) at every place, and gluing of every Schwartz section |
| [FiniteLines](MetaplecticSummation/FiniteLines.lean) | Absolute convergence, joint continuity and uniform vanishing for large line parameter on finite-place test functions in Lemma 4.2 |
| [SmoothFiniteLines](MetaplecticSummation/SmoothFiniteLines.lean) | Joint local constancy of both finite-place Radon charts and uniform Schwartz–Bruhat bounds for the line slices over compact sets of output vectors |
| [LocalCharacters](MetaplecticSummation/LocalCharacters.lean) | Continuity, additivity and unitarity of the restrictions of the adelic character |
| [CharacterNontrivial](MetaplecticSummation/CharacterNontrivial.lean) | Nontriviality of a character satisfying the local Plancherel identity |
| [ArchimedeanSlice](MetaplecticSummation/ArchimedeanSlice.lean), [SchwartzSliceIntegral](MetaplecticSummation/SchwartzSliceIntegral.lean), [SchwartzSliceFamily](MetaplecticSummation/SchwartzSliceFamily.lean) | Differentiation of affine line integrals and compact-uniform Schwartz bounds under the determinant substitution τ ↦ τⁿ |
| [FourierDifferences](MetaplecticSummation/FourierDifferences.lean), [ArchimedeanFourierDecay](MetaplecticSummation/ArchimedeanFourierDecay.lean) | Fourier multipliers for translations and differences, integral decay estimates from real derivatives, and uniform Fourier decay for bounded Schwartz families |
| [FiniteTransform](MetaplecticSummation/FiniteTransform.lean) | Absolute convergence of the outer transform integral on finite-place test sections and local constancy of both charts of every finite-place Schwartz section |
| [FiniteSchwartzLines](MetaplecticSummation/FiniteSchwartzLines.lean) | Absolute convergence of both line integrals on the full Schwartz space at every finite place for nonzero line parameters |
| [RadonConvergence](MetaplecticSummation/RadonConvergence.lean), [RadonDecay](MetaplecticSummation/RadonDecay.lean) | Lemma 4.2(i) at every number-field place under the chart growth hypothesis, absolute convergence and chart-valued linearity of the Fourier integral on the local Schwartz space |
| [TransformLinearity](MetaplecticSummation/TransformLinearity.lean) | Scalar linearity and additivity of the chart integrals under absolute convergence |
| [RayFourier](MetaplecticSummation/RayFourier.lean) | The normalized transform on each power ray as a one-dimensional Fourier integral, at every place |
| [FiniteLeading](MetaplecticSummation/FiniteLeading.lean) | Construction of the leading-term map on the full finite-place Schwartz space and its formula at frequency zero |
| [FiniteRayFourier](MetaplecticSummation/FiniteRayFourier.lean) | Local constancy and nontriviality of finite-place additive characters, and uniform Schwartz–Bruhat bounds after one-dimensional Fourier transformation |
| [FiniteRays](MetaplecticSummation/FiniteRays.lean) | Bounded families of normalized ray extensions for every finite-place Schwartz section in §8 |
| [FiniteGerms](MetaplecticSummation/FiniteGerms.lean) | Local constancy and homogeneity of the leading term, compact support in the plane, agreement with the leading term near zero, and identification of its kernel with the test sections |
| [AdelicAnnihilator](MetaplecticSummation/AdelicAnnihilator.lean), [AdelicConductor](MetaplecticSummation/AdelicConductor.lean) | Compact annihilator of a compact set of representatives for the adelic quotient and the unramified conductor at almost every finite place |
| [AdelicCharacters](MetaplecticSummation/AdelicCharacters.lean) | Convergence of the sum of the single-place components of an adele and the product formula for its additive character |
| [RationalEvaluation](MetaplecticSummation/RationalEvaluation.lean) | The product formula for the normalized modulus, adelic chart evaluations on the restricted tensor product, and agreement at rational points by Hilbert reciprocity |
| [BoundaryDilation](MetaplecticSummation/BoundaryDilation.lean) | The local modification in Appendix B, preserving the leading term and killing the transformed leading term (B.8) |
| [AdelicFourier](MetaplecticSummation/AdelicFourier.lean) | The adelic Fourier and leading-term maps on restricted tensor products |
| [ThetaBoxes](MetaplecticSummation/ThetaBoxes.lean), [ThetaEstimate](MetaplecticSummation/ThetaEstimate.lean), [ThetaMajorant](MetaplecticSummation/ThetaMajorant.lean) | The rational-point count, dyadic summation, and uniform idele estimate of Lemma B.1 |
| [LocalGrowth](MetaplecticSummation/LocalGrowth.lean) | Local bounds for the theta series, including the finite-place estimate and the archimedean reduction to transforms of test functions |
| [ThetaSquare](MetaplecticSummation/ThetaSquare.lean), [Theta](MetaplecticSummation/Theta.lean) | Absolute convergence of the theta series from local growth and invariance of its sum under the square of the adelic transform |
| [TensorDescent](MetaplecticSummation/TensorDescent.lean), [BoundaryConstruction](MetaplecticSummation/BoundaryConstruction.lean) | Descent of a functional through a restricted tensor product of surjections, Lemma B.10, and construction of the boundary functional from Proposition B.6 |
| [Poisson](MetaplecticSummation/Poisson.lean) | Theorem 9.1, Corollary 9.2 including its local vanishing criterion, and the degree-one boundary value |
| [Shears](MetaplecticSummation/Shears.lean) | Proved chart gluing, additive composition and the two Radon and Fourier identities of Lemma 5.2 |
| [RapidCharts](MetaplecticSummation/RapidCharts.lean) | Rapid derivative estimates under real-linear changes of variables and local changes of chart |
| [ArchimedeanShears](MetaplecticSummation/ArchimedeanShears.lean) | Preservation of the real and complex test spaces by both shear operators |
| [Cover](MetaplecticSummation/Cover.lean) | Construction of the unique upper and lower shear automorphisms of the full local Schwartz space, equivariance, and the statement of the Kubota projection |
| [FourierOrthogonality](MetaplecticSummation/FourierOrthogonality.lean) | Fourier transform of additive subgroup indicators and the volume of the annihilator of a compact open subgroup |
| [FinitePlancherel](MetaplecticSummation/FinitePlancherel.lean), [DualBallVolumes](MetaplecticSummation/DualBallVolumes.lean) | Haar normalization by dual balls, Fourier inversion with frequency cutoffs and Plancherel on every continuous compactly supported test at finite places |
| [FiniteFourierInversion](MetaplecticSummation/FiniteFourierInversion.lean) | Ordinary Fourier inversion on finite completions with the chosen self-dual measure, and the affine pairing from Appendix A |
| [TorusCharts](MetaplecticSummation/TorusCharts.lean) and [FiniteInversion](MetaplecticSummation/FiniteInversion.lean) | Diagonal lifts, the square of the raw transform on test sections, and its extension to the full local Schwartz space |
| [ArchimedeanDiagonal](MetaplecticSummation/ArchimedeanDiagonal.lean) and [Schwartz/FourierStability](MetaplecticSummation/Schwartz/FourierStability.lean) | Preservation of tests by the archimedean diagonal lifts and construction of the local Fourier endomorphism from inversion on tests |
| [LocalParseval](MetaplecticSummation/LocalParseval.lean), [ArchimedeanInversion](MetaplecticSummation/ArchimedeanInversion.lean) | Polarization of the self-dual normalization and pointwise ordinary Fourier inversion for the chosen character at every infinite place |
| [Inversion](MetaplecticSummation/Inversion.lean) | Theorem 7.1 assembled from the local marginal identities, ordinary inversion, and metaplectic Plancherel. Metaplectic Plancherel and the root-kernel integral formula are admitted |
| [FiniteBoundaryImage](MetaplecticSummation/FiniteBoundaryImage.lean) | The quotient by test sections, its identification with the image of the intertwining operator, and the support and germ characterization of Schwartz sections (Corollary 8.4) |
| [LineMoments](MetaplecticSummation/LineMoments.lean) | Normalized test weights on local power classes, surjectivity of the weighted moment map, and products of tests isolating individual coefficient tuples |
| [PowerHaar](MetaplecticSummation/PowerHaar.lean), [Jacquet/LeadingKernel](MetaplecticSummation/Jacquet/LeadingKernel.lean) | The power-map Haar normalization (2.1) at every place and absolute convergence for interchanging the power average with a line integral |
| [Jacquet/PowerAverage](MetaplecticSummation/Jacquet/PowerAverage.lean) | Power averages of Jacquet lifts, including vanishing for a zero moment vector, and the proof of the local leading-term formula (Lemma 8.3) |
| [Jacquet/LineWeights](MetaplecticSummation/Jacquet/LineWeights.lean), [Jacquet](MetaplecticSummation/Jacquet.lean) | The explicit dual weight (Proposition 10.8), lifting and unfolding of both adelic sums, and the deduction of the line formula with its unique power-class coefficients (Theorem 10.16) |
| [Jacquet/Kernel](MetaplecticSummation/Jacquet/Kernel.lean), [ArchimedeanFourierSchwartz](MetaplecticSummation/ArchimedeanFourierSchwartz.lean) | Schwartz–Bruhat regularity of the kernel in Proposition 10.8 and absolute convergence of its Fourier integral at every frequency |
| [Jacquet/Weak](MetaplecticSummation/Jacquet/Weak.lean), [Jacquet/ArchWeak](MetaplecticSummation/Jacquet/ArchWeak.lean), [Jacquet/ShearRegion](MetaplecticSummation/Jacquet/ShearRegion.lean) | Weak and pointwise Jacquet identities, their finite-place proofs, and reduction at infinite places to the vertical part of the shear estimate |
| [Jacquet/FiniteShear](MetaplecticSummation/Jacquet/FiniteShear.lean), [Jacquet/WeightIntegrability](MetaplecticSummation/Jacquet/WeightIntegrability.lean) | The finite-place shear estimate, decay and absolute integrability of Jacquet weights, and the Radon identity on a shear representative |
| [Jacquet/Convergence](MetaplecticSummation/Jacquet/Convergence.lean), [Jacquet/Lines](MetaplecticSummation/Jacquet/Lines.lean) | Absolute convergence, continuity, unipotent equivariance, and the fixed-parameter Radon identity for integrable X-charts |
| [SArithmetic](MetaplecticSummation/SArithmetic.lean) | Finiteness of residue rings, power residue symbols, independence of Gauss sums from residue representatives, and the divisor sum over S-integers |
| [Gauss/Setup](MetaplecticSummation/Gauss/Setup.lean) | Classical arithmetic hypotheses, twists, scaling the additive character, and its conductor |
| [Gauss](MetaplecticSummation/Gauss.lean) | Deduction of the untwisted S-integer identity from adelic line summation, the twisted formula (Theorem 10.34), and quadratic duals (Corollary 10.40) |
| [ConductorMeasure](MetaplecticSummation/ConductorMeasure.lean) | Existence of finite conductor parameters, self-dual volumes, and Fourier integrals over the local integers |
| [BasicShears](MetaplecticSummation/BasicShears.lean) | Gluing and integral shear invariance of the explicit basic vector, and determination of an invariant section by its vertical axis |
| [PrimitiveLayer](MetaplecticSummation/PrimitiveLayer.lean) | Local constancy of the explicit basic charts, the primitive test section, and the shell recurrence (6.1) |
| [Dilations](MetaplecticSummation/Dilations.lean) | Dilation of both Radon and Fourier integrals at every place and stability of the finite Schwartz space under power dilations |
| [BasicShells](MetaplecticSummation/BasicShells.lean) | The basic-vector marginal on every nonzero vertical line (Lemma A.5) |
| [BasicFixed](MetaplecticSummation/BasicFixed.lean) | Fourier invariance of the raw unramified basic vector (Proposition 6.3(i)) |
| [TransformScaling](MetaplecticSummation/TransformScaling.lean) | The local integral transform under a change of the global additive character |
| [BasicConductor](MetaplecticSummation/BasicConductor.lean) | The explicit transform of the basic vector at a tame finite place with a prescribed local conductor (Corollary 6.5) |
| [LocalCharacterScaling](MetaplecticSummation/LocalCharacterScaling.lean) | Change of local conductor and self-dual measure under a global scalar |
| [BasicMembership](MetaplecticSummation/BasicMembership.lean) | Membership of the explicit basic vector in the Schwartz space at every tame finite place (Proposition 6.3(ii)) |
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
| [UnitGauss](MetaplecticSummation/UnitGauss.lean) | Support and absolute value of a ramified character Gauss integral, and the unit-character reduction of the Jacquet kernel |
| [UnramifiedGauss](MetaplecticSummation/UnramifiedGauss.lean) | Ramanujan integrals and both valuation cases of the Hilbert-character transform in Proposition 10.27 |
| [UnitTransformBounds](MetaplecticSummation/UnitTransformBounds.lean) | Hilbert-symbol realization of n-torsion unit characters, evaluation of the ball and sphere integrals, and the support and norm bounds for all continuous unit characters |
| [RamifiedGauss](MetaplecticSummation/RamifiedGauss.lean) | Conductor of the Hilbert-symbol twist and the two Gauss factors in the ramified local transform |
| [TwistedWeights](MetaplecticSummation/TwistedWeights.lean) | Character test weights, unit covariance of their transforms, vanishing of power-class moments, and the norm and Gauss-sum expression for ε |
| [TwistedSummation](MetaplecticSummation/TwistedSummation.lean) | Adelic line summation at S ∪ T, vanishing of the main term for nonempty T, and the product of transformed weights at the conductor primes |
| [LocalWeights](MetaplecticSummation/LocalWeights.lean) | Jacquet inversion from Schwartz inversion, Mellin factors, and the intertwining operator on leading terms |
| [AdeleLattice](MetaplecticSummation/AdeleLattice.lean) | Discreteness of the diagonal field, an additive fundamental domain in the adeles, and compactness of the Hausdorff quotient |
| [Marginals](MetaplecticSummation/Marginals.lean) | Both local Fourier identities and the two Schwartz–Bruhat regularity assertions of Lemma A.6 |
| [MarginalDifference](MetaplecticSummation/MarginalDifference.lean) | The cocycle for the multiplicative difference integral in Appendix A, finite-place integrability, and cancellation for a nontrivial Hilbert character |
| [MarginalRoots](MetaplecticSummation/MarginalRoots.lean) | Decomposition of the difference integral over the distinct roots of an n-th power, including the integrated identity |
| [MultiplicativeMeasure](MetaplecticSummation/MultiplicativeMeasure.lean) | Multiplicative Haar measure on the units, invariance under inversion, and the substitution t = a/u at every completion |
| [LinearFactor](MetaplecticSummation/LinearFactor.lean) | Absolute convergence and evaluation of the tested linear factor in Appendix A and the resulting sum over distinct roots at every finite place |
| [Marginals/ArchimedeanTest](MetaplecticSummation/Marginals/ArchimedeanTest.lean), [Density](MetaplecticSummation/Marginals/Density.lean), and [Regularity](MetaplecticSummation/Marginals/Regularity.lean) | Flat extension through the origin and Schwartz–Bruhat regularity of both marginal kernels at every place |
| [TestedMarginal](MetaplecticSummation/TestedMarginal.lean) | The scaled marginal, the change to the Y chart, and the finite-place pairing against a test frequency with its first exchange of integrals |
| [MarginalConvergence](MetaplecticSummation/MarginalConvergence.lean) | Joint absolute convergence of the subtracted integral and the tested reverse marginal identity for finite-place test sections |
| [TamePowers](MetaplecticSummation/TamePowers.lean) | Identification of the radical of the normalized tame Hilbert pairing with the subgroup of n-th powers |
| [MarginalRootFormula](MetaplecticSummation/MarginalRootFormula.lean) | The pointwise sum over roots in Appendix A for finite-place test sections, with the power criterion at all finite places |
| [PowerJacobian](MetaplecticSummation/PowerJacobian.lean) | Bijection of sufficiently small balls under the power map, with radius scaled by the norm of its derivative |
| [PowerArea](MetaplecticSummation/PowerArea.lean) | Integrated change of variables for the power map on locally constant compactly supported functions vanishing at zero, at every finite place |
| [FiniteMarginal](MetaplecticSummation/FiniteMarginal.lean) | Reverse marginal Fourier identity on test sections at every finite place |
| [TransformedMarginals](MetaplecticSummation/TransformedMarginals.lean) | Extension of the reverse identity from test sections to the full span, and the independent proof at tame places |
| [DiagonalTransform](MetaplecticSummation/DiagonalTransform.lean) | Covariance of both defining chart integrals under the diagonal lifts at every place |
| [SchwartzStability](MetaplecticSummation/SchwartzStability.lean) | Absolute convergence of the outer integral, the Fourier automorphism of the full tame Schwartz space, and its square |
| [BasicMarginals](MetaplecticSummation/BasicMarginals.lean) | The basic axis density at almost all places, its ordinary Fourier transform for an unramified character, and the basic marginal at a unit |
| [FourierCoefficients](MetaplecticSummation/FourierCoefficients.lean) | Rational products of the marginal kernels, unfolding at frequencies zero and one, Poisson on power classes and the constant-term identity |

## Conventions and proof status

At every place the self-dual Haar measure is unique if it exists. Multiplying
Haar measure by a positive scalar multiplies the squared norm of the transform
by its cube and the squared norm of the input by the scalar itself. A nonzero
compactly supported test forces the scalar to equal one. At real and complex
places the character pairing is the standard Fourier character composed
with an invertible real linear change of frequency. The ordinary integral
agrees almost everywhere with the L² Fourier transform for functions in
L¹ ∩ L². Rescaling Euclidean volume by the inverse square root of its
pushforward Haar factor gives Plancherel for the chosen character. Transport
to the completion proves `exists_arch_selfDual`. At finite places, scale Haar measure so that each
ball and its character annihilator have reciprocal volumes. Integrating
the ordinary Fourier transform of a continuous compactly supported function
over increasing balls then converges to its value at zero. Apply this
to the convolution of a test with its reflected conjugate. Its transform is
the squared modulus of the original transform, so monotone convergence
gives Plancherel. This proves `exists_finite_selfDual` for the given character.
The existence and uniqueness of the self-dual measures at all number-field
places now use only standard Lean axioms.

At infinite places `arch_hat_hat_of_integrable` proves pointwise ordinary
Fourier inversion for a continuous integrable function with integrable transform.
Polarization gives Parseval on compactly supported tests. Fubini moves the
transform between the two factors, and smooth compactly supported tests
separate continuous functions in real and complex coordinates.

At a finite place of norm q prime to n, the symbol of a uniformizer and a unit u
reduces to u^((q−1)/n). Bimultiplicativity, continuity and global reciprocity,
together with the tame normalization, characterize the symbol family. Weak
approximation isolates each exceptional place modulo n-th powers. The
existence proof transports Yamaguchi’s coherent Hilbert pairing from
ClassFieldTheory and takes its inverse to match the uniformizer convention.
The primitive global root identifies the global and local groups of roots of
unity. The explicit infinite factors complete the product formula.
This project's proof of Steinberg uses the arithmetic characterization directly.
Hensel lifting treats principal units at tame places. At the remaining finite
places weak approximation and reciprocity isolate the desired symbol.
`Datum.radon_glues` uses these results with the normalized Haar measures.
At every number-field place, continuous charts satisfying (4.2) have
absolutely convergent line integrals, including at τ = 0. In multiplicative
Haar measure, the integrand is bounded by a constant times
min(|x|ᵥ^(1/n), |x|ᵥ^(−1/n)). Dominated convergence gives joint continuity.
A cutoff removes the singularity at the origin. On a compact set of output
vectors, the determinant equation bounds the values of τ for which this
cutoff affects the integral. The Radon slices therefore decay rapidly in τ,
uniformly on each such compact set. Every local Schwartz section satisfies
(4.2), so both outer integrals converge absolutely as well.

At every place the normalized ray identity gives the leading term on a
transformed test section by evaluating a one-dimensional Fourier integral at
zero. The leading term of a test section vanishes. Linearity and uniqueness of
limits give the leading-term map on the entire Schwartz space. Its two
archimedean charts are continuous. At every place the charts glue, and their
power-dilation law follows by reparametrizing the ray limit. The leading term
commutes with the two shear generators. Its kernel is invariant under every
element of the local cover, and the cover acts on the space of leading terms.

The defining integral gives a linear map to pairs of chart functions at every place.
The reverse marginal identity on tests and ordinary Fourier inversion identify the
second transform of each test with its diagonal translate. The diagonal preserves
tests at every place, giving an endomorphism by restriction to the span. The
chosen Fourier operator `fourier` uses this construction at every place. At
tame finite places `tame_schwartz_inversion` constructs the Fourier
automorphism independently. At finite places the normalized rays extend to bounded Schwartz–Bruhat families over compact
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
the one-dimensional power-ray formula. Both marginal kernels are Schwartz–Bruhat
for every Schwartz section at every number-field place. For a pure tensor at
almost every finite place the axis density is the indicator of the local integers.
The remaining analytic input to Lemma A.6 is the Archimedean case of the reverse Fourier identity on test
sections (Lemma A.2). Lean proves the identity on tests at every finite place. The finite-place proof establishes
absolute convergence of the multiplicative difference integral for finite-place
tests and its vanishing when the Hilbert character is nontrivial. For an n-th
power parameter the cocycle splits the integral into contributions from its
distinct roots. At every finite place the linear-factor integral is absolutely
convergent and evaluates to the axis value times the multiplicative Fourier
integral of the test. The reciprocal change of variables uses the measure
obtained by weighting additive self-dual measure by the inverse modulus.
At every finite place, for test sections, subtracting the axis value gives
joint absolute convergence and justifies the exchange of the three integrals.
At every finite place the right kernel of the normalized Hilbert pairing consists
of the powers. Localizing the frequency test gives the pointwise sum over the
roots of −sy in Appendix A, including at primes dividing the degree.
On a sufficiently small ball around a nonzero root a, the power map is
bijective onto a ball with radius scaled by |n a^(n−1)|. Partitioning the
compact support into disjoint such balls gives the integrated change of
variables at all finite places. This proves the reverse
marginal Fourier identity on test sections. Ordinary Fourier inversion gives
the square of the defining integral transform on the vertical axis. The upper
and lower shears preserve finite-place test sections, so the equality extends
to both charts. Diagonal covariance gives the square on transforms of test sections as
well. Absolute convergence gives linearity on their span, and the square
formula gives bijectivity. The finite-place right-kernel theorem supplies the arithmetic input to this argument in every residue characteristic.

For a real or complex test section, restricting the rapid chart to the vertical
axis gives a Schwartz function flat at zero. Pullback by the power map preserves
flatness. At a real place flatness permits multiplication by a power of the
absolute value. At a complex place the modulus is the squared Euclidean norm.
For a transformed test section the density is a scalar multiple of the ordinary
Fourier transform of the original axis line integral, including at zero.
Linearity therefore gives Schwartz regularity of the density on the whole span.
The same transform relation applied to an arbitrary section identifies the
Fourier transform of its line integral with a Schwartz–Bruhat function.
Ordinary Fourier inversion recovers the line integral at every point.

Both shear operators preserve the local Schwartz space at every place. In
the real and complex cases local changes of chart reduce the estimates for
all derivatives to those for a real-linear coordinate change. The inverse
shear uses the negative parameter. At tame places the constructed integral
automorphism commutes with the group generated by these shears and the
central scalars (`tame_transform_equivariant`). Identifying the projection of the
resulting operator group to SL₂ and proving the Plancherel identity in
Theorem 7.1 remain open.

Lemma B.3, `Datum.powerClass_poisson`, is proved over number fields. The
Hilbert pairing identifies the image of the rational power classes with its
adelic annihilator. After restriction to a sufficiently large set of places,
the two sums are finite Fourier sums on the image of the $S$-units.
[PowerClassPoisson](MetaplecticSummation/PowerClassPoisson.lean)

For every pure tensor in Proposition B.4, the sums of the zero-frequency
terms agree. The proof identifies the class integral with the integral of
the normalized axis density and reindexes the rational classes by $x ↦ -1/x$.
Summing a convergent series over all rational power classes and power
parameters gives exactly $n$ copies of the original sum.
[Class integrals](MetaplecticSummation/PowerClassIntegrals.lean) ·
[Global comparison](MetaplecticSummation/FourierCoefficients/Basic.lean) ·
[Rational multiplicity](MetaplecticSummation/RationalPowerSums.lean)

Ordinary additive Poisson now applies to both tensors in Proposition B.4 for
each rational power-class representative. The normalized adelic Fourier
integral is the product of the local self-dual integrals at every adelic
frequency. Both diagonal series converge absolutely. The axis-line
specialization uses the Archimedean marginal identity in its local
Schwartz regularity proof. At almost all primes, the basic marginal vanishes
outside classes represented by integral units. Only finitely many rational
classes can contribute. Summing the second identity
at the representative $-1/y'$ yields the boundary evaluated at $y'$
in the definition of $T$.
[Constant-term identity](MetaplecticSummation/ConstantTermPoisson.lean) ·
[Support on rational classes](MetaplecticSummation/ConstantTermSupport.lean) ·
[Product Poisson](MetaplecticSummation/AdelicFourierIntegrals.lean) ·
[Real and complex tensors](MetaplecticSummation/AdelicTests.lean) ·
[Finite-adelic Fourier integrals](MetaplecticSummation/FiniteAdelicIntegrals.lean) ·
[Conductor and finite volumes](MetaplecticSummation/TraceConductor.lean)

The global product calculations cancel the normalizing constants at rational arguments
and identify the leading-term contributions at zero. For Lemma B.2, the
points with nonzero first coordinate have rational slopes. Periodizing
each slope over the additive quotient and integrating unfolds the series
to adelic integrals. A single summable majorant on the fundamental domain
gives absolute convergence. Substitution in the local integrals and the
product formula give the marginal at frequency zero and the Jacquet
integral at frequency one. [Unfolding and local factors](MetaplecticSummation/FourierCoefficients/LocalFactors.lean)

For Theorem 9.1, `theta_idele_bound` proves Lemma B.1 over number fields.
The sum of the majorant over nonzero rational vectors is bounded by a
constant times |a|^(−2−κ), uniformly for all ideles a. Applying this to
Schwartz sections uses local growth. At finite places Lean derives it from
the ray extensions and compact support, with constant one for the basic
vector. At real and complex places the bound follows for test functions
from their defining rapid decay. For transformed test sections, the power-ray
identity and a compact set of representatives for the dominant-coordinate
cones reduce (4.2) to rapid decay of the ordinary Fourier integrals of the
Radon slices. Their joint continuity and uniform boundedness at all frequencies follow
from the integral estimates. For high frequencies, translating a slice by
a/u at frequency u gives a fixed nontrivial character multiplier. An iterated
forward difference then bounds the Fourier integral by derivatives of the
same order. This proves the required uniform Fourier decay for bounded
Schwartz families at both real and complex places. The theorem
`arch_radon_schwartz_slices` proves that the Radon slices of a test section
form such a family. For a linear determinant parameter, differentiating a chart
along the affine line gives an integrable majorant at every derivative order.
Pullback by τ ↦ τⁿ preserves bounded sets of Schwartz functions. Together these
prove the slice assertion of Lemma 4.2(iii). Its additional assertions about
joint smoothness and derivatives in the output vector remain open at infinite places.

For every nontrivial adelic character trivial on the diagonal, the annihilator
of the local integers equals the local integers at almost every finite place.
To see this, take compact representatives for the adelic quotient with
integral finite components. Only finitely many rational translates of this
compact set meet its annihilator. The rational translation parameters are
integral at almost every prime, which bounds the local annihilator there.
The same compactness argument proves that every local component of the
character is nontrivial. Both character results follow from the adelic
character and lattice alone.

At almost every finite place the self-dual measure gives the local integers
volume one, the local Fourier operator fixes the basic vector, and the
ordinary Fourier transform of a pure tensor's axis density is the indicator
of the local integers at every frequency. The basic-vector identity supplies
the compatibility required to form the adelic Fourier operator.

For Lemma B.5, a single restricted lift of a rational matrix acts by right
multiplication on rational evaluations for every adelic section. For
Lemma B.7 the integral of the translated theta difference over the
upper unipotent quotient vanishes under the two local leading-term
hypotheses. [Rational lifts](MetaplecticSummation/RationalLifts.lean) ·
[Translated constant term](MetaplecticSummation/TranslatedConstantTerm.lean)

The global vanishing statement of Proposition B.6 remains admitted in
`thetaDifference_vanishing`. Given this input, Lean constructs the boundary
functional. Modifying a single finite factor gives a functional that descends
through the adelic leading-term map (Lemma B.10). Reindexing the theta sum
under the square of Fourier transformation yields the boundary identity.
The same local modification determines the boundary functional uniquely.
These arguments also depend on earlier results about local Fourier inversion
and the almost-everywhere invariance of the basic vectors. For the current list of direct
proof obligations, run `rg -n '\bsorry\b' MetaplecticSummation`.

## Reading the Gauss-sum formulas

`lineSummation` chooses one family of coefficients for all test weights at a
fixed set of places. Its outer sums run over nonzero field elements.
At each number-field place a single power class supports a test with
weighted integral one. Finite sums of these tests realize any vector of
moments. Unfolding the Jacquet lifts and their transforms gives two
absolutely convergent sums, each multilinear in the tests. If all moments
vanish at one place, the lift and its transform have zero leading terms
there. The Poisson vanishing criterion applied to upper unipotent translates
then identifies their Fourier coefficients. The difference of the two sums
therefore descends to a multilinear form on the moment vectors. Evaluation
on products of the normalized tests determines its coefficients uniquely.
The remaining project admissions used by this deduction are the Archimedean
reverse marginal identity on tests and Proposition B.6 on the theta
difference.
For any covering degree, the original summand has finite support on those
elements. The local tests at S give bounded radii, the basic factors outside S
vanish on nonintegral elements, and the rational box count applies.
In degree one, the local dual of a test weight is evaluation at the reciprocal
argument. The same identity holds for the basic Jacquet factor at every finite
conductor. Reindexing the finite sum by inversion proves `line_degree_one`
with zero main term independently of `lineSummation`. The project dependencies
that still contain admissions include the Archimedean
reverse marginal identity on tests used to construct the local Fourier operator.
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
ordinary Gauss-sum factorization uses the normalized family of
Hilbert symbols. The basic Jacquet evaluation uses this same arithmetic input.

At a tame finite place, the explicit charts for the basic vector satisfy gluing
and invariance under integral shears. With unramified character the integral
over a vertical line is one when the valuation of its nonzero first coordinate
is a nonnegative multiple of n, and zero otherwise. The Fourier integral on the axis then gives
the original basic vector. Changing the character gives Corollary 6.5 for a
local conductor parameter b. These calculations use the explicit charts
before passing to the Schwartz space. For Proposition 6.3(ii), the primitive
shell gives a test section. Subtracting a power dilation removes the interior
shells. Applying the transform expresses the basic vector as a linear
combination of a dilated test section and a transformed test section.
Rescaling the character gives the result at every conductor.

At every place, a compactly supported test weight W lifts to a test section
whose Jacquet integral equals W. The X-chart of the lift is
|x|ᵥ⁻¹ W(x) β(y/x), where β has Fourier coefficient one at the chosen
frequency. At finite places β is a normalized compact-open ball indicator.
At real and complex places, smooth compact tests separate the continuous
additive character from zero. The support stays in a compact subset of the
X-chart, and the Hilbert-symbol transition preserves smoothness and rapid
decay on the Y-chart. The same β works for all W. The power average of the
lift is given on the X-chart by the weighted moment of W over xFᵥˣⁿ.
If every such moment vanishes, the average vanishes on both charts.

For every local Schwartz section Φ, the vertical integral defining JΦ
converges absolutely and varies continuously on the units. It is locally
constant at finite places. The normalized shear difference preserves both
JΦ and J(ℱΦ) under iteration. For an X-chart integrable with respect to
d×x dy, the fixed-parameter Radon identity follows by Fubini, with the
L¹ norm of the X-chart bounding all transverse integrals. The Jacquet lift
of a compact test weight satisfies this integrability condition. At finite
places, the third normalized difference provides such a representative for
every Schwartz section. Its vertical slice has L¹ norm bounded by a constant
times min(|c|ᵥ^(1/n), |c|ᵥ^(-A)) for each A ≥ 0. The normalized ray
extensions give uniform vanishing on a cone about the vertical axis.
Integration over multiplicative annuli then proves absolute integrability
of the regularized X-chart and of every Jacquet weight.

The weak Jacquet identity follows for any section whose X-chart is
absolutely integrable for d×x dy. At every finite place, including places
dividing n, the shear representative gives the identity for every section.
Testing on a compact open ball around one gives Proposition 10.8 for a
compactly supported test weight. At an infinite place, smooth tests
supported away from zero give the same pointwise identity for sections
with integrable X-chart. In particular, the explicit lift of every test
weight W satisfies both $J\Phi = W$ and $J(\mathcal F\Phi) = W^\vee$ at every
place, with the explicit kernel formula for $W^\vee$. The finite-place formulas and the all-place lift
use the normalized Hilbert symbols and the Fourier endomorphism constructed
from the reverse marginal identity on tests.

For an arbitrary section at a real or complex place, the weak and pointwise
formulas still use `arch_integrableOn_shear_vertical`. This is the open
estimate for the third shear difference on |x|ᵥ < 1 and ‖y‖ > ‖x‖.
The chart growth bound proves absolute integrability on the complementary
region. Together these give an integrable representative with the same
two Jacquet weights. Applied to a difference with zero Jacquet integral,
Proposition 10.8 gives descent to the full Jacquet image. The local square
formula then gives inversion and bijectivity on that image.

The untwisted S-integer summation formula follows in Lean from the adelic
line formula, the identity for the transformed basic Jacquet weight, and
`product_basic`. Lean now derives the basic-weight identity from Corollary 6.5
by changing the line variable.
Both S-integer series converge absolutely by the summability in the adelic
line formula. The nonintegral terms vanish, and the same power-class coefficients
from the adelic formula occur in the S-integer formula.

With empty twist set, `mainTerm` forms both the coefficients and the
multiplicative measures using the scaled character. With nonempty twist set,
Lean proves that each power-class moment vanishes by translating by an n-th
power of a local unit on which the twisting character is nontrivial. This
gives the absolutely convergent adelic identity from the adelic line formula.
The local twisted-vector evaluation now follows from unit Gauss integrals.
A unit detecting the character gives vanishing below the conductor shell,
and an additive period gives vanishing above it. Parseval fixes the absolute
value on the shell. Tame power lifting preserves the principal-unit depth,
so the conjugate character twisted by the Hilbert symbol has the conductor
of the original character's n-th power. Substitution in the Jacquet kernel
then gives the two Gauss factors and the epsilon norm. After reindexing, the product at the conductor
primes gives ε, the conjugate twisting character and the residue symbol
with denominator f. For the original adelic sum, splitting the product over S,
the conductor primes and the remaining places gives the stated sum over
nonzero S-integers, including the square-root normalization for the scaled
character. On the dual side the reindexed basic factor outside S and the
conductor primes contributes one Hilbert symbol. For an integral argument
with nonzero twist, their product is the residue symbol with that argument
as denominator. Reindexing the dual sum and cancelling the common square-root
factor proves Theorem 10.34 from the adelic line formula and the local
evaluations. Both S-integer series converge absolutely. The
empty conductor retains the scaled main term.

The quadratic-dual corollary and its sextic specialization now follow in Lean
from Theorem 10.34. For an odd covering degree, the quadratic twist has
conductor exponent one at each prime dividing the squarefree modulus.
Power reciprocity identifies the dual summand, including its Hilbert factor
at S. For degree three, compatibility between the degree-six and degree-three
embeddings yields the sextic specialization. The residue-symbol identities
also cover numerators sharing a prime with the modulus, where the symbols
vanish.

The scope is the principal formulas over number fields and their completions.
The local estimates, illustrative examples and intermediate proof lemmas do
not have individual Lean statements throughout.
