import Mathlib

/-!
# A Schwartz space for the n-fold cover of SL₂: advertised statements

This file states, against Mathlib alone, the main results of the paper
*A Schwartz space for the n-fold cover of SL₂* (P. D. Nelson) over a number
field `F` containing a primitive `n`th root of unity:

* `NFoldCover.schwartz_inversion` — Theorem 7.1 (Fourier inversion, equivariance
  under the local cover, Plancherel) at every place;
* `NFoldCover.basicCharts_mem` — Proposition 6.3(ii) (the basic vector lies in
  the Schwartz space at every finite place not dividing `n`);
* `NFoldCover.poisson` — Theorem 9.1 (the Poisson formula, with a unique
  boundary functional) and `NFoldCover.poisson_of_leading_eq_zero`
  (Corollary 9.2);
* `NFoldCover.twistedGaussSummation` — Theorem 10.34 (twisted sums of Gauss
  sums of order `n`) and `NFoldCover.quadraticDual` — Corollary 10.40.

Canonical objects (self-dual measures, Hilbert symbols, the local Fourier
transform on the Schwartz space, leading terms, the adelic maps) are not
constructed here: they are **characterized** by their defining properties,
bundled in `Setup` and `Data`. The theorems `exists_setup` and `nonempty_data`
show that such data exist, and each characterization determines the object
uniquely, so the statements are not vacuous and do not depend on choices.

Conventions. A genuine function on the punctured plane is stored as a pair of
charts `(Φ_X, Φ_Y)`: `Φ_X x y` is defined for `x ≠ 0`, `Φ_Y x y` for `y ≠ 0`,
and they are related by `Φ_X = {x, y} Φ_Y` (`Glues`). Places are infinite
places of `F` or height-one primes of its ring of integers.
-/

noncomputable section

namespace NFoldCover

open NumberField IsDedekindDomain Filter MeasureTheory
open scoped Topology ContDiff ENNReal TensorProduct

/-! ## Places, completions and characters -/

section Places
variable (F : Type) [Field F] [NumberField F]

/-- The places of `F`: infinite places and finite places (height-one primes). -/
abbrev Place := InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)

/-- The completion `F_v`. -/
def LocalField : Place F → Type
  | .inl w => w.Completion
  | .inr p => p.adicCompletion F

instance localNormedField (v : Place F) : NormedField (LocalField F v) := by
  cases v with
  | inl w => exact inferInstanceAs (NormedField w.Completion)
  | inr p => exact inferInstanceAs (NormedField (p.adicCompletion F))

instance (v : Place F) : MeasurableSpace (LocalField F v) := borel _
instance (v : Place F) : BorelSpace (LocalField F v) := ⟨rfl⟩

/-- The embedding `F → F_v`. -/
def diagonal (v : Place F) : F →+* LocalField F v := by
  cases v with
  | inl w => exact algebraMap F w.Completion
  | inr p => exact FinitePlace.embedding p

/-- The normalized absolute value `|x|_v` (the square of the usual absolute value
at a complex place). -/
def modulus (v : Place F) (x : LocalField F v) : ℝ :=
  match v with
  | .inl w => ‖x‖ ^ w.mult
  | .inr _ => ‖x‖

/-- The adele ring of `F`. -/
abbrev Adeles := AdeleRing (𝓞 F) F

/-- The adele that is `x` at the place `v` and zero elsewhere. -/
def singleAdele (v : Place F) : LocalField F v → Adeles F := by
  classical
  cases v with
  | inl w => exact fun x => (Pi.single w x, 0)
  | inr p => exact fun x => (0, RestrictedProduct.single
      (fun q : HeightOneSpectrum (𝓞 F) => q.adicCompletionIntegers F) p x)

variable {F}

/-- The local component `ψ_v` of an adelic character. -/
def localChar (ψ : AddChar (Adeles F) Circle) (v : Place F) (x : LocalField F v) : ℂ :=
  ψ (singleAdele F v x)

/-- Plancherel on continuous compactly supported functions for an integral kernel. -/
def KernelPlancherel {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    (kernel : K → K → ℂ) (μ : Measure K) : Prop :=
  ∀ f : K → ℂ, Continuous f → HasCompactSupport f →
    (∫⁻ y, ‖∫ x, f x * kernel x y ∂μ‖ₑ^2 ∂μ) = ∫⁻ x, ‖f x‖ₑ^2 ∂μ

/-- `μ` is the Haar measure on `F_v` self-dual with respect to `ψ_v`. -/
def IsSelfDual (ψ : AddChar (Adeles F) Circle) (v : Place F)
    (dx : Measure (LocalField F v)) : Prop :=
  dx.IsAddHaarMeasure ∧ KernelPlancherel (fun x y => localChar ψ v (x*y)) dx

variable (F)

/-- The `n`th roots of unity in `F`. -/
abbrev Mu (n : ℕ) := rootsOfUnity n F

/-- A family of `μ_n`-valued pairings on the local multiplicative groups. -/
abbrev SymbolFamily (n : ℕ) := (v : Place F) → (LocalField F v)ˣ → (LocalField F v)ˣ → Mu F n

/-- The `n`th-power Hilbert symbols: continuous, bimultiplicative, skew, with
`{a, -a} = 1`, the tame normalization `{ϖ, u} ≡ u^((q-1)/n)` at finite places
prime to `n`, and Hilbert reciprocity. These properties determine the family. -/
structure IsHilbertFamily (n : ℕ) (H : SymbolFamily F n) : Prop where
  continuous_pair : ∀ v, Continuous (fun a : (LocalField F v)ˣ × (LocalField F v)ˣ =>
    diagonal F v (((H v a.1 a.2 : Fˣ) : F)))
  mul_left : ∀ v a b c, H v (a*b) c = H v a c * H v b c
  mul_right : ∀ v a b c, H v a (b*c) = H v a b * H v a c
  skew : ∀ v a b, H v a b * H v b a = 1
  neg_self : ∀ v a, H v a (-a) = 1
  tame_units : ∀ (p : HeightOneSpectrum (𝓞 F)), p.asIdeal.absNorm.Coprime n →
    ∀ a b : (LocalField F (.inr p))ˣ, ‖(a : LocalField F (.inr p))‖ = 1 →
      ‖(b : LocalField F (.inr p))‖ = 1 → H (.inr p) a b = 1
  tame_uniformizer : ∀ (p : HeightOneSpectrum (𝓞 F)), p.asIdeal.absNorm.Coprime n →
    ∀ π u : (LocalField F (.inr p))ˣ, ‖(π : LocalField F (.inr p))‖ = (p.asIdeal.absNorm : ℝ)⁻¹ →
      ‖(u : LocalField F (.inr p))‖ = 1 →
      ‖diagonal F (.inr p) (((H (.inr p) π u : Fˣ) : F)) -
        (u : LocalField F (.inr p)) ^ ((p.asIdeal.absNorm - 1) / n)‖ < 1
  unramified : ∀ a b : Fˣ, ∀ᶠ v in cofinite,
    H v (Units.map (diagonal F v) a) (Units.map (diagonal F v) b) = 1
  reciprocity : ∀ a b : Fˣ,
    (∏ᶠ v, H v (Units.map (diagonal F v) a) (Units.map (diagonal F v) b)) = 1

/-- The global choices of §9.1: a primitive `n`th root of unity, an embedding
`μ_n → ℂˣ`, a nontrivial continuous character `ψ` of `𝔸/F`, together with the
self-dual measures `μ v` for `ψ_v` and the Hilbert symbols `H`. -/
structure Setup (n : ℕ) where
  root : F
  primitive : IsPrimitiveRoot root n
  embedding : Mu F n →* ℂˣ
  injective : Function.Injective embedding
  character : AddChar (Adeles F) Circle
  continuous_character : Continuous character
  nontrivial : ∃ a, character a ≠ 1
  trivial_on_F : ∀ x : F, character (algebraMap F (Adeles F) x) = 1
  measure : ∀ v, Measure (LocalField F v)
  selfDual : ∀ v, IsSelfDual character v (measure v)
  hilbert : SymbolFamily F n
  isHilbert : IsHilbertFamily F n hilbert

end Places

/-! ## Genuine functions, the transform, the Schwartz space -/

/-- A genuine function in coordinates: the `X` chart on `x ≠ 0` and the `Y` chart on `y ≠ 0`. -/
abbrev Charts (K : Type*) [Field K] := (Kˣ → K → ℂ) × (K → Kˣ → ℂ)

section Local
variable {K : Type*} [Field K]

/-- The gluing relation `Φ_X(x, y) = h(x, y) Φ_Y(x, y)` on `xy ≠ 0`. -/
def Glues (h : Kˣ → Kˣ → ℂ) (f : Charts K) : Prop :=
  ∀ x y : Kˣ, f.1 x y = h x y * f.2 x y

/-- The two line integrals over `x y' - y x' = t^n` (§4.1). -/
def radon [MeasurableSpace K] (n : ℕ) (h : Kˣ → Kˣ → ℂ) (modulus : K → ℝ)
    (dx : Measure K) (f : Charts K) (t : K) : Charts K := by
  classical
  exact
    (fun u v => (∫ x, if hx : x ≠ 0 then
        f.1 (Units.mk0 x hx) ((x * v - t ^ n) / (u : K)) * h (Units.mk0 x hx) (-u)
        else 0 ∂dx) / (modulus u : ℂ),
     fun u v => (∫ y, if hy : y ≠ 0 then
        f.2 ((u * y + t ^ n) / (v : K)) (Units.mk0 y hy) *
          h (Units.mk0 y hy) v * h (-1) v else 0 ∂dx) / (modulus v : ℂ))

/-- Definition 4.4: the Fourier transform `ℱ`, `|n|^{-1/2}` times the Fourier
integral at `1` of the line integrals in `t`. -/
def transform [MeasurableSpace K] (n : ℕ) (ψ : K → ℂ) (h : Kˣ → Kˣ → ℂ) (modulus : K → ℝ)
    (dx : Measure K) (f : Charts K) : Charts K :=
  let c : ℂ := (Real.sqrt (modulus (n : K)))⁻¹
  let R := radon n h modulus dx f
  (fun u v => c * ∫ t, ψ t * (R t).1 u v ∂dx,
   fun u v => c * ∫ t, ψ t * (R t).2 u v ∂dx)

/-- `g` is the leading term `bΦ` of `f` (§8): in each chart,
`|μ|^(n-1) f(μ^n v) → g(v)` as `μ → 0`. -/
def IsLeadingTerm [TopologicalSpace K] (n : ℕ) (modulus : K → ℝ)
    (f g : Charts K) : Prop :=
  let atZero := comap (fun t : Kˣ => (t : K)) (𝓝 0)
  (∀ x y, Tendsto (fun t : Kˣ => (modulus t : ℂ) ^ (n - 1) *
      f.1 (t ^ n * x) ((t : K) ^ n * y)) atZero (𝓝 (g.1 x y))) ∧
  (∀ x y, Tendsto (fun t : Kˣ => (modulus t : ℂ) ^ (n - 1) *
      f.2 ((t : K) ^ n * x) (t ^ n * y)) atZero (𝓝 (g.2 x y)))

/-- The `X` chart extended by zero to `K × K`. -/
def xChart (f : Charts K) (p : K × K) : ℂ := by
  classical exact if h : p.1 ≠ 0 then f.1 (Units.mk0 p.1 h) p.2 else 0

/-- The `Y` chart extended by zero to `K × K`. -/
def yChart (f : Charts K) (p : K × K) : ℂ := by
  classical exact if h : p.2 ≠ 0 then f.2 p.1 (Units.mk0 p.2 h) else 0

/-- Test functions at a finite place: both charts locally constant, vanishing
outside a compact subset of `K² - {0}`. -/
def finiteTest [TopologicalSpace K] (f : Charts K) : Prop :=
  IsLocallyConstant (fun p : Kˣ × K => f.1 p.1 p.2) ∧
  IsLocallyConstant (fun p : K × Kˣ => f.2 p.1 p.2) ∧
  ∃ C : Set (K × K), IsCompact C ∧ (0 : K × K) ∉ C ∧
    ∀ p ∉ C, xChart f p = 0 ∧ yChart f p = 0

/-- Smooth on `U`, with every derivative decaying faster than any power of `‖x‖`
both at `0` and at `∞`. -/
def rapidChart {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (f : E → ℂ) : Prop :=
  ContDiffOn ℝ ∞ f U ∧ ∀ k N : ℕ, ∃ C : ℝ, ∀ x ∈ U,
    ‖iteratedFDeriv ℝ k f x‖ ≤ C * min (‖x‖ ^ N) ((‖x‖ ^ N)⁻¹)

/-- Test functions at an archimedean place, read in real coordinates via `e`. -/
def archTest {L : Type} [NormedField L] [NormedAlgebra ℝ L]
    (e : K ≃+* L) (f : Charts K) : Prop :=
  rapidChart {p : L × L | p.1 ≠ 0} (fun p => xChart f (e.symm p.1, e.symm p.2)) ∧
  rapidChart {p : L × L | p.2 ≠ 0} (fun p => yChart f (e.symm p.1, e.symm p.2))

end Local

/-- The algebraic restricted tensor product of the `V i` with respect to `basic`:
the span of the pure tensors `⊗ fᵢ` with `fᵢ = basicᵢ` for almost all `i`. -/
def restrictedTensor {ι : Type*} {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (basic : ∀ i, V i) :
    Submodule ℂ (⨂[ℂ] i, V i) :=
  Submodule.span ℂ (PiTensorProduct.tprod ℂ '' {x | ∀ᶠ i in cofinite, x i = basic i})

/-- Points of `F² - {0}`. -/
abbrev RationalPoint (F : Type*) [Field F] := {v : F × F // v ≠ 0}

/-- The value at a rational point of a local section, read in the `X` chart when
`x ≠ 0` and in the `Y` chart otherwise. -/
def pointValue {F : Type} [Field F] [NumberField F] (p : RationalPoint F) (v : Place F)
    (f : Charts (LocalField F v)) : ℂ := by
  classical exact if p.val.1 ≠ 0 then xChart f (diagonal F v p.val.1, diagonal F v p.val.2)
    else yChart f (diagonal F v p.val.1, diagonal F v p.val.2)

namespace Setup
variable {F : Type} [Field F] [NumberField F] {n : ℕ} (s : Setup F n)

/-- The complex-valued Hilbert symbol `{a, b}_v`. -/
def symbol (v : Place F) (a b : (LocalField F v)ˣ) : ℂ :=
  s.embedding (s.hilbert v a b)

/-- The space `𝒟_v` of genuine test functions. -/
def testSet (v : Place F) : Set (Charts (LocalField F v)) :=
  {f | Glues (s.symbol v) f ∧ (by
    classical
    cases v with
    | inr p => exact finiteTest f
    | inl w =>
      by_cases h : w.IsReal
      · exact archTest (InfinitePlace.Completion.ringEquivRealOfIsReal h) f
      · exact archTest (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp h)) f)}

/-- The transform `ℱ` at `v`, for `ψ_v` and its self-dual measure. -/
def integralTransform (v : Place F) :=
  transform n (localChar s.character v) (s.symbol v) (modulus F v) (s.measure v)

/-- Definition 4.9: the Schwartz space `𝒮_v = 𝒟_v + ℱ 𝒟_v`. -/
def schwartz (v : Place F) : Submodule ℂ (Charts (LocalField F v)) :=
  Submodule.span ℂ (s.testSet v ∪ s.integralTransform v '' s.testSet v)

/-- The basic vector `Φ⁰` at a finite place (§6): on the shell
`max(|x|,|y|) = q^(-nk)` it has weight `q^((n-1)k)`, and its chart for the larger
coordinate is `1`; it vanishes off these shells. -/
def basicCharts (p : HeightOneSpectrum (𝓞 F)) : Charts (LocalField F (.inr p)) := by
  classical
  let q := p.asIdeal.absNorm
  let weight (r : ℝ) : ℂ := ∑' k : ℕ,
    if r = ((q : ℝ) ^ (n*k))⁻¹ then (q : ℂ) ^ ((n-1)*k) else 0
  let X (x : (LocalField F (.inr p))ˣ) (y : LocalField F (.inr p)) :=
    weight (max ‖(x : LocalField F (.inr p))‖ ‖y‖) *
      (if ‖y‖ ≤ ‖(x : LocalField F (.inr p))‖ then 1 else
        if h : y ≠ 0 then s.symbol (.inr p) x (Units.mk0 y h) else 0)
  let Y (x : LocalField F (.inr p)) (y : (LocalField F (.inr p))ˣ) :=
    weight (max ‖x‖ ‖(y : LocalField F (.inr p))‖) *
      (if ‖x‖ ≤ ‖(y : LocalField F (.inr p))‖ then 1 else
        if h : x ≠ 0 then s.symbol (.inr p) y (Units.mk0 x h) else 0)
  exact (X, Y)

/-- The reference vectors of the restricted tensor product: the basic vector at
finite places prime to `n`, and (immaterially) zero at the finitely many others. -/
def basicVector : (v : Place F) → Charts (LocalField F v)
  | .inl _ => 0
  | .inr p => if p.asIdeal.absNorm.Coprime n then s.basicCharts p else 0

/-- Linear automorphisms of the local Schwartz space. -/
abbrev Operators (v : Place F) := s.schwartz v ≃ₗ[ℂ] s.schwartz v

/-- The upper unipotent `n(u)`: `(n(u)Φ)_X(x, y) = Φ_X(x, y + ux)`, fixing the `Y`
chart on the axis `x = 0`. -/
def IsUpper (v : Place F) (u : LocalField F v) (g : s.Operators v) : Prop :=
  ∀ Φ, (∀ x y, (g Φ).val.1 x y = Φ.val.1 x (y + u * x)) ∧
    ∀ y, (g Φ).val.2 0 y = Φ.val.2 0 y

/-- The lower unipotent `n⁻(u)`. -/
def IsLower (v : Place F) (u : LocalField F v) (g : s.Operators v) : Prop :=
  ∀ Φ, (∀ x y, (g Φ).val.2 x y = Φ.val.2 (x + u * y) y) ∧
    ∀ x, (g Φ).val.1 x 0 = Φ.val.1 x 0

/-- Multiplication by a scalar in `μ_n`. -/
def IsCentralScalar (v : Place F) (g : s.Operators v) : Prop :=
  ∃ z : Mu F n, ∀ Φ, g Φ = ((s.embedding z : ℂˣ) : ℂ) • Φ

/-- The local cover `SL̃₂(F_v)` acting on `𝒮_v`: the group generated by the
scalars in `μ_n` and the operators `n(u)`, `n⁻(u)` (Proposition 5.1). -/
def cover (v : Place F) : Subgroup (s.Operators v) := Subgroup.closure
  {g | s.IsCentralScalar v g ∨ (∃ u, s.IsUpper v u g) ∨ ∃ u, s.IsLower v u g}

/-- The action of the diagonal lift `h(a)` (Lemma 5.4). -/
def torusCharts (v : Place F) (a : (LocalField F v)ˣ) (Φ : Charts (LocalField F v)) :
    Charts (LocalField F v) :=
  (fun x y => s.symbol v x a * s.symbol v (-1) a * Φ.1 (a*x) (y/a),
   fun x y => s.symbol v a y * Φ.2 (a*x) (y/a))

/-- `‖Φ‖₂² = ∫ |Φ_X|² dx dy`. -/
def mass (v : Place F) (Φ : Charts (LocalField F v)) : ℝ≥0∞ :=
  ∫⁻ p, ‖xChart Φ p‖ₑ ^ 2 ∂((s.measure v).prod (s.measure v))

end Setup

/-! ## Weights, local transforms and global Gauss sums (§10) -/

section Weights
variable {F : Type} [Field F] [NumberField F]

/-- A function on `F_v^×`. -/
abbrev Weight (v : Place F) := (LocalField F v)ˣ → ℂ

/-- Smoothness of a function on `K^×`, read in real coordinates via `e`. -/
def archSmooth {K L : Type} [Field K] [NormedField L] [NormedAlgebra ℝ L]
    (e : K ≃+* L) (W : Kˣ → ℂ) : Prop := by
  classical
  exact ContDiffOn ℝ ∞ (fun x => if h : e.symm x ≠ 0 then W (Units.mk0 _ h) else 0) {0}ᶜ

/-- `W ∈ C_c^∞(F_v^×)`: compactly supported in `F_v^×`, smooth (archimedean `v`) or
locally constant (finite `v`). -/
def TestWeight (v : Place F) (W : Weight v) : Prop :=
  HasCompactSupport W ∧ (by
    classical
    cases v with
    | inr p => exact IsLocallyConstant W
    | inl w =>
      by_cases h : w.IsReal
      · exact archSmooth (InfinitePlace.Completion.ringEquivRealOfIsReal h) W
      · exact archSmooth (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp h)) W)

/-- A weight `W_𝔭` at each place of `S`. -/
abbrev Weights (S : Finset (Place F)) := (v : S) → Weight v.val

/-- Each `W_𝔭` lies in `C_c^∞(F_𝔭^×)`. -/
abbrev Admissible {S : Finset (Place F)} (W : Weights S) := ∀ v, TestWeight v.val (W v)

/-- The cosets of `F_v^{×n}` in `F_v^×`. -/
abbrev PowerClass (n : ℕ) (v : Place F) := (LocalField F v)ˣ ⧸ (powMonoidHom n :
  (LocalField F v)ˣ →* (LocalField F v)ˣ).range

/-- Tuples `β = (β_𝔭)_{𝔭 ∈ S}` of power classes. -/
abbrev Classes (n : ℕ) (S : Finset (Place F)) := (v : S) → PowerClass n v.val

/-- The ring `𝒪_S` of `S`-integers. -/
abbrev SIntegers (S : Finset (Place F)) :=
  ({p : HeightOneSpectrum (𝓞 F) | Sum.inr p ∈ S}.integer F)

/-- `𝒪_S - {0}`. -/
abbrev NonzeroInteger (S : Finset (Place F)) := {c : SIntegers S // c ≠ 0}

/-- A nonzero `S`-integer as an element of `F^×`. -/
def fieldUnit {S : Finset (Place F)} (c : NonzeroInteger S) : Fˣ :=
  Units.mk0 (c.val : F) (fun h => c.property (Subtype.ext h))

/-- `|x|_S = ∏_{v ∈ S} |x|_v`. -/
def sNorm (S : Finset (Place F)) (x : F) := ∏ v ∈ S, modulus F v (diagonal F v x)

/-- The image of `x ∈ F^×` in `F_v^×`. -/
abbrev atPlace (v : Place F) (x : Fˣ) : (LocalField F v)ˣ := Units.map (diagonal F v) x

/-- The unit group `𝔬_𝔭^×`. -/
def integralUnits (p : HeightOneSpectrum (𝓞 F)) : Subgroup (LocalField F (.inr p))ˣ where
  carrier := {u | ‖(u : LocalField F (.inr p))‖ = 1}
  one_mem' := norm_one
  mul_mem' := by
    intro a b ha hb
    change ‖(a : LocalField F (.inr p)) * b‖ = 1
    rw [norm_mul, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    change ‖((a⁻¹ : (LocalField F (.inr p))ˣ) : LocalField F (.inr p))‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, ha, inv_one]

/-- Unitary characters of `𝔬_𝔭^×`. -/
abbrev UnitChar (p : HeightOneSpectrum (𝓞 F)) := integralUnits p →* Circle

/-- The weight `1_{𝔬_𝔭^×} χ`. -/
def charWeight {p : HeightOneSpectrum (𝓞 F)} (χ : UnitChar p) : Weight (.inr p : Place F) := by
  classical exact fun x => if h : x ∈ integralUnits p then ((χ ⟨x,h⟩ : Circle) : ℂ) else 0

/-- `χ` is trivial on `1 + 𝔭^k` (on `𝔬_𝔭^×` if `k = 0`). -/
def trivialAtLevel {p : HeightOneSpectrum (𝓞 F)} (χ : UnitChar p) (k : ℕ) : Prop :=
  ∀ u : integralUnits p, (k = 0 ∨ ‖((u.val : LocalField F (.inr p)) - 1)‖ ≤
    ((p.asIdeal.absNorm : ℝ) ^ k)⁻¹) → χ u = 1

/-- The twisting data of Theorem 10.34: a finite set `T` of primes outside `S`,
characters `χ_𝔭` of `𝔬_𝔭^×` with `χ_𝔭^n` ramified of conductor exponent `e_𝔭 > 0`,
and `f ∈ 𝒪_S` generating `∏_{𝔭 ∈ T} 𝔭^{e_𝔭}` (with `f = 1` if `T` is empty). -/
structure Twist (n : ℕ) (S : Finset (Place F)) (f : NonzeroInteger S) where
  primes : Finset (HeightOneSpectrum (𝓞 F))
  outside : ∀ p ∈ primes, Sum.inr p ∉ S
  character : (p : primes) → UnitChar p.val
  continuous_char : ∀ p, Continuous (character p)
  exponent : primes → ℕ
  positive : ∀ p, 0 < exponent p
  conductor : ∀ p, IsLeast {k | trivialAtLevel (character p ^ n) k} (exponent p)
  generator : ∀ p : primes, ‖diagonal F (.inr p.val) (fieldUnit f)‖ =
    ((p.val.asIdeal.absNorm : ℝ) ^ exponent p)⁻¹
  unit_elsewhere : ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S → p ∉ primes →
    ‖diagonal F (.inr p) (fieldUnit f)‖ = 1
  empty_modulus : primes = ∅ → fieldUnit f = 1

/-- `χ(c) = ∏_{𝔭 ∈ T} (1_{𝔬_𝔭^×} χ_𝔭)(c)`. -/
def twistValue {n : ℕ} {S : Finset (Place F)} {f : NonzeroInteger S} (T : Twist n S f) (c : Fˣ) :=
  ∏ p : T.primes, charWeight (T.character p) (atPlace (.inr p.val) c)

/-- `W_S(c) = ∏_{v ∈ S} W_v(c)`. -/
def sWeight {S : Finset (Place F)} (W : Weights S) (c : Fˣ) :=
  ∏ v : S, W v (atPlace v.val c)

end Weights

namespace Setup
variable {F : Type} [Field F] [NumberField F] {n : ℕ} (s : Setup F n)

/-- `∫_{F_v^×} f(x) d^×x` with `d^×x = dx/|x|_v` and `dx` self-dual. -/
def lineIntegral (v : Place F) (f : Weight v) : ℂ := by
  classical
  exact ∫ x, if h : x ≠ 0 then f (Units.mk0 x h) / (modulus F v x : ℂ) else 0 ∂(s.measure v)

/-- The inner integral in the transform `W ↦ W^∨` (Proposition 10.8). -/
def kernelIntegral (v : Place F) (W : Weight v) (c : (LocalField F v)ˣ) (t : LocalField F v) :=
  s.lineIntegral v fun x => W x * s.symbol v x (-c) *
    localChar s.character v (-(t ^ n) / ((c : LocalField F v) * x))

/-- Definition 10.7 / Proposition 10.8: `W^∨(c) = |n|^{-1/2} ∫ ψ(t) ∫ W(x) {x,-c}
ψ(-tⁿ/(cx)) d^×x dt`. -/
def dualWeight (v : Place F) (W : Weight v) (c : (LocalField F v)ˣ) : ℂ :=
  (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ *
    ∫ t, localChar s.character v t * s.kernelIntegral v W c t ∂(s.measure v)

/-- `∫_β W(x) |x|^{1/n} d^×x`. -/
def classMoment (v : Place F) (W : Weight v) (β : PowerClass n v) : ℂ := by
  classical
  exact s.lineIntegral v fun x => if QuotientGroup.mk x = β then
    W x * ((modulus F v x ^ (1 / (n : ℝ)) : ℝ) : ℂ) else 0

/-- `∏_{𝔭 ∈ S} ∫_{β_𝔭} W_𝔭(x) |x|^{1/n} d^×x`. -/
def moment {S : Finset (Place F)} (W : Weights S) (β : Classes n S) : ℂ :=
  ∏ v : S, s.classMoment v.val (W v) (β v)

/-- `W_S^∨(c) = ∏_{v ∈ S} W_v^∨(c)`. -/
def sDual {S : Finset (Place F)} (W : Weights S) (c : Fˣ) :=
  ∏ v : S, s.dualWeight v.val (W v) (atPlace v.val c)

/-- `ψ_S(x) = ∏_{v ∈ S} ψ_v(x)`. -/
def sPsi (S : Finset (Place F)) (x : F) := ∏ v ∈ S, localChar s.character v (diagonal F v x)

/-- `{a, b}_S = ∏_{v ∈ S} {a, b}_v`. -/
def sSymbol (S : Finset (Place F)) (a b : Fˣ) := ∏ v ∈ S, s.symbol v (atPlace v a) (atPlace v b)

/-- Definition 9.3: the power residue symbol `(a/c)_n = ∏_{𝔭 | c, 𝔭 ∉ S} {c, a}_𝔭`
if `a` is a unit at every such `𝔭`, and `0` otherwise. -/
def residue (S : Finset (Place F)) (a c : F) : ℂ := by
  classical
  exact ∏ᶠ p : HeightOneSpectrum (𝓞 F), if Sum.inr p ∉ S ∧ ‖diagonal F (.inr p) c‖ < 1 then
    if h : a ≠ 0 ∧ c ≠ 0 ∧ ‖diagonal F (.inr p) a‖ = 1 then
      s.symbol (.inr p) (atPlace _ (Units.mk0 c h.2.1)) (atPlace _ (Units.mk0 a h.1))
    else 0 else 1

/-- Definition 10.32: `g(b, c) = ∑_{d ∈ (𝒪_S/c)^×} (d/c)_n ψ_S(bd/c)`, evaluated on
representatives (the summand does not depend on the choice). -/
def gauss (S : Finset (Place F)) (b c : SIntegers S) : ℂ :=
  ∑ᶠ u : (SIntegers S ⧸ Ideal.span {c})ˣ,
    let a : SIntegers S := Quotient.out (u : SIntegers S ⧸ Ideal.span {c})
    s.residue S a c * s.sPsi S ((b : F) * a / c)

/-- The summand `|τ|_S^{n-1} g(b, c/τⁿ)` if `τⁿ | c`, and `0` otherwise. -/
def powerDivisorTerm (S : Finset (Place F)) (b c t : SIntegers S) : ℂ := by
  classical exact if h : t ^ n ∣ c then
    (sNorm S t : ℂ) ^ (n-1) * s.gauss S b h.choose else 0

/-- Definition 10.32: `g̃(b, c) = |c|_S^{-1} ∑_{τ ∈ 𝒪_S/𝒪_S^×, τⁿ | c} |τ|_S^{n-1} g(b, c/τⁿ)`. -/
def normalizedGauss (S : Finset (Place F)) (b c : SIntegers S) : ℂ :=
  (sNorm S c : ℂ)⁻¹ * ∑ᶠ t : Associates (SIntegers S), s.powerDivisorTerm S b c (Quotient.out t)

/-- `ε = ∏_{𝔭 ∈ T} (1_{𝔬_𝔭^×} χ_𝔭)^∨((b f^{n-1})^{-1})` (10.33). -/
def epsilon {S : Finset (Place F)} {f : NonzeroInteger S} (T : Twist n S f) (b : Fˣ) :=
  ∏ p : T.primes, s.dualWeight (.inr p.val) (charWeight (T.character p))
    (atPlace _ (b * fieldUnit f ^ (n-1))⁻¹)

/-- §9.1: `S` is nonempty, contains the archimedean places, and every `𝔭 ∉ S` is
prime to `n` with `ψ_𝔭` trivial on `𝔬_𝔭`. -/
def GoodOutside (S : Finset (Place F)) : Prop :=
  S.Nonempty ∧ (∀ w, Sum.inl w ∈ S) ∧ ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S →
    p.asIdeal.absNorm.Coprime n ∧ ∀ x : LocalField F (.inr p), ‖x‖ ≤ 1 →
      localChar s.character (.inr p) x = 1

/-- `ψ_v` is unramified: `𝔬_v` is the largest fractional ideal on which it is trivial. -/
def UnramifiedAt (v : Place F) : Prop :=
  ∀ x : LocalField F v, (∀ y : LocalField F v, ‖y‖ ≤ 1 →
    localChar s.character v (x * y) = 1) ↔ ‖x‖ ≤ 1

/-- The setting of §10.5: `S` good, `ψ_𝔭` unramified outside `S`, `𝒪_S` a PID. -/
structure ClassicalSetting (S : Finset (Place F)) : Prop where
  good : s.GoodOutside S
  unramified : ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S → s.UnramifiedAt (.inr p)
  principal : IsPrincipalIdealRing (SIntegers S)

end Setup

/-! ## The local and adelic data characterized by their defining properties -/

/-- Given the setup, the local Fourier transform `ℱ_v` on `𝒮_v`, the leading-term
maps `b_v` (§8), reference vectors equal to the basic vectors, and the adelic
maps `ℱ`, `b` and rational evaluation on `𝒮_𝔸 = ⊗' 𝒮_v`, each specified on pure
tensors (§9.2). Each field is uniquely determined by its specification. -/
structure Data {F : Type} [Field F] [NumberField F] {n : ℕ} (s : Setup F n) where
  fourier : ∀ v, s.schwartz v →ₗ[ℂ] s.schwartz v
  fourier_spec : ∀ v f, (fourier v f).val = s.integralTransform v f
  leading : ∀ v, s.schwartz v →ₗ[ℂ] Charts (LocalField F v)
  leading_spec : ∀ v (f : s.schwartz v), IsLeadingTerm n (modulus F v) f (leading v f)
  basic : ∀ v, s.schwartz v
  basic_spec : ∀ v, (basic v).val = s.basicVector v
  adelicFourier : restrictedTensor basic →ₗ[ℂ] restrictedTensor basic
  adelicFourier_spec : ∀ (f : ∀ v, s.schwartz v) (hf : ∀ᶠ v in cofinite, f v = basic v),
    (adelicFourier ⟨PiTensorProduct.tprod ℂ f, Submodule.subset_span ⟨f, hf, rfl⟩⟩).val =
      PiTensorProduct.tprod ℂ (fun v => fourier v (f v))
  adelicLeading : restrictedTensor basic →ₗ[ℂ]
    restrictedTensor (fun v => (leading v).rangeRestrict (basic v))
  adelicLeading_spec : ∀ (f : ∀ v, s.schwartz v) (hf : ∀ᶠ v in cofinite, f v = basic v),
    (adelicLeading ⟨PiTensorProduct.tprod ℂ f, Submodule.subset_span ⟨f, hf, rfl⟩⟩).val =
      PiTensorProduct.tprod ℂ (fun v => (leading v).rangeRestrict (f v))
  evaluation : restrictedTensor basic →ₗ[ℂ] (RationalPoint F → ℂ)
  evaluation_spec : ∀ (f : ∀ v, s.schwartz v) (hf : ∀ᶠ v in cofinite, f v = basic v) p,
    evaluation ⟨PiTensorProduct.tprod ℂ f, Submodule.subset_span ⟨f, hf, rfl⟩⟩ p =
      ∏ᶠ v, pointValue p v (f v)

variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n]

/-! ## Existence of the characterized objects -/

/-- Self-dual measures and Hilbert symbols exist for all the basic choices. -/
theorem exists_setup {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (ψ : AddChar (Adeles F) Circle) (hψ : Continuous ψ) (hnt : ∃ a, ψ a ≠ 1)
    (htriv : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) :
    ∃ μ : ∀ v, Measure (LocalField F v), ∃ H : SymbolFamily F n,
      (∀ v, IsSelfDual ψ v (μ v)) ∧ IsHilbertFamily F n H := by
  sorry

/-- Proposition 6.3(ii): at a finite place prime to `n`, the basic vector lies in
the Schwartz space. -/
theorem basicCharts_mem (s : Setup F n) (p : HeightOneSpectrum (𝓞 F))
    (hp : p.asIdeal.absNorm.Coprime n) : s.basicCharts p ∈ s.schwartz (.inr p) := by
  sorry

/-- The local transform preserves `𝒮_v`, leading terms exist, the basic vectors
are fixed by `ℱ_v` at almost all places, and rational evaluation is well defined
(by Hilbert reciprocity): all the data in `Data` exist. -/
theorem nonempty_data (s : Setup F n) : Nonempty (Data s) := by
  sorry

/-! ## Main results -/

/-- Theorem 7.1. At every place `v`: `ℱ` maps `𝒮_v` bijectively onto itself with
`ℱ² = h(ε)`, `ε = (-1)^(n+1)`; it commutes with the local cover; and it preserves
the `L²` norm (finite on `𝒮_v`). -/
theorem schwartz_inversion (s : Setup F n) (D : Data s) (v : Place F) :
    Function.Bijective (D.fourier v) ∧
    (∀ Φ, (D.fourier v (D.fourier v Φ)).val = s.torusCharts v ((-1) ^ (n+1)) Φ.val) ∧
    (∀ (g : s.cover v) Φ, D.fourier v (g.val Φ) = g.val (D.fourier v Φ)) ∧
    (∀ Φ : s.schwartz v, s.mass v Φ < ⊤ ∧ s.mass v (D.fourier v Φ) = s.mass v Φ) := by
  sorry

/-- Theorem 9.1 (Poisson formula). There is a unique linear functional `B` on the
restricted tensor product `b(𝒮_𝔸)` of the local spaces of leading terms such
that for every `Φ ∈ 𝒮_𝔸` the sums over `F² - {0}` converge absolutely and
`∑ Φ(v) + B(bΦ) = ∑ ℱΦ(v) + B(bℱΦ)`. -/
theorem poisson (s : Setup F n) (D : Data s) :
    ∃! B : restrictedTensor (fun v => (D.leading v).rangeRestrict (D.basic v)) →ₗ[ℂ] ℂ,
      ∀ Φ : restrictedTensor D.basic,
      Summable (fun v => ‖D.evaluation Φ v‖) ∧
      Summable (fun v => ‖D.evaluation (D.adelicFourier Φ) v‖) ∧
      (∑' v, D.evaluation Φ v) + B (D.adelicLeading Φ) =
        (∑' v, D.evaluation (D.adelicFourier Φ) v) +
          B (D.adelicLeading (D.adelicFourier Φ)) := by
  sorry

/-- Corollary 9.2. If `bΦ = 0` and `bℱΦ = 0`, then `∑ Φ(v) = ∑ ℱΦ(v)`. -/
theorem poisson_of_leading_eq_zero (s : Setup F n) (D : Data s)
    (Φ : restrictedTensor D.basic)
    (h : D.adelicLeading Φ = 0) (hF : D.adelicLeading (D.adelicFourier Φ) = 0) :
    (∑' v, D.evaluation Φ v) = ∑' v, D.evaluation (D.adelicFourier Φ) v := by
  sorry

open scoped ComplexConjugate in
/-- Theorem 10.34. Fix `b ∈ 𝒪_S - {0}`. There are constants `ρ(β)`, indexed by the
tuples of power classes at the places of `S`, such that for every twist `(T, χ, f)`
with `b` coprime to `f` and all `W_𝔭 ∈ C_c^∞(F_𝔭^×)`: `|ε| = 1`, both series converge
absolutely, and
`∑ W_S(c) χ(c) g̃(b,c) = ε ∑ (W_S {·,b}_S)^∨(c/(b f^{n-1})) conj(χ(c)) (c/f)_n (f/c)_n g̃(b,c)
  + M_b(W_S)`,
where `M_b(W_S) = ∑_β ρ(β) ∏_{𝔭 ∈ S} ∫_{β_𝔭} W_𝔭 |x|^{1/n} d^×x` if `T` is empty and
`M_b = 0` otherwise. (In the paper `ρ` is given by Theorem 10.16 for `ψ(b ·)`; here it
is asserted to exist, independently of `T`, `χ`, `f` and `W`.) -/
theorem twistedGaussSummation (s : Setup F n) {S : Finset (Place F)} (h : s.ClassicalSetting S)
    (b : NonzeroInteger S) :
    ∃ ρ : Classes n S → ℂ, ∀ (f : NonzeroInteger S) (T : Twist n S f),
      IsCoprime b.val f.val → ∀ W : Weights S, Admissible W →
      ‖s.epsilon T (fieldUnit b)‖ = 1 ∧
      Summable (fun c : NonzeroInteger S => ‖sWeight W (fieldUnit c) * twistValue T (fieldUnit c) *
        s.normalizedGauss S b.val c.val‖) ∧
      Summable (fun c : NonzeroInteger S =>
        ‖s.sDual (fun v x => W v x * s.symbol v.val x (atPlace _ (fieldUnit b)))
          (fieldUnit c / (fieldUnit b * fieldUnit f ^ (n-1))) *
        conj (twistValue T (fieldUnit c)) * s.residue S (fieldUnit c) (fieldUnit f) *
        s.residue S (fieldUnit f) (fieldUnit c) * s.normalizedGauss S b.val c.val‖) ∧
      (∑' c : NonzeroInteger S, sWeight W (fieldUnit c) * twistValue T (fieldUnit c) *
        s.normalizedGauss S b.val c.val) =
      s.epsilon T (fieldUnit b) * (∑' c : NonzeroInteger S,
        s.sDual (fun v x => W v x * s.symbol v.val x (atPlace _ (fieldUnit b)))
          (fieldUnit c / (fieldUnit b * fieldUnit f ^ (n-1))) *
        conj (twistValue T (fieldUnit c)) * s.residue S (fieldUnit c) (fieldUnit f) *
        s.residue S (fieldUnit f) (fieldUnit c) * s.normalizedGauss S b.val c.val) +
        (if T.primes.card = 0 then ∑ᶠ β, ρ β * s.moment W β else 0) := by
  sorry

/-- Corollary 10.40. Let `n` be odd, `S` contain the places above `2`, and
`h ∈ 𝒪_S` squarefree and not a unit. There is `ε` with `|ε| = 1` such that for all
`W_𝔭 ∈ C_c^∞(F_𝔭^×)`,
`∑ W_S(c) (c/h)_2 (c/h)_n² g̃(1,c) = ε ∑ W_S^∨(c/h^{n-1}) {h,c}_S (c/h)_2 g̃(1,c)`.
Here `(·/·)_2` is the quadratic residue symbol, taken from any setup `s₂` with `n = 2`
(only its Hilbert symbol enters). -/
theorem quadraticDual (s : Setup F n) (s₂ : Setup F 2) {S : Finset (Place F)}
    (hS : s.ClassicalSetting S) (odd : Odd n)
    (awayTwo : ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S → Odd p.asIdeal.absNorm)
    (h : NonzeroInteger S) (nonunit : ¬ IsUnit h.val) (squarefree : Squarefree h.val) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ W : Weights S, Admissible W →
      (∑' c : NonzeroInteger S, sWeight W (fieldUnit c) * s₂.residue S (fieldUnit c) (fieldUnit h) *
        s.residue S (fieldUnit c) (fieldUnit h) ^ 2 * s.normalizedGauss S 1 c.val) =
      ε * ∑' c : NonzeroInteger S, s.sDual W (fieldUnit c / fieldUnit h ^ (n-1)) *
        s.sSymbol S (fieldUnit h) (fieldUnit c) * s₂.residue S (fieldUnit c) (fieldUnit h) *
        s.normalizedGauss S 1 c.val := by
  sorry

/-- The case `n = 3` of Corollary 10.40: the twist on the left is the sextic residue
symbol `(c/h)_6`, for embeddings of `μ_3` and `μ_6` that agree on `μ_3`. -/
theorem sextic_to_quadratic (s : Setup F 3) (s₆ : Setup F 6) (s₂ : Setup F 2)
    (compatible : ∀ z : Mu F 3,
      s₆.embedding ⟨z.val, rootsOfUnity_le_of_dvd (⟨2, rfl⟩ : 3 ∣ 6) z.property⟩ = s.embedding z)
    {S : Finset (Place F)} (hS : s.ClassicalSetting S)
    (awayTwo : ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S → Odd p.asIdeal.absNorm)
    (h : NonzeroInteger S) (nonunit : ¬ IsUnit h.val) (squarefree : Squarefree h.val) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ W : Weights S, Admissible W →
      (∑' c : NonzeroInteger S, sWeight W (fieldUnit c) * s₆.residue S (fieldUnit c) (fieldUnit h) *
        s.normalizedGauss S 1 c.val) =
      ε * ∑' c : NonzeroInteger S, s.sDual W (fieldUnit c / fieldUnit h ^ 2) *
        s.sSymbol S (fieldUnit h) (fieldUnit c) * s₂.residue S (fieldUnit c) (fieldUnit h) *
        s.normalizedGauss S 1 c.val := by
  sorry

end NFoldCover
