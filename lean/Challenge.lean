import Mathlib

/-!
# Twisted sums of Gauss sums of order n: advertised statements

This file states, against Mathlib alone, two results of the paper
*A Schwartz space for the n-fold cover of SL₂* (P. D. Nelson), over a number field
`F` containing a primitive `n`th root of unity:

* `NFoldCover.twistedGaussSummation` — Theorem 10.33, a Voronoi-type summation
  formula for sums of Gauss sums of order `n` twisted by characters at finitely
  many primes;
* `NFoldCover.quadraticDual` — Corollary 10.39, under which the twist
  `(c/h)_2 (c/h)_n²` becomes the quadratic twist `(c/h)_2` in the dual sum.

The statements quantify over a nontrivial continuous character `ψ` of `𝔸/F`, the
Haar measures `μ v` on the completions that are self-dual for `ψ_v`, and any family
of local Hilbert symbols satisfying the axioms `IsHilbertFamily` (these determine
the family).  `NFoldCover.exists_selfDual_hilbert` shows that such data exist.

The weights on the dual side are given by the explicit integral of
Proposition 10.8 at `λ = 1` (formula (10.15)), not by the Schwartz space of the
paper, so the statements do not depend on §§3–9.
-/

noncomputable section

namespace NFoldCover

open NumberField IsDedekindDomain Filter MeasureTheory
open scoped Topology ContDiff ComplexConjugate

/-! ## Places, completions, characters, Hilbert symbols -/

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


/-- The complex-valued Hilbert symbol `{a, b}_v`, through an embedding `μ_n → ℂˣ`. -/
def hilbertSymbol {n : ℕ} (ε : Mu F n →* ℂˣ) (H : SymbolFamily F n) (v : Place F)
    (a b : (LocalField F v)ˣ) : ℂ :=
  ε (H v a b)

end Places

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

/-- The twisting data of Theorem 10.33: a finite set `T` of primes outside `S`,
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

/-! ## Local transforms, Gauss sums, the classical setting (§§9.3, 10.4, 10.6) -/

section Gauss
variable {F : Type} [Field F] [NumberField F] (n : ℕ)
  (ψ : AddChar (Adeles F) Circle) (μ : ∀ v, Measure (LocalField F v))
  (σ : ∀ v : Place F, (LocalField F v)ˣ → (LocalField F v)ˣ → ℂ)

/-- Proposition 10.8 at `λ = 1`, formula (10.15): for `W ∈ C_c^∞(F_v^×)`,
`W^∨(c) = |n|^{-1/2} ∫_{F_v} ψ(t) ∫_{F_v^×} W(x) {x, -c} ψ(-tⁿ/(cx)) d^×x dt`,
with `dt` self-dual for `ψ_v` and `d^×x = dx/|x|_v`. -/
def dualWeight (v : Place F) (W : Weight v) (c : (LocalField F v)ˣ) : ℂ :=
  (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ *
    ∫ t, localChar ψ v t *
      (by classical exact ∫ x, if h : x ≠ 0 then
        (W (Units.mk0 x h) * σ v (Units.mk0 x h) (-c) *
          localChar ψ v (-(t ^ n) / ((c : LocalField F v) * x))) /
          (modulus F v x : ℂ) else 0 ∂(μ v)) ∂(μ v)

/-- `∏_{𝔭 ∈ S} ∫_{β_𝔭} W_𝔭(x) |x|_𝔭^{1/n} d^×x`. -/
def moment {S : Finset (Place F)} (W : Weights S) (β : Classes n S) : ℂ := by
  classical
  exact ∏ v : S, ∫ x, if h : x ≠ 0 then
    (if QuotientGroup.mk (Units.mk0 x h) = β v then
      W v (Units.mk0 x h) * ((modulus F v.val x ^ (1 / (n : ℝ)) : ℝ) : ℂ) else 0) /
      (modulus F v.val x : ℂ) else 0 ∂(μ v.val)

/-- `W_S^∨(c) = ∏_{v ∈ S} W_v^∨(c)`. -/
def sDual {S : Finset (Place F)} (W : Weights S) (c : Fˣ) :=
  ∏ v : S, dualWeight n ψ μ σ v.val (W v) (atPlace v.val c)

/-- `ψ_S(x) = ∏_{v ∈ S} ψ_v(x)`. -/
def sPsi (S : Finset (Place F)) (x : F) := ∏ v ∈ S, localChar ψ v (diagonal F v x)

/-- `{a, b}_S = ∏_{v ∈ S} {a, b}_v`. -/
def sSymbol (S : Finset (Place F)) (a b : Fˣ) := ∏ v ∈ S, σ v (atPlace v a) (atPlace v b)

/-- Definition 9.3: the power residue symbol `(a/c) = ∏_{𝔭 | c, 𝔭 ∉ S} {c, a}_𝔭`
if `a` is a unit at every such `𝔭`, and `0` otherwise. -/
def residue (S : Finset (Place F)) (a c : F) : ℂ := by
  classical
  exact ∏ᶠ p : HeightOneSpectrum (𝓞 F), if Sum.inr p ∉ S ∧ ‖diagonal F (.inr p) c‖ < 1 then
    if h : a ≠ 0 ∧ c ≠ 0 ∧ ‖diagonal F (.inr p) a‖ = 1 then
      σ (.inr p) (atPlace _ (Units.mk0 c h.2.1)) (atPlace _ (Units.mk0 a h.1))
    else 0 else 1

/-- Definition 10.30: `g(b, c) = ∑_{d ∈ (𝒪_S/c)^×} (d/c)_n ψ_S(bd/c)`, evaluated on
representatives (the summand does not depend on the choice). -/
def gauss (S : Finset (Place F)) (b c : SIntegers S) : ℂ :=
  ∑ᶠ u : (SIntegers S ⧸ Ideal.span {c})ˣ,
    let a : SIntegers S := Quotient.out (u : SIntegers S ⧸ Ideal.span {c})
    residue σ S a c * sPsi ψ S ((b : F) * a / c)

/-- The summand `|τ|_S^{n-1} g(b, c/τⁿ)` if `τⁿ | c`, and `0` otherwise. -/
def powerDivisorTerm (S : Finset (Place F)) (b c t : SIntegers S) : ℂ := by
  classical exact if h : t ^ n ∣ c then
    (sNorm S t : ℂ) ^ (n-1) * gauss ψ σ S b h.choose else 0

/-- Definition 10.30: `g̃(b, c) = |c|_S^{-1} ∑_{τ ∈ 𝒪_S/𝒪_S^×, τⁿ | c} |τ|_S^{n-1} g(b, c/τⁿ)`. -/
def normalizedGauss (S : Finset (Place F)) (b c : SIntegers S) : ℂ :=
  (sNorm S c : ℂ)⁻¹ * ∑ᶠ t : Associates (SIntegers S), powerDivisorTerm n ψ σ S b c (Quotient.out t)

/-- (10.21): `ε = ∏_{𝔭 ∈ T} (1_{𝔬_𝔭^×} χ_𝔭)^∨((b f^{n-1})^{-1})`. -/
def epsilon {S : Finset (Place F)} {f : NonzeroInteger S} (T : Twist n S f) (b : Fˣ) :=
  ∏ p : T.primes, dualWeight n ψ μ σ (.inr p.val) (charWeight (T.character p))
    (atPlace _ (b * fieldUnit f ^ (n-1))⁻¹)

/-- §9.1 and §10.6: `S` is nonempty and contains the archimedean places; every
`𝔭 ∉ S` is prime to `n`, `ψ_𝔭` is unramified (`𝔬_𝔭` is the largest fractional
ideal on which it is trivial), and `𝒪_S` is a principal ideal domain. -/
structure ClassicalSetting (S : Finset (Place F)) : Prop where
  nonempty : S.Nonempty
  infinite : ∀ w, Sum.inl w ∈ S
  coprime : ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S → p.asIdeal.absNorm.Coprime n
  unramified : ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S → ∀ x : LocalField F (.inr p),
    (∀ y : LocalField F (.inr p), ‖y‖ ≤ 1 → localChar ψ (.inr p) (x * y) = 1) ↔ ‖x‖ ≤ 1
  principal : IsPrincipalIdealRing (SIntegers S)

end Gauss

/-! ## Statements -/

variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n]

/-- The data quantified over below exist: self-dual measures for every nontrivial
continuous character of `𝔸/F`, and Hilbert symbols whenever `μ_n ⊂ F`. -/
theorem exists_selfDual_hilbert {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (ψ : AddChar (Adeles F) Circle) (hψ : Continuous ψ) (hnt : ∃ a, ψ a ≠ 1)
    (htriv : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) :
    ∃ μ : ∀ v, Measure (LocalField F v), ∃ H : SymbolFamily F n,
      (∀ v, IsSelfDual ψ v (μ v)) ∧ IsHilbertFamily F n H := by
  sorry

/-- Theorem 10.33. Let `F ⊇ μ_n` be a number field, `ψ` a nontrivial continuous
character of `𝔸/F`, `μ v` the self-dual measures, `H` the Hilbert symbols (with an
embedding `ε : μ_n → ℂˣ`), and `S` as in §10.6. Fix `b ∈ 𝒪_S - {0}`. There are
constants `ρ(β)`, indexed by the tuples of power classes at the places of `S`, such
that for every twist `(T, χ, f)` with `b` coprime to `f` and all
`W_𝔭 ∈ C_c^∞(F_𝔭^×)`: `|ε| = 1`, both series converge absolutely, and
`∑ W_S(c) χ(c) g̃(b,c) = ε ∑ (W_S {·,b}_S)^∨(c/(b f^{n-1})) conj(χ(c)) (c/f)_n (f/c)_n g̃(b,c)
  + M_b(W_S)`,
with `M_b(W_S) = ∑_β ρ(β) ∏_{𝔭 ∈ S} ∫_{β_𝔭} W_𝔭 |x|^{1/n} d^×x` if `T` is empty and
`M_b = 0` otherwise. (In the paper `ρ` is given by Theorem 10.16 for `ψ(b ·)`; here
it is asserted to exist, independently of `T`, `χ`, `f` and `W`.) -/
theorem twistedGaussSummation {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (ε : Mu F n →* ℂˣ) (hε : Function.Injective ε)
    (ψ : AddChar (Adeles F) Circle) (hψ : Continuous ψ) (hnt : ∃ a, ψ a ≠ 1)
    (htriv : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (μ : ∀ v, Measure (LocalField F v)) (hμ : ∀ v, IsSelfDual ψ v (μ v))
    (H : SymbolFamily F n) (hH : IsHilbertFamily F n H)
    {S : Finset (Place F)} (hS : ClassicalSetting n ψ S) (b : NonzeroInteger S) :
    let σ := hilbertSymbol F ε H
    ∃ ρ : Classes n S → ℂ, ∀ (f : NonzeroInteger S) (T : Twist n S f),
      IsCoprime b.val f.val → ∀ W : Weights S, Admissible W →
      ‖epsilon n ψ μ σ T (fieldUnit b)‖ = 1 ∧
      Summable (fun c : NonzeroInteger S => ‖sWeight W (fieldUnit c) * twistValue T (fieldUnit c) *
        normalizedGauss n ψ σ S b.val c.val‖) ∧
      Summable (fun c : NonzeroInteger S =>
        ‖sDual n ψ μ σ (fun v x => W v x * σ v.val x (atPlace _ (fieldUnit b)))
          (fieldUnit c / (fieldUnit b * fieldUnit f ^ (n-1))) *
        conj (twistValue T (fieldUnit c)) * residue σ S (fieldUnit c) (fieldUnit f) *
        residue σ S (fieldUnit f) (fieldUnit c) * normalizedGauss n ψ σ S b.val c.val‖) ∧
      (∑' c : NonzeroInteger S, sWeight W (fieldUnit c) * twistValue T (fieldUnit c) *
        normalizedGauss n ψ σ S b.val c.val) =
      epsilon n ψ μ σ T (fieldUnit b) * (∑' c : NonzeroInteger S,
        sDual n ψ μ σ (fun v x => W v x * σ v.val x (atPlace _ (fieldUnit b)))
          (fieldUnit c / (fieldUnit b * fieldUnit f ^ (n-1))) *
        conj (twistValue T (fieldUnit c)) * residue σ S (fieldUnit c) (fieldUnit f) *
        residue σ S (fieldUnit f) (fieldUnit c) * normalizedGauss n ψ σ S b.val c.val) +
        (if T.primes.card = 0 then ∑ᶠ β, ρ β * moment n μ W β else 0) := by
  sorry

/-- Corollary 10.39. In the setting of Theorem 10.33, let `n` be odd, let every
`𝔭 ∉ S` have odd residue characteristic, and let `h ∈ 𝒪_S` be squarefree and not a
unit. There is `ε'` with `|ε'| = 1` such that for all `W_𝔭 ∈ C_c^∞(F_𝔭^×)`,
`∑ W_S(c) (c/h)_2 (c/h)_n² g̃(1,c) = ε' ∑ W_S^∨(c/h^{n-1}) {h,c}_S (c/h)_2 g̃(1,c)`.
The quadratic symbol `(·/·)_2` is formed from quadratic Hilbert symbols `H₂`. -/
theorem quadraticDual {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (ε : Mu F n →* ℂˣ) (hε : Function.Injective ε)
    (ψ : AddChar (Adeles F) Circle) (hψ : Continuous ψ) (hnt : ∃ a, ψ a ≠ 1)
    (htriv : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (μ : ∀ v, Measure (LocalField F v)) (hμ : ∀ v, IsSelfDual ψ v (μ v))
    (H : SymbolFamily F n) (hH : IsHilbertFamily F n H)
    (ε₂ : Mu F 2 →* ℂˣ) (hε₂ : Function.Injective ε₂)
    (H₂ : SymbolFamily F 2) (hH₂ : IsHilbertFamily F 2 H₂)
    {S : Finset (Place F)} (hS : ClassicalSetting n ψ S) (odd : Odd n)
    (awayTwo : ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S → Odd p.asIdeal.absNorm)
    (h : NonzeroInteger S) (nonunit : ¬ IsUnit h.val) (squarefree : Squarefree h.val) :
    let σ := hilbertSymbol F ε H
    let σ₂ := hilbertSymbol F ε₂ H₂
    ∃ ε' : ℂ, ‖ε'‖ = 1 ∧ ∀ W : Weights S, Admissible W →
      (∑' c : NonzeroInteger S, sWeight W (fieldUnit c) * residue σ₂ S (fieldUnit c) (fieldUnit h) *
        residue σ S (fieldUnit c) (fieldUnit h) ^ 2 * normalizedGauss n ψ σ S 1 c.val) =
      ε' * ∑' c : NonzeroInteger S, sDual n ψ μ σ W (fieldUnit c / fieldUnit h ^ (n-1)) *
        sSymbol σ S (fieldUnit h) (fieldUnit c) * residue σ₂ S (fieldUnit c) (fieldUnit h) *
        normalizedGauss n ψ σ S 1 c.val := by
  sorry

end NFoldCover
