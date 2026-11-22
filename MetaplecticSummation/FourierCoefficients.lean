import MetaplecticSummation.Jacquet
import MetaplecticSummation.AdeleLattice
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Filter
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

def marginal (v : Place F) (Φ : d.schwartz v) (c : (LocalField F v)ˣ) :=
  ∫ y, Φ.val.1 c y ∂(selfDual F d.character v)

def axis (v : Place F) (Φ : d.schwartz v) (y : (LocalField F v)ˣ) := Φ.val.2 0 y

def Bruhat (v : Place F) (g : LocalField F v → ℂ) : Prop := by
  classical
  cases v with
  | inr p => exact IsLocallyConstant g ∧ HasCompactSupport g
  | inl w =>
    by_cases h : w.IsReal
    · exact ∃ f : SchwartzMap ℝ ℂ, ∀ x, g x = f (InfinitePlace.Completion.ringEquivRealOfIsReal h x)
    · exact ∃ f : SchwartzMap ℂ ℂ, ∀ x, g x = f (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp h) x)

def hat (v : Place F) (g : LocalField F v → ℂ) (u : LocalField F v) :=
  ∫ t, g t * d.character.localValue F v (u*t) ∂(selfDual F d.character v)

/-- The two marginal identities of Appendix A, on the full Schwartz space. -/
theorem marginal_fourier (v : Place F) (Φ : d.schwartz v) (x y : (LocalField F v)ˣ) :
    let N : ℂ := modulus F v (n : LocalField F v)
    let k : ℂ := (Real.sqrt (modulus F v (n : LocalField F v)))⁻¹
    ∃ ν σ : LocalField F v → ℂ, Bruhat v ν ∧ Bruhat v σ ∧
      (∀ u : (LocalField F v)ˣ,
        ν u = d.symbol v (-1) y / (modulus F v y : ℂ) * d.marginal v Φ (u^n/y) ∧
        σ u = N / (modulus F v x : ℂ) * (modulus F v u : ℂ)^(n-1) * d.axis v Φ (-(u^n)/x)) ∧
      (∀ u : (LocalField F v)ˣ,
        d.axis v (d.fourier v Φ) (u^n*y) = k * (modulus F v u : ℂ)^(1-(n : ℤ)) * d.hat v ν u ∧
        d.marginal v (d.fourier v Φ) (u^n*x) = k * d.hat v σ u) := by sorry

abbrev AdeleQuotient (F : Type) [Field F] [NumberField F] :=
  AdeleLattice.Quotient F

local instance : MeasurableSpace (AdeleQuotient F) := borel _
local instance : BorelSpace (AdeleQuotient F) := ⟨rfl⟩

theorem exists_quotient_measure :
    ∃! μ : Measure (AdeleQuotient F), μ.IsAddHaarMeasure ∧ IsProbabilityMeasure μ := by
  let C : TopologicalSpace.PositiveCompacts (AdeleQuotient F) := ⊤
  let μ := Measure.addHaarMeasure C
  letI : IsProbabilityMeasure μ := ⟨Measure.addHaarMeasure_self (K₀ := C)⟩
  refine ⟨μ,⟨inferInstance,inferInstance⟩,?_⟩
  rintro ν ⟨hH,hP⟩
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure ν μ

/-- The theta series at an upper unipotent translate, written in the common rational chart. -/
def translatedTheta (Φ : ∀ v, d.schwartz v) (u : Adeles F) : ℂ :=
  ∑' p : RationalPoint F, ∏ᶠ v,
    let z := diagonalPoint p v
    if p.val.1 ≠ 0 then xChart (Φ v) (z.1, z.2 + component u v * z.1) else yChart (Φ v) z

private def rationalShear (t : F) (p : RationalPoint F) : RationalPoint F :=
  ⟨(p.val.1,p.val.2+t*p.val.1),fun h => p.property (by
    have h₁ : p.val.1 = 0 := congrArg Prod.fst h
    exact Prod.ext h₁ (by simpa [h₁] using congrArg Prod.snd h))⟩

private def rationalShearEquiv (t : F) : RationalPoint F ≃ RationalPoint F where
  toFun := rationalShear t
  invFun := rationalShear (-t)
  left_inv p := by apply Subtype.ext; ext <;> simp [rationalShear]
  right_inv p := by apply Subtype.ext; ext <;> simp [rationalShear]

/-- Translating the unipotent parameter by a principal adele permutes the rational points. -/
theorem translatedTheta_add_diagonal (Φ : ∀ v, d.schwartz v) (u : Adeles F) (t : F) :
    d.translatedTheta Φ (u + algebraMap F (Adeles F) t) = d.translatedTheta Φ u := by
  let term (p : RationalPoint F) (u : Adeles F) (v : Place F) :=
    let z := diagonalPoint p v
    if p.val.1 ≠ 0 then xChart (Φ v) (z.1,z.2 + component u v*z.1) else yChart (Φ v) z
  change (∑' p, ∏ᶠ v, term p (u + algebraMap F (Adeles F) t) v) = ∑' p, ∏ᶠ v, term p u v
  rw [← (rationalShearEquiv t).tsum_eq (fun p => ∏ᶠ v, term p u v)]
  apply tsum_congr
  intro p
  apply finprod_congr
  intro v
  have hc : component (u + algebraMap F (Adeles F) t) v = component u v + diagonal F v t := by
    cases v <;> rfl
  by_cases hp : p.val.1 = 0
  · simp [term,rationalShearEquiv,rationalShear,diagonalPoint,hp]
  · simp only [term,rationalShearEquiv,rationalShear,Equiv.coe_fn_mk,diagonalPoint,hp,ne_eq,not_false_eq_true,
      if_true,hc,map_add,map_mul,add_mul]
    congr 2
    ring

/-- The integrand of the Fourier coefficient has the same value at every
representative of a class modulo the diagonal field. -/
def quotientIntegrand (Φ : ∀ v, d.schwartz v) (a : F) : AdeleQuotient F → ℂ :=
  Quotient.lift (fun u : Adeles F => d.translatedTheta Φ u * (d.character.toChar (-(algebraMap F (Adeles F) a * u)) : ℂ))
    (by
      intro u w h
      have he : (-u + w) ∈ AdeleRing.principalSubgroup (𝓞 F) F := QuotientAddGroup.leftRel_apply.mp h
      obtain ⟨t,ht⟩ := he
      have hw : w = u + algebraMap F (Adeles F) t := by rw [ht]; abel
      rw [hw,d.translatedTheta_add_diagonal, mul_add,neg_add,← map_mul,← map_neg,AddChar.map_add_eq_mul,
        d.character.trivial_diagonal,mul_one])

@[simp] theorem quotientIntegrand_mk (Φ : ∀ v, d.schwartz v) (a : F) (u : Adeles F) :
    d.quotientIntegrand Φ a (QuotientAddGroup.mk u) =
      d.translatedTheta Φ u * (d.character.toChar (-(algebraMap F (Adeles F) a * u)) : ℂ) := rfl

def coefficient (Φ : ∀ v, d.schwartz v) (a : F) : ℂ :=
  ∫ q : AdeleQuotient F, d.quotientIntegrand Φ a q
    ∂(exists_quotient_measure (F := F)).exists.choose

def constantTerm (Φ : ∀ v, d.schwartz v) :=
  (∑' y : Fˣ, ∏ᶠ v, d.axis v (Φ v) (atPlace v y)) +
    ∑' x : Fˣ, ∏ᶠ v, d.marginal v (Φ v) (atPlace v x)

theorem unfolding (Φ : ∀ v, d.schwartz v) (h : ∀ᶠ v in cofinite, Φ v = d.basic v) :
    d.coefficient Φ 0 = d.constantTerm Φ ∧
    Summable (fun c : Fˣ => ‖∏ᶠ v, d.jacquet v (Φ v) (atPlace v c)‖) ∧
    d.coefficient Φ 1 = ∑' c : Fˣ, ∏ᶠ v, d.jacquet v (Φ v) (atPlace v c) := by sorry

abbrev GlobalClass (n : ℕ) (F : Type) [Field F] := Fˣ ⧸ (powMonoidHom n : Fˣ →* Fˣ).range

/-- Appendix B's Poisson formula on multiplicative power classes. -/
theorem powerClass_poisson (β : (v : Place F) → PowerClass n v → ℂ)
    (hβ : ∀ᶠ p : HeightOneSpectrum (𝓞 F) in cofinite, ∀ c, β (.inr p) c =
      if ∃ u : (LocalField F (.inr p))ˣ, ‖(u : LocalField F (.inr p))‖ = 1 ∧
        QuotientGroup.mk u = c then 1 else 0) :
    let eval := fun (v : Place F) (x : GlobalClass n F) =>
      (QuotientGroup.mk (atPlace v x.out) : PowerClass n v)
    let dual := fun (v : Place F) (y : PowerClass n v) =>
      (n : ℂ)⁻¹ * ∑ᶠ c : PowerClass n v, d.symbol v c.out y.out * β v c
    (∑' x : GlobalClass n F, ∏ᶠ v, β v (eval v x)) =
      ∑' y : GlobalClass n F, ∏ᶠ v, dual v (eval v y) := by sorry

def axisBoundary (Φ : ∀ v, d.schwartz v) :=
  (n : ℂ)⁻¹ * ∑ᶠ y : GlobalClass n F, ∏ᶠ v,
    (d.leading v (Φ v)).2 0 (atPlace v y.out)

theorem constantTerm_identity (Φ : ∀ v, d.schwartz v) (h : ∀ᶠ v in cofinite, Φ v = d.basic v) :
    let dual := fun v => d.fourier v (Φ v)
    d.constantTerm Φ + d.axisBoundary Φ = d.constantTerm dual + d.axisBoundary dual := by sorry

end MetaplecticPoisson.Datum
