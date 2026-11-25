import MetaplecticSummation.FiniteGerms
import MetaplecticSummation.FiniteInversion
import MetaplecticSummation.ArchimedeanInversion
import MetaplecticSummation.RootKernel
import MetaplecticSummation.PlancherelBounds

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain Filter MeasureTheory
open scoped Topology Matrix ENNReal
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (v : Place F)
def mass (Φ : d.schwartz v) : ℝ≥0∞ :=
  let dx := selfDual F d.character v
  ∫⁻ p, ‖xChart Φ p‖ₑ ^ 2 ∂(dx.prod dx)

/-- Ordinary Fourier inversion at frequency one for the chosen archimedean
character and its self-dual measure. -/
theorem hat_hat_arch_one (w : InfinitePlace F) (f : LocalField F (.inl w) → ℂ)
    (hf : Bruhat (.inl w) f) : d.hat (.inl w) (d.hat (.inl w) f) 1 = f (-1) :=
  congrFun (d.arch_hat_hat w f hf) 1

theorem schwartz_fourier_square (Φ : d.schwartz v) :
    (d.fourier v (d.fourier v Φ)).val = d.torusCharts v ((-1) ^ (n+1)) Φ.val := by
  cases v with
  | inl w => exact d.fourier_square_of_ordinary_inversion _ (d.hat_hat_arch_one w) Φ
  | inr p => exact d.finite_fourier_square p Φ

/-- Finiteness and invariance of the squared norm in Theorem 7.1. -/
theorem fourier_mass (Φ : d.schwartz v) :
    d.mass v Φ < ⊤ ∧ d.mass v (d.fourier v Φ) = d.mass v Φ := by sorry

/-- Theorem 7.1, in the chart model, with §5's lift of the diagonal matrix. -/
theorem schwartz_inversion :
    Function.Bijective (d.fourier v) ∧
    (∀ Φ, (d.fourier v (d.fourier v Φ)).val = d.torusCharts v ((-1) ^ (n+1)) Φ.val) ∧
    (∀ (g : d.cover v) Φ, d.fourier v (g.val Φ) = g.val (d.fourier v Φ)) ∧
    (∀ Φ, d.mass v Φ < ⊤ ∧ d.mass v (d.fourier v Φ) = d.mass v Φ) :=
  ⟨d.fourier_bijective_of_square v (d.schwartz_fourier_square v),
    d.schwartz_fourier_square v, d.fourier_equivariant v, d.fourier_mass v⟩

/-- Section 4's root kernel in the X chart. The deleted axis and the
zero-determinant line have measure zero and are assigned value zero. -/
def rootKernel (x' : (LocalField F v)ˣ) (y' : LocalField F v)
    (z : LocalField F v × LocalField F v) : ℂ := by
  classical
  let det := z.1 * y' - z.2 * x'
  exact if h : z.1 ≠ 0 ∧ det ≠ 0 then
    d.symbol v (Units.mk0 _ h.1) (-x') *
      ((modulus F v (n : LocalField F v) ^ (-(3/2 : ℝ)) : ℝ) : ℂ) *
      ∑ᶠ t : {t : LocalField F v // t^n = det},
        d.character.localValue F v t.val * ((modulus F v t.val : ℂ) ^ (1 - (n : ℤ)))
    else 0

theorem fourier_root_kernel (Φ : d.schwartz v) (x' : (LocalField F v)ˣ) (y' : LocalField F v) :
    let dx := selfDual F d.character v
    let integrand := fun z => xChart Φ z * d.rootKernel v x' y' z
    Integrable integrand (dx.prod dx) ∧
      (d.fourier v Φ).val.1 x' y' = ∫ z, integrand z ∂(dx.prod dx) := by
  intro dx integrand
  classical
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let : NullSingletonClass dx := d.selfDual_nullSingleton v
  obtain ⟨hG,heq⟩ := d.integralTransform_root_kernel v Φ x' y'
  have hnK : (n : LocalField F v) ≠ 0 := by
    have hnz := (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n:F) ≠ 0)
    simpa only [map_natCast,map_zero] using hnz
  have hmn : 0 < modulus F v (n : LocalField F v) := by
    cases v <;> simp [modulus,norm_pos_iff.mpr hnK,pow_pos]
  let c : ℂ := (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ * (modulus F v (n : LocalField F v) : ℂ)⁻¹
  have hc : ((modulus F v (n : LocalField F v) ^ (-(3/2:ℝ)) : ℝ) : ℂ) = c := by
    simp only [c]
    rw [Real.sqrt_eq_rpow,← Complex.ofReal_inv,← Complex.ofReal_inv,← Complex.ofReal_mul,
      ← Real.rpow_neg hmn.le,← Real.rpow_neg_one,← Real.rpow_add hmn]
    norm_num
  have hroots (a : LocalField F v) (f : LocalField F v → ℂ) :
      ∑ᶠ t : {t : LocalField F v // t^n = a}, f t.val = ∑ t ∈ Polynomial.nthRootsFinset n a, f t := by
    rw [finsum_subtype_eq_finsum_cond (fun t : LocalField F v => t^n = a) (f := f)]
    change ∑ᶠ t ∈ {t : LocalField F v | t^n = a}, f t = _
    rw [show {t : LocalField F v | t^n = a} = (↑(Polynomial.nthRootsFinset n a) : Set (LocalField F v)) by
      ext t; simp [Polynomial.mem_nthRootsFinset (NeZero.pos n)],finsum_mem_coe_finset]
  let D (z : LocalField F v × LocalField F v) := z.1*y' - z.2*x'.val
  have hnull : ∀ᵐ z ∂(dx.prod dx), D z ≠ 0 := by
    have hDc : Continuous D := by fun_prop
    have hs : MeasurableSet {z : LocalField F v × LocalField F v | D z ≠ 0} :=
      (isOpen_ne_fun hDc continuous_const).measurableSet
    refine (Measure.ae_prod_mem_iff_ae_ae_mem hs).mpr (.of_forall fun x => ?_)
    filter_upwards [(dx).ae_ne (x*y'/x'.val)] with y hy
    intro h
    apply hy
    change x*y' - y*x'.val = 0 at h
    field_simp
    linear_combination -h
  have hpt : ∀ᵐ z ∂(dx.prod dx), integrand z = c * (if hx : z.1 ≠ 0 then
      Φ.val.1 (Units.mk0 z.1 hx) z.2 * d.symbol v (Units.mk0 z.1 hx) (-x') *
        ∑ τ ∈ Polynomial.nthRootsFinset n (z.1*y' - z.2*x'.val),
          d.character.localValue F v τ * (modulus F v τ : ℂ)^(1-(n:ℤ)) else 0) := by
    filter_upwards [hnull] with z hz
    by_cases h1 : z.1 = 0
    · simp [integrand,xChart,h1]
    · have hz' : z.1*y' - z.2*x'.val ≠ 0 := hz
      simp only [integrand,xChart,rootKernel,ne_eq,h1,not_false_eq_true,dite_true,hz',and_self]
      rw [hroots _ (fun t => d.character.localValue F v t * (modulus F v t : ℂ)^(1-(n:ℤ))),hc]
      ring
  refine ⟨(hG.const_mul c).congr (hpt.mono fun z h => h.symm),?_⟩
  rw [d.fourier_apply,heq,integral_congr_ae hpt,integral_const_mul]

end MetaplecticPoisson.Datum
