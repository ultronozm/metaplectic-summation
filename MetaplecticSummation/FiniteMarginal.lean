import MetaplecticSummation.MarginalRootFormula
import MetaplecticSummation.TorusCharts
import MetaplecticSummation.PowerArea
import Mathlib.Topology.Algebra.IsOpenUnits

/-! The reverse marginal Fourier identity for finite-place test sections. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Set Filter Polynomial
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

private theorem axis_locallyConstant_on_test (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (hΦ : Φ.val ∈ d.testSet (.inr p)) :
    IsLocallyConstant (fun y => yChart Φ.val (0,y)) := by
  let K := LocalField F (.inr p)
  have ht : finiteTest Φ.val := hΦ.2
  obtain ⟨C,hC,h₀,hout⟩ := ht.2.2
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro y
  by_cases hy : y = 0
  · subst y
    have hm : Cᶜ ∈ 𝓝 ((0,0) : K × K) := hC.isClosed.isOpen_compl.mem_nhds h₀
    filter_upwards [((continuous_const (y := (0 : K))).prodMk continuous_id).continuousAt.eventually hm] with z hz
    exact (hout _ hz).2.trans (hout _ h₀).2.symm
  · let u := Units.mk0 y hy
    change ∀ᶠ z in 𝓝 u.val, yChart Φ.val (0,z) = yChart Φ.val (0,u.val)
    rw [← (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).map_nhds_eq u,eventually_map]
    have hl := ht.2.1.comp_continuous ((continuous_const (y := (0 : K))).prodMk (continuous_id (X := Kˣ)))
    filter_upwards [hl.eventually_eq u] with z hz
    change Φ.val.2 0 z = Φ.val.2 0 u at hz
    simpa only [yChart,dif_pos z.ne_zero,dif_pos u.ne_zero,Units.mk0_val] using hz

/-- Appendix A, the reverse marginal identity on test sections. The transform
on the left is the defining integral. At a wild place the input still needed
here is the radical of the Hilbert pairing. -/
theorem finite_reverse_marginal_with_density (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (hΦ : Φ.val ∈ d.testSet (.inr p)) (s μ : (LocalField F (.inr p))ˣ)
    (σ : LocalField F (.inr p) → ℂ)
    (hσ : ∀ t : (LocalField F (.inr p))ˣ, σ t.val =
      (modulus F (.inr p) (n : LocalField F (.inr p)) : ℂ) / (modulus F (.inr p) s.val : ℂ) *
        (modulus F (.inr p) t.val : ℂ)^(n-1) * d.axis (.inr p) Φ (-(t^n)/s))
    (hpow : ∀ a : (LocalField F (.inr p))ˣ, (∀ u, d.symbol (.inr p) u a = 1) → ∃ b, b^n = a) :
    let v : Place F := .inr p
    d.marginal v (d.transformTest v Φ hΦ) (μ^n*s) =
      (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ * d.hat v σ μ.val := by
  let v : Place F := .inr p
  let K := LocalField F v
  let dx := selfDual F d.character v
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)
  letI : NullSingletonClass dx := d.selfDual_nullSingleton v
  let ψ := d.character.localValue F v
  let A (y : K) := yChart Φ.val (0,y)
  have hA (y : Kˣ) : A y.val = d.axis v Φ y := by simp [A,yChart,axis,y.ne_zero]
  have hA₀ : A 0 = 0 := by simp [A,yChart]
  let g (t : K) := A (-(t^n)/s.val) * ψ (μ.val*t)
  have hg : IsLocallyConstant g :=
    ((d.axis_locallyConstant_on_test p Φ hΦ).comp_continuous (by fun_prop : Continuous (fun t : K => -(t^n)/s.val))).mul
      ((d.character.locallyConstant_finiteValue p).comp_continuous (continuous_const.mul continuous_id))
  have hg₀ : g 0 = 0 := by simp [g,zero_pow (NeZero.ne n),hA₀]
  obtain ⟨B,hB⟩ := d.axis_roots_bounded p Φ hΦ s
  have hgC : HasCompactSupport g := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : K) B)
    intro t ht
    by_cases h : t = 0
    · exact h ▸ hg₀
    let a := Units.mk0 t h
    let y := -(a^n)/s
    have hv : y.val = -(t^n)/s.val := by simp [y,a]
    have hy : -(s.val*y.val) = t^n := by rw [hv]; field_simp
    have hz : d.axis v Φ y = 0 := by
      by_contra hne
      exact ht (mem_closedBall_zero_iff.mpr (hB y hne t ((mem_nthRootsFinset (NeZero.pos n) _).mpr hy.symm)))
    simp [g,← hv,hA,hz]
  let H (y : K) := ∑ a ∈ nthRootsFinset n y, g a
  have hsum (y : K) : H (-(s.val*y)) = A y * ∑ a ∈ nthRootsFinset n (-(s.val*y)), ψ (μ.val*a) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a ha => by
      have he := (mem_nthRootsFinset (NeZero.pos n) _).mp ha
      have e : -(a^n)/s.val = y := by rw [he,neg_neg]; exact (div_eq_iff s.ne_zero).mpr (mul_comm ..)
      simp only [g,e]
  have hroot := d.finite_marginal_root_formula_on_test p Φ hΦ s μ hpow
  dsimp only at hroot ⊢
  let c : ℂ := Real.sqrt (modulus F v (n : K))
  have hn : (n : K) ≠ 0 := by
    have h := (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n : F) ≠ 0)
    simpa only [map_natCast,map_zero] using h
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos (norm_pos_iff.mpr hn)).ne'
  apply (eq_inv_mul_iff_mul_eq₀ hc).mpr
  apply hroot.trans
  calc
    _ = ∫ y, H ((-s).val*y) ∂dx := by
      apply integral_congr_ae
      filter_upwards [dx.ae_ne 0] with y hy
      change y ≠ 0 at hy
      rw [Units.val_neg,neg_mul,hsum,dif_pos hy]
      exact congrArg (· * _) (hA (Units.mk0 y hy)).symm
    _ = (∫ z, H z ∂dx) / (‖s.val‖ : ℂ) := by
      simpa only [v,modulus,Units.val_neg,norm_neg] using d.integral_local_mul v (-s) H
    _ = d.hat v σ μ.val := by
      change (∫ z, ∑ t ∈ nthRootsFinset n z, g t ∂dx) / _ = _
      rw [d.finite_power_area p hg hgC hg₀,div_eq_mul_inv,← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [dx.ae_ne 0] with t ht
      let a := Units.mk0 t ht
      change (‖(n : K)*a.val^(n-1)‖ : ℂ) * g a.val * _ = σ a.val * ψ (μ.val*a.val)
      rw [hσ]
      have hv : (-(a^n)/s).val = -(a.val^n)/s.val := by simp
      unfold g
      rw [← hv,hA]
      simp only [v,modulus,norm_mul,norm_pow,Complex.ofReal_mul,Complex.ofReal_pow,div_eq_mul_inv]
      ring

theorem finite_reverse_marginal_on_test (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (hΦ : Φ.val ∈ d.testSet (.inr p)) (s μ : (LocalField F (.inr p))ˣ)
    (hpow : ∀ a : (LocalField F (.inr p))ˣ, (∀ u, d.symbol (.inr p) u a = 1) → ∃ b, b^n = a) :
    let v : Place F := .inr p
    d.marginal v (d.transformTest v Φ hΦ) (μ^n*s) =
      (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ * d.hat v (d.axisDensity v Φ s) μ.val :=
  d.finite_reverse_marginal_with_density p Φ hΦ s μ _ (d.axisDensity_unit _ Φ s) hpow

/-- The reverse marginal Fourier formula on test sections at every tame place. -/
theorem tame_reverse_marginal_on_test (p : HeightOneSpectrum (𝓞 F)) (hp : p.asIdeal.absNorm.Coprime n)
    (Φ : d.schwartz (.inr p)) (hΦ : Φ.val ∈ d.testSet (.inr p)) (s μ : (LocalField F (.inr p))ˣ) :
    let v : Place F := .inr p
    d.marginal v (d.transformTest v Φ hΦ) (μ^n*s) =
      (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ * d.hat v (d.axisDensity v Φ s) μ.val :=
  d.finite_reverse_marginal_on_test p Φ hΦ s μ (fun a => (d.tame_symbol_radical p hp a).mp)

/-- A Schwartz–Bruhat extension of the axis density at a finite place, constructed
from the power-ray extension of the section. -/
theorem exists_finite_axis_density (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (s : (LocalField F (.inr p))ˣ) :
    let v : Place F := .inr p
    ∃ σ : LocalField F v → ℂ, Bruhat v σ ∧ ∀ t : (LocalField F v)ˣ, σ t.val =
      (modulus F v (n : LocalField F v) : ℂ) / (modulus F v s.val : ℂ) *
        (modulus F v t.val : ℂ)^(n-1) * d.axis v Φ (-(t^n)/s) := by
  let v : Place F := .inr p
  let K := LocalField F v
  let q : K × Kˣ := (0,-1/s)
  let c : ℂ := (modulus F v (n : K) : ℂ) / (modulus F v s.val : ℂ)
  obtain ⟨E,hE,he⟩ := (d.finite_schwartz_rayExtensions p Φ).2
  let σ (t : K) := c * E q t
  have hb : IsLocallyConstant (E q) ∧ HasCompactSupport (E q) := bruhat_finite_slice hE q
  have hσ : Bruhat v σ := ⟨hb.1.comp (c * ·),hb.2.mul_left (f := fun _ => c)⟩
  have hu (t : Kˣ) : σ t.val = c * (modulus F v t.val : ℂ)^(n-1) * d.axis v Φ (-(t^n)/s) := by
    have h : E q t.val = (modulus F v t.val : ℂ)^(n-1) * d.axis v Φ (-(t^n)/s) := by
      simpa only [q,mul_zero,mul_div_assoc',mul_neg_one,axis,modulus] using he q t
    rw [mul_assoc,← h]
  exact ⟨σ,hσ,hu⟩

/-- The square of the defining integral transform on the vertical axis,
for finite-place test sections under Hilbert nondegeneracy. -/
theorem finite_integralTransform_square_axis (p : HeightOneSpectrum (𝓞 F))
    (hpow : ∀ a : (LocalField F (.inr p))ˣ, (∀ u, d.symbol (.inr p) u a = 1) → ∃ b, b^n = a)
    (Φ : d.schwartz (.inr p)) (hΦ : Φ.val ∈ d.testSet (.inr p)) (y : (LocalField F (.inr p))ˣ) :
    let v : Place F := .inr p
    let e : (LocalField F v)ˣ := (-1)^(n+1)
    (d.integralTransform v (d.integralTransform v Φ.val)).2 0 y =
      d.symbol v e y * d.axis v Φ (y/e) := by
  let v : Place F := .inr p
  let s := y⁻¹
  obtain ⟨σ,hσ,hu⟩ := d.exists_finite_axis_density p Φ s
  exact d.integralTransform_axis_of_marginal v Φ (d.transformTest _ Φ hΦ) y σ (hu (-1))
    (fun μ => d.finite_reverse_marginal_with_density p Φ hΦ s μ σ hu hpow)
    (d.hat_hat_finite p hσ 1)

/-- Appendix A inversion on test sections at a finite place whose Hilbert pairing
has radical equal to the subgroup of n-th powers. -/
theorem finite_integralTransform_square_on_test (p : HeightOneSpectrum (𝓞 F))
    (hpow : ∀ a : (LocalField F (.inr p))ˣ, (∀ u, d.symbol (.inr p) u a = 1) → ∃ b, b^n = a)
    {f : Charts (LocalField F (.inr p))} (hf : f ∈ d.testSet (.inr p)) :
    let v : Place F := .inr p
    d.integralTransform v (d.integralTransform v f) = d.torusCharts v ((-1)^(n+1)) f := by
  let v : Place F := .inr p
  exact d.integralTransform_square_of_test_axis v (d.finite_integralTransform_square_axis p hpow) hf

/-- At a tame place the defining double integral equals the diagonal lift
on the entire test section. -/
theorem tame_integralTransform_square_on_test (p : HeightOneSpectrum (𝓞 F))
    (hp : p.asIdeal.absNorm.Coprime n) {f : Charts (LocalField F (.inr p))} (hf : f ∈ d.testSet (.inr p)) :
    let v : Place F := .inr p
    d.integralTransform v (d.integralTransform v f) = d.torusCharts v ((-1)^(n+1)) f :=
  d.finite_integralTransform_square_on_test p (fun a => (d.tame_symbol_radical p hp a).mp) hf

end MetaplecticPoisson.Datum
