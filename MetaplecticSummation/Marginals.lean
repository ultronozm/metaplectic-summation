import MetaplecticSummation.FiniteRays
import MetaplecticSummation.Schwartz
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

omit [NeZero n] in
theorem Bruhat.integrable {v : Place F} {g : LocalField F v → ℂ} (hg : Bruhat v g) :
    Integrable g (selfDual F d.character v) := by
  letI : (selfDual F d.character v).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  cases v with
  | inr p =>
    obtain ⟨hl,hc⟩ := hg
    exact hl.continuous.integrable_of_hasCompactSupport hc
  | inl w =>
    letI : MeasurableSpace w.Completion := borel _
    letI : BorelSpace w.Completion := ⟨rfl⟩
    let μ : Measure w.Completion := selfDual F d.character (.inl w)
    letI : μ.IsAddHaarMeasure := (existsUnique_selfDual F d.character (.inl w)).exists.choose_spec.1
    have pull {L : Type} [NormedField L] [NormedAlgebra ℝ L] [FiniteDimensional ℝ L]
        [MeasurableSpace L] [BorelSpace L] [SecondCountableTopology L]
        (e : w.Completion ≃+* L) (he : Isometry e) (f : SchwartzMap L ℂ) (hf : ∀ x, g x = f (e x)) :
        Integrable g μ := by
      let i : w.Completion ≃ᵢ L := ⟨e.toEquiv,he⟩
      letI : (μ.map e).IsAddHaarMeasure := e.toAddEquiv.isAddHaarMeasure_map μ he.continuous i.symm.continuous
      rw [show g = (f ∘ e) from funext hf]
      exact (integrable_map_measure f.continuous.aestronglyMeasurable he.continuous.aemeasurable).mp f.integrable
    dsimp only [Bruhat] at hg
    split at hg
    · obtain ⟨f,hf⟩ := hg
      exact pull _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _) f hf
    · obtain ⟨f,hf⟩ := hg
      exact pull _ (InfinitePlace.Completion.isometry_extensionEmbedding w) f hf

/-- The Y-chart line integral along the axis, including at parameter zero. -/
def axisLine (v : Place F) (Φ : d.schwartz v) (y : (LocalField F v)ˣ) (t : LocalField F v) :=
  (radon n (d.symbol v) (modulus F v) (selfDual F d.character v) Φ.val t).2 0 y

omit [NeZero n] in
theorem selfDual_nullSingleton (v : Place F) : NullSingletonClass (selfDual F d.character v) := by
  letI : LocallyCompactSpace (LocalField F v) := by
    cases v with
    | inl w => exact inferInstanceAs (LocallyCompactSpace w.Completion)
    | inr p => exact inferInstanceAs (LocallyCompactSpace (p.adicCompletion F))
  letI : (𝓝[≠] (0 : LocalField F v)).NeBot := by
    cases v with
    | inl w =>
      letI := archNontriviallyNormedCompletion w
      exact NormedField.nhdsNE_neBot (0 : LocalField F (.inl w))
    | inr p =>
      letI := FinitePlace.nontriviallyNormedCompletion p
      exact NormedField.nhdsNE_neBot (0 : p.adicCompletion F)
  letI : (selfDual F d.character v).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  exact Measure.IsAddHaarMeasure.nullSingletonClass _

/-- At nonzero parameter the line is vertical, so its normalized integral is a marginal. -/
theorem axisLine_unit (v : Place F) (Φ : d.schwartz v) (y t : (LocalField F v)ˣ) :
    d.axisLine v Φ y t = d.symbol v (-1) y / (modulus F v y : ℂ) * d.marginal v Φ (t^n/y) := by
  let dx := selfDual F d.character v
  letI : NullSingletonClass dx := d.selfDual_nullSingleton v
  let H := d.lineSymbol v (by cases v with
    | inl w => exact d.arch_steinberg w
    | inr p => exact d.finite_steinberg p)
  have hs (z : (LocalField F v)ˣ) : d.symbol v (t^n/y) z = d.symbol v z y := by
    change ((H.pairing (t^n/y) z).val) = (H.pairing z y).val
    rw [map_div,MonoidHom.div_apply,H.pow_left,one_div,← H.skew]
  unfold axisLine radon marginal
  simp only [zero_mul,zero_add]
  rw [div_mul_eq_mul_div, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [dx.ae_ne 0] with z hz
  have hg := (d.schwartz_glues v Φ) (t^n/y) (Units.mk0 z hz)
  rw [hs] at hg
  simp only [Units.val_mk0,Units.val_div_eq_div_val,Units.val_pow_eq_pow_val] at hg
  rw [dif_pos hz,hg]
  ring

/-- At parameter zero the same integral is the Hilbert-symbol-weighted axis integral. -/
theorem axisLine_zero (v : Place F) (Φ : d.schwartz v) (y : (LocalField F v)ˣ) :
    d.axisLine v Φ y 0 = d.symbol v (-1) y / (modulus F v y : ℂ) *
      ∫ z, if hz : z ≠ 0 then d.symbol v (Units.mk0 z hz) y * d.axis v Φ (Units.mk0 z hz)
        else 0 ∂(selfDual F d.character v) := by
  unfold axisLine radon axis
  simp only [zero_mul,zero_pow (NeZero.ne n),zero_add,zero_div]
  rw [div_mul_eq_mul_div, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ≠ 0
  · rw [dif_pos hz,dif_pos hz]
    ring
  · rw [dif_neg hz,dif_neg hz,mul_zero]

/-- The first Fourier identity of Appendix A at every place. -/
theorem axis_fourier (v : Place F) (Φ : d.schwartz v) (y u : (LocalField F v)ˣ) :
    d.axis v (d.fourier v Φ) (u^n*y) =
      (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ *
      (modulus F v u : ℂ)^(1-(n : ℤ)) * d.hat v (d.axisLine v Φ y) u := by
  have h := (d.transform_pow_ray v Φ.val u).2 0 y
  simp only [mul_zero] at h
  have he : (1-(n : ℤ)) = -((n-1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (NeZero.pos n)]
    push_cast
    ring
  have hm := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v u)
  unfold axis
  rw [d.fourier_apply,he,zpow_neg,zpow_natCast]
  change _ = _ * _ * d.hat v (d.axisLine v Φ y) u
  field_simp [hm]
  simpa only [hat,axisLine,div_eq_mul_inv,mul_comm] using h

/-- At frequency zero the Fourier transform of the vertical line integral gives
the leading term of the transformed section on the axis. -/
theorem axisLine_hat_zero (v : Place F) (Φ : d.schwartz v) (y : (LocalField F v)ˣ)
    (hi : Integrable (d.axisLine v Φ y) (selfDual F d.character v)) :
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ * d.hat v (d.axisLine v Φ y) 0 =
      (d.leading v (d.fourier v Φ)).2 0 y := by
  letI : NeBot (comap (fun u : (LocalField F v)ˣ => u.val) (𝓝 0)) := by
    cases v with
    | inl w =>
      letI := archNontriviallyNormedCompletion w
      exact units_neBot_at_zero
    | inr p =>
      letI := FinitePlace.nontriviallyNormedCompletion p
      exact units_neBot_at_zero (L := p.adicCompletion F)
  have ht := ((d.continuous_hat v hi).tendsto 0).comp
    (tendsto_comap (f := fun u : (LocalField F v)ˣ => u.val))
  apply tendsto_nhds_unique (ht.const_mul _)
  apply ((d.leading_spec v (d.fourier v Φ)).2 0 y).congr
  intro u
  simpa only [axisLine,hat,Function.comp_apply,d.fourier_apply] using
    (d.transform_pow_ray v Φ.val u).2 0 y

private theorem bruhat_finite_slice {P : Type*} [TopologicalSpace P] {p : HeightOneSpectrum (𝓞 F)}
    {g : P → LocalField F (.inr p) → ℂ} (hg : SmoothFiniteFamily g) (q : P) :
    Bruhat (.inr p) (g q) := by
  obtain ⟨C,hC,ho⟩ := (hg.2 {q} (isCompact_singleton)).2.1
  exact ⟨hg.1.comp_continuous (continuous_const.prodMk continuous_id),
    HasCompactSupport.intro hC (ho q (Set.mem_singleton q))⟩

/-- The marginal slice of a finite-place test section is Schwartz–Bruhat in the root variable. -/
theorem axisLine_finiteTest_bruhat (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (hΦ : Φ.val ∈ d.testSet (.inr p)) (y : (LocalField F (.inr p))ˣ) :
    Bruhat (.inr p) (d.axisLine (.inr p) Φ y) :=
  bruhat_finite_slice (d.smooth_finiteTest_lines p hΦ).2 (0,y)

/-- The density in the converse marginal identity. Its value at zero is the
normalized leading term at the point of the axis. -/
def axisDensity (v : Place F) (Φ : d.schwartz v) (x : (LocalField F v)ˣ) (t : LocalField F v) : ℂ :=
  (modulus F v (n : LocalField F v) : ℂ) / (modulus F v x : ℂ) *
    if ht : t = 0 then (d.leading v Φ).2 0 (-1/x)
    else (modulus F v t : ℂ)^(n-1) * d.axis v Φ (-(Units.mk0 t ht)^n/x)

theorem axisDensity_unit (v : Place F) (Φ : d.schwartz v) (x t : (LocalField F v)ˣ) :
    d.axisDensity v Φ x t = (modulus F v (n : LocalField F v) : ℂ) / (modulus F v x : ℂ) *
      (modulus F v t : ℂ)^(n-1) * d.axis v Φ (-(t^n)/x) := by
  unfold axisDensity
  rw [dif_neg t.ne_zero,Units.mk0_val,mul_assoc]

@[simp] theorem axisDensity_zero (v : Place F) (Φ : d.schwartz v) (x : (LocalField F v)ˣ) :
    d.axisDensity v Φ x 0 = (modulus F v (n : LocalField F v) : ℂ) / (modulus F v x : ℂ) *
      (d.leading v Φ).2 0 (-1/x) := by simp [axisDensity]

/-- At a finite place the density is Schwartz–Bruhat for every Schwartz section,
including transforms of test sections. -/
theorem axisDensity_finite_bruhat (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (x : (LocalField F (.inr p))ˣ) : Bruhat (.inr p) (d.axisDensity (.inr p) Φ x) := by
  let v : Place F := .inr p
  let K := LocalField F v
  let q : K × Kˣ := (0,-1/x)
  let c : ℂ := (modulus F v (n : K) : ℂ) / (modulus F v x : ℂ)
  obtain ⟨E,hE,he⟩ := (d.finite_schwartz_rayExtensions p Φ).2
  have hb : IsLocallyConstant (E q) ∧ HasCompactSupport (E q) := bruhat_finite_slice hE q
  have hu (t : Kˣ) : E q t.val = (modulus F v t : ℂ)^(n-1) * d.axis v Φ (-(t^n)/x) := by
    simpa only [q,mul_zero,mul_div_assoc',mul_neg_one,axis,modulus] using he q t
  have hzero : E q 0 = (d.leading v Φ).2 0 (-1/x) := by
    letI : NontriviallyNormedField K := FinitePlace.nontriviallyNormedCompletion p
    letI : NeBot (comap (fun u : Kˣ => u.val) (𝓝 0)) := units_neBot_at_zero
    have ht := (hb.1.continuous.tendsto 0).comp (tendsto_comap (f := fun u : Kˣ => u.val) (x := 𝓝 0))
    apply tendsto_nhds_unique ht
    have hl := (d.leading_spec v Φ).2 0 (-1/x)
    exact hl.congr fun t => (he q t).symm
  have eqn : d.axisDensity v Φ x = fun t => c * E q t := by
    funext t
    by_cases ht : t = 0
    · subst t
      rw [axisDensity_zero,hzero]
    · let u := Units.mk0 t ht
      change d.axisDensity v Φ x u.val = c * E q u.val
      rw [d.axisDensity_unit,hu,mul_assoc]
  rw [show d.axisDensity (.inr p) Φ x = _ from eqn]
  exact ⟨hb.1.comp (c * ·),hb.2.mul_left (f := fun _ => c)⟩

/-- Schwartz regularity of both marginal kernels and the converse Fourier identity
on the full local Schwartz space (Appendix A). -/
theorem schwartz_marginal_kernels (v : Place F) (Φ : d.schwartz v) (x y : (LocalField F v)ˣ) :
    Bruhat v (d.axisLine v Φ y) ∧ Bruhat v (d.axisDensity v Φ x) ∧
    ∀ u : (LocalField F v)ˣ, d.marginal v (d.fourier v Φ) (u^n*x) =
      (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ * d.hat v (d.axisDensity v Φ x) u := by sorry

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
        d.marginal v (d.fourier v Φ) (u^n*x) = k * d.hat v σ u) := by
  dsimp only
  obtain ⟨hν,hσ,hrev⟩ := d.schwartz_marginal_kernels v Φ x y
  exact ⟨_,_,hν,hσ,fun t => ⟨d.axisLine_unit v Φ y t,d.axisDensity_unit v Φ x t⟩,
    fun u => ⟨d.axis_fourier v Φ y u,hrev u⟩⟩

end MetaplecticPoisson.Datum
