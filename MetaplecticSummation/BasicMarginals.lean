import MetaplecticSummation.Marginals
import MetaplecticSummation.BasicWeights

/-! The marginal kernels of the basic vector in Appendix A. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Filter Set WithZero
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

private theorem integral_norm_power (p : Prime F) (t : (p.adicCompletion F)ˣ) (ht : ‖t.val‖ ≤ 1) :
    ∃ k : ℕ, ‖t.val‖ = ((p.asIdeal.absNorm : ℝ)^k)⁻¹ := by
  have hv : Valued.v t.val ≠ 0 := Valued.v.ne_zero_iff.mpr t.ne_zero
  have hle := Valued.toNormedField.norm_le_one_iff.mp ht
  rw [← exp_log hv,← exp_zero] at hle
  let k := (-(Valued.v t.val).log).toNat
  have h : Valued.v t.val = exp (-(k : ℤ)) := by
    simp only [k,Int.toNat_of_nonneg (neg_nonneg.mpr (exp_le_exp.mp hle)),neg_neg,exp_log hv]
  refine ⟨k,?_⟩
  rw [NumberField.FinitePlace.norm_def,h,WithZeroMulInt.toNNReal_neg_apply _ (exp_ne_zero (a := _))]
  change (↑((p.asIdeal.absNorm : NNReal) ^ (-(k : ℤ))) : ℝ) = _
  simp

private theorem axis_basic (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n) (y : (LocalField F (.inr p))ˣ) :
    d.axis (.inr p) (d.basic (.inr p)) y = ∑' k : ℕ,
      if ‖y.val‖ = ((p.asIdeal.absNorm : ℝ)^(n*k))⁻¹ then (p.asIdeal.absNorm : ℂ)^((n-1)*k) else 0 := by
  unfold axis
  rw [basic,dif_pos hp]
  simp [basicCharts]

/-- The finite-place basic density is the characteristic function of the local
integers when x and the cover degree have unit norm. -/
theorem axisDensity_basic (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n)
    (hn : ‖(n : LocalField F (.inr p))‖ = 1) (x : (LocalField F (.inr p))ˣ) (hx : ‖x.val‖ = 1)
    (t : LocalField F (.inr p)) :
    d.axisDensity (.inr p) (d.basic (.inr p)) x t = if ‖t‖ ≤ 1 then 1 else 0 := by
  let v : Place F := .inr p
  let q : ℝ := p.asIdeal.absNorm
  have hq : 1 < q := by dsimp [q]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  have he (u : (LocalField F v)ˣ) : d.axisDensity v (d.basic v) x u =
      if ‖u.val‖ ≤ 1 then 1 else 0 := by
    rw [d.axisDensity_unit,d.axis_basic p hp]
    simp only [v,modulus,hn,hx,Complex.ofReal_one,div_one,one_mul,Units.val_div_eq_div_val,
      Units.val_neg,Units.val_pow_eq_pow_val,norm_div,norm_neg,norm_pow]
    by_cases hu : ‖u.val‖ ≤ 1
    · obtain ⟨k,hk⟩ := integral_norm_power p u hu
      change ‖u.val‖ = (q^k)⁻¹ at hk
      have heq (j : ℕ) : ‖u.val‖^n = (q^(n*j))⁻¹ ↔ j = k := by
        rw [hk,inv_pow,← pow_mul,inv_inj]
        rw [Nat.mul_comm k,pow_right_inj₀ (zero_lt_one.trans hq) hq.ne', Nat.mul_right_inj (NeZero.ne n),eq_comm]
      rw [if_pos hu,tsum_eq_single k (fun j hj => if_neg (mt (heq j).mp hj)),if_pos ((heq k).mpr rfl)]
      rw [hk,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_natCast,inv_pow,← pow_mul,Nat.mul_comm k]
      have hq₀ : (p.asIdeal.absNorm : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm p)).ne'
      exact inv_mul_cancel₀ (pow_ne_zero _ hq₀)
    · have hlt : 1 < ‖u.val‖^n := one_lt_pow₀ (lt_of_not_ge hu) (NeZero.ne n)
      have hne (j : ℕ) : ‖u.val‖^n ≠ (q^(n*j))⁻¹ :=
        ne_of_gt ((inv_le_one_of_one_le₀ (one_le_pow₀ hq.le)).trans_lt hlt)
      rw [if_neg hu]
      rw [tsum_eq_single 0 (fun j _ => if_neg (hne j)),if_neg (hne 0),mul_zero]
  by_cases ht : t = 0
  · subst t
    letI : NontriviallyNormedField (LocalField F v) := FinitePlace.nontriviallyNormedCompletion p
    letI : (𝓝[≠] (0 : LocalField F v)).NeBot := NormedField.nhdsNE_neBot _
    have hl : IsLocallyConstant (d.axisDensity v (d.basic v) x) := (d.axisDensity_finite_bruhat p (d.basic v) x).1
    have hlt : ∀ᶠ u : LocalField F v in 𝓝 0, ‖u‖ < 1 := continuous_norm.continuousAt.eventually_lt
      (continuousAt_const (y := (1:ℝ))) (by simp)
    obtain ⟨u,hu,hval,hsmall⟩ := Filter.nonempty_of_mem (f := 𝓝[≠] (0 : LocalField F v))
      (inter_mem (self_mem_nhdsWithin (s := {0}ᶜ)) (mem_nhdsWithin_of_mem_nhds ((hl.eventually_eq 0).and hlt)))
    have eqn := he (Units.mk0 u hu)
    simpa only [Units.val_mk0,if_pos hsmall.le,hval,norm_zero,zero_le_one,if_true] using eqn
  · exact he (Units.mk0 t ht)

/-- On a unit vertical line the basic marginal is the self-dual volume of the integers. -/
theorem marginal_basic_unit (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n)
    (x : (LocalField F (.inr p))ˣ) (hx : ‖x.val‖ = 1) :
    d.marginal (.inr p) (d.basic (.inr p)) x =
      ((selfDual F d.character (.inr p)).real {y | ‖y‖ ≤ 1} : ℂ) := by
  let O := {y : LocalField F (.inr p) | ‖y‖ ≤ 1}
  have hO : MeasurableSet O := (isClosed_le continuous_norm continuous_const).measurableSet
  unfold marginal
  calc
    _ = ∫ y, O.indicator (fun _ => (1:ℂ)) y ∂(selfDual F d.character (.inr p)) := by
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : ‖y‖ ≤ 1
      · have he := d.basic_xChart_unit p hp x.val y hx hy
        rw [indicator_of_mem (show y ∈ O from hy)]
        simpa only [xChart,dif_pos x.ne_zero,Units.mk0_val] using he
      · exact (d.basic_x_outside p hp x y ((lt_of_not_ge hy).trans_le (le_max_right _ _))).trans
          (indicator_of_notMem (show y ∉ O from hy) _).symm
    _ = _ := by simp [integral_indicator hO,Measure.real,O]

/-- With unramified character, the ordinary Fourier transform of the basic
density is the same characteristic function. -/
theorem hat_axisDensity_basic (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n)
    (hn : ‖(n : LocalField F (.inr p))‖ = 1) (hψ : d.UnramifiedAt (.inr p))
    (x : (LocalField F (.inr p))ˣ) (hx : ‖x.val‖ = 1) (u : LocalField F (.inr p)) :
    d.hat (.inr p) (d.axisDensity (.inr p) (d.basic (.inr p)) x) u = if ‖u‖ ≤ 1 then 1 else 0 := by
  let K := p.adicCompletion F
  letI : MeasurableSpace K := borel _
  letI : BorelSpace K := ⟨rfl⟩
  let μ : Measure K := selfDual F d.character (.inr p)
  letI : μ.IsAddHaarMeasure := (existsUnique_selfDual F d.character (.inr p)).exists.choose_spec.1
  let O := (p.adicCompletionIntegers F).toSubring
  have hmem (z : K) : z ∈ O ↔ ‖z‖ ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F p).trans Valued.toNormedField.norm_le_one_iff.symm
  have hperp (z : K) : (∀ y ∈ O, d.character.localValue F (.inr p) (z*y) = 1) ↔ z ∈ O := by
    simp only [hmem]
    exact hψ z
  have h := hat_subring_indicator O (O : Set K) (FinitePlace.isOpen_adicCompletionIntegers p).measurableSet
    μ _ (d.character.localValue_add (.inr p)) hperp u
  have hset : (O : Set K) = {z | ‖z‖ ≤ 1} := Set.ext hmem
  rw [show μ.real (O : Set K) = 1 from hset ▸ d.selfDual_volume_unramified p hψ] at h
  unfold hat
  simp_rw [d.axisDensity_basic p hp hn x hx,mul_comm u]
  simp only [indicator,SetLike.mem_coe,hmem,Complex.ofReal_one] at h
  exact h

/-- At almost every finite place the density of a pure tensor is the entire
basic one-dimensional Schwartz–Bruhat function, including its value at zero. -/
theorem eventually_axisDensity_basic (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v)
    (x : Fˣ) : ∀ᶠ p : Prime F in cofinite, ∀ t : LocalField F (.inr p),
      d.axisDensity (.inr p) (Φ (.inr p)) (atPlace (.inr p) x) t = if ‖t‖ ≤ 1 then 1 else 0 := by
  have he := (Sum.inr_injective (α := InfinitePlace F)).tendsto_cofinite.eventually hΦ
  have ht := (FinitePlace.finite_places_over_degree (K := F) n).eventually_cofinite_notMem
  filter_upwards [he,ht,eventually_diagonal_norm_one x.ne_zero,
    eventually_diagonal_norm_one (F := F) (Nat.cast_ne_zero.mpr (NeZero.ne n))] with p hp hdeg hx hn
  rw [map_natCast] at hn
  rw [hp]
  exact d.axisDensity_basic p (FinitePlace.tame_of_degree_not_mem n p hdeg) hn _ hx

end MetaplecticPoisson.Datum
