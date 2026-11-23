import MetaplecticSummation.AdelicConductor
import MetaplecticSummation.FourierOrthogonality
import MetaplecticSummation.FiniteRayFourier

/-! Volumes and Fourier integrals of local integer rings for a given conductor. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Set WithZero
open scoped Pointwise
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

omit [NeZero n] in
/-- The annihilator of the integer ring is a fractional ideal. Local constancy
and nontriviality give the first ball on which the character is nontrivial. -/
theorem exists_finite_conductor (p : Prime F) :
    ∃ b : (LocalField F (.inr p))ˣ, ∀ x : LocalField F (.inr p),
      (∀ y : LocalField F (.inr p), ‖y‖ ≤ 1 → d.character.localValue F (.inr p) (x*y) = 1) ↔
        ‖x*b.val‖ ≤ 1 := by
  let K := LocalField F (.inr p)
  let ψ := d.character.localValue F (.inr p)
  let q : ℝ := p.asIdeal.absNorm
  have hq : 1 < q := by dsimp [q]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  have hpos := zero_lt_one.trans hq
  have hψ : ψ 0 = 1 := d.character.localValue_zero _
  let P (j : ℤ) := ∃ z : K, ‖z‖ ≤ q^j ∧ ψ z ≠ 1
  obtain ⟨z,hz⟩ := d.character.nontrivial_finiteValue p
  have hz₀ : z ≠ 0 := fun h => hz (h ▸ hψ)
  obtain ⟨j,hj⟩ := norm_zpow_residue_card p (Units.mk0 z hz₀)
  have hex : ∃ j, P j := ⟨j,z,hj.le,hz⟩
  have near := (d.character.locallyConstant_finiteValue p).eventually_eq 0
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp near
  obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hq)
  have hN' : q^(-(N : ℤ)) < ε := by simpa only [zpow_neg,zpow_natCast,inv_pow] using hN
  obtain ⟨m,⟨z,hz,hz'⟩,hmin⟩ := Int.exists_least_of_bdd (P := P) (by
    refine ⟨-(N:ℤ),?_⟩
    rintro j ⟨z,hz,hbad⟩
    by_contra! h
    apply hbad
    exact (hball (mem_ball_zero_iff.mpr ((hz.trans (zpow_le_zpow_right₀ hq.le h.le)).trans_lt hN'))).trans hψ) hex
  obtain ⟨π,hπ⟩ : ∃ π : Kˣ, ‖π.val‖ = q⁻¹ := FinitePlace.exists_norm_uniformizer p
  let b := π^(m-1)
  have hb : ‖b.val‖ = (q^(m-1))⁻¹ := by
    simp only [b,Units.val_zpow_eq_zpow_val,norm_zpow,hπ,inv_zpow]
  refine ⟨b,fun x => ?_⟩
  rw [norm_mul,hb,← div_eq_mul_inv,div_le_one (zpow_pos hpos _)]
  constructor
  · intro h
    by_contra! hbig
    have hx : x ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hbig
      exact (zpow_pos hpos (m-1)).not_gt hbig
    obtain ⟨i,hi⟩ := norm_zpow_residue_card p (Units.mk0 x hx)
    change ‖x‖ = q^i at hi
    have hmi : m-1 < i := (zpow_lt_zpow_iff_right₀ hq).mp (hi ▸ hbig)
    have hzx : ‖z‖ ≤ ‖x‖ := hi ▸ hz.trans (zpow_le_zpow_right₀ hq.le (by omega : m ≤ i))
    have hh := h (z/x) (by rwa [norm_div,div_le_one (norm_pos_iff.mpr hx)])
    exact hz' (by simpa only [mul_div_cancel₀ _ hx] using hh)
  · intro hx y hy
    by_contra hbad
    have hz : ‖x*y‖ ≤ q^(m-1) := by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hy).trans hx
    have := hmin (m-1) ⟨x*y,hz,hbad⟩
    omega

/-- The ordinary Fourier integral of a subring indicator is its volume times
the indicator of its annihilator. -/
theorem hat_subring_indicator {K : Type*} [NormedField K] [MeasurableSpace K] [BorelSpace K]
    (O : Subring K) (D : Set K) (hO : MeasurableSet (O : Set K))
    (μ : Measure K) [μ.IsAddHaarMeasure] (ψ : K → ℂ) (ha : ∀ x y, ψ (x+y) = ψ x * ψ y)
    (hperp : ∀ x : K, (∀ y ∈ O, ψ (x*y) = 1) ↔ x ∈ D) (y : K) :
    (∫ x, (O : Set K).indicator (fun _ => (1 : ℂ)) x * ψ (x*y) ∂μ) =
      D.indicator (fun _ => (μ.real (O : Set K) : ℂ)) y :=
  hat_addSubgroup_indicator O.toAddSubgroup D hO μ ψ ha hperp y

omit [NeZero n] in
/-- The annihilator of the integer ring is b⁻¹ times the ring. The
self-dual volume is therefore the square root of the normalized modulus of b. -/
theorem selfDual_volume_of_conductor (p : Prime F) (b : (p.adicCompletion F)ˣ)
    (hψ : ∀ x : p.adicCompletion F, (∀ y : p.adicCompletion F, ‖y‖ ≤ 1 →
      d.character.localValue F (.inr p) (x*y) = 1) ↔ ‖x * b.val‖ ≤ 1) :
    (selfDual F d.character (.inr p)).real {x | ‖x‖ ≤ 1} = Real.sqrt ‖b.val‖ := by
  letI : MeasurableSpace (p.adicCompletion F) := borel _
  letI : BorelSpace (p.adicCompletion F) := ⟨rfl⟩
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace (p.adicCompletion F) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  let O := (p.adicCompletionIntegers F).toSubring
  let μ : Measure (p.adicCompletion F) := selfDual F d.character (.inr p)
  have hm := (existsUnique_selfDual F d.character (.inr p)).exists.choose_spec
  letI : μ.IsAddHaarMeasure := hm.1
  have hmem (x : p.adicCompletion F) : x ∈ O ↔ ‖x‖ ≤ 1 :=
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F p).trans
      Valued.toNormedField.norm_le_one_iff.symm
  have hO : IsClopen (O : Set (p.adicCompletion F)) :=
    ⟨(FinitePlace.isCompact_adicCompletionIntegers p).isClosed, Valued.isOpen_valuationSubring _⟩
  let D := (b⁻¹ • (O : Set (p.adicCompletion F)))
  have hd (x : p.adicCompletion F) : x ∈ D ↔ x*b.val ∈ O := by
    change x ∈ b⁻¹ • (O : Set (p.adicCompletion F)) ↔ _
    rw [Set.mem_inv_smul_set_iff, Units.smul_def, smul_eq_mul, mul_comm]
    rfl
  have hD : MeasurableSet D := hO.isOpen.smul b⁻¹ |>.measurableSet
  have hp := volume_mul_annihilator O.toAddSubgroup D hD hO (FinitePlace.isCompact_adicCompletionIntegers p)
    μ (d.character.localValue F (.inr p)) (d.character.localValue_add (.inr p))
    (fun x => by
      change (∀ y ∈ O, _) ↔ x ∈ D
      simpa only [hd, hmem] using hψ x) hm.2
  change μ.real (O : Set _) * μ.real D = 1 at hp
  have hvol := congrArg ENNReal.toReal (distribHaarChar_mul μ b⁻¹ (O : Set (p.adicCompletion F)))
  rw [FinitePlace.haarChar_eq_nnnorm, ENNReal.toReal_mul, ENNReal.coe_toReal] at hvol
  change ‖b⁻¹.val‖ * μ.real O = μ.real D at hvol
  rw [← hvol, Units.val_inv_eq_inv_val, norm_inv] at hp
  have hnorm : ‖b.val‖ ≠ 0 := norm_ne_zero_iff.mpr b.ne_zero
  field_simp at hp
  have hs : {x : LocalField F (.inr p) | ‖x‖ ≤ 1} = (O : Set (p.adicCompletion F)) :=
    Set.ext fun x => (hmem x).symm
  rw [hs]
  change μ.real O = Real.sqrt ‖b.val‖
  symm
  apply (Real.sqrt_eq_iff_mul_self_eq (norm_nonneg _) measureReal_nonneg).mpr
  simpa only [pow_two] using hp.symm

omit [NeZero n] in
theorem selfDual_volume_unramified (p : Prime F) (hψ : d.UnramifiedAt (.inr p)) :
    (selfDual F d.character (.inr p)).real {x | ‖x‖ ≤ 1} = 1 := by
  simpa only [Units.val_one, norm_one, Real.sqrt_one] using
    d.selfDual_volume_of_conductor p 1 (fun x => by rw [Units.val_one, mul_one]; exact hψ x)

omit [NeZero n] in
/-- The self-dual measures give the integral reference factors volume one
outside a finite set of primes. -/
theorem eventually_selfDual_volume_one :
    ∀ᶠ p : Prime F in Filter.cofinite, (selfDual F d.character (.inr p)).real {x | ‖x‖ ≤ 1} = 1 :=
  d.eventually_unramified.mono (fun p hp => d.selfDual_volume_unramified p hp)

omit [NeZero n] in
theorem scaled_selfDual_volume (p : Prime F) (hψ : d.UnramifiedAt (.inr p)) (b : Fˣ) :
    (selfDual F (d.scaled b).character (.inr p)).real {x | ‖x‖ ≤ 1} =
      Real.sqrt ‖diagonal F (.inr p) b‖ :=
  (d.scaled b).selfDual_volume_of_conductor p (atPlace (.inr p) b) (d.scaled_conductor b (.inr p) hψ)

omit [NeZero n] in
/-- The ordinary Fourier transform of the unit ball for an unramified character. -/
theorem integral_unitBall_character (p : Prime F) (hψ : d.UnramifiedAt (.inr p))
    (u : LocalField F (.inr p)) :
    (∫ y, (if ‖y‖ ≤ 1 then (1:ℂ) else 0) * d.character.localValue F (.inr p) (y*u)
      ∂selfDual F d.character (.inr p)) = if ‖u‖ ≤ 1 then 1 else 0 := by
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
  simp only [indicator,SetLike.mem_coe,hmem,Complex.ofReal_one] at h
  exact h.trans (if_congr (show u ∈ (O : Set K) ↔ ‖u‖ ≤ 1 from hmem u) rfl rfl)

end MetaplecticPoisson.Datum
