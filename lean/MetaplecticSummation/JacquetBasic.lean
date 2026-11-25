import MetaplecticSummation.LocalGauss

/-! The basic Jacquet function as a generating series for local Gauss sums. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set Filter
open scoped Topology NNReal
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
section Shell
variable (p : Prime F)
local notation "K" => p.adicCompletion F

private def jacquetPhase (c : Kˣ) (y : K) : ℂ :=
  (if ‖y‖ ≤ ‖c.val‖ then 1 else
    if hy : y ≠ 0 then d.symbol (.inr p) c (Units.mk0 y hy) else 0) *
      d.character.localValue F (.inr p) (-y / c.val)

private theorem primitive_eq_phase
    (hψ : ∀ x : K, ‖x‖ ≤ 1 → d.character.localValue F (.inr p) x = 1)
    (c : Kˣ) (y : K) : d.primitiveJacquet p c y =
      if max ‖c.val‖ ‖y‖ = 1 then d.jacquetPhase p c y else 0 := by
  by_cases h : ‖y‖ ≤ ‖c.val‖
  · rw [max_eq_left h]
    by_cases hc : ‖c.val‖ = 1
    · have hy : ‖y‖ ≤ 1 := hc ▸ h
      simp only [primitiveJacquet,jacquetPhase,if_pos h,if_pos hc,if_pos hy,one_mul]
      exact (hψ _ (by simpa only [norm_div,norm_neg,hc,div_one] using hy)).symm
    · have he : ¬ (‖c.val‖ < 1 ∧ ‖y‖ = 1) := fun ⟨hl,hy⟩ => (h.trans_lt hl).ne hy
      simp only [primitiveJacquet,if_neg hc, if_neg he]
  · have hlt := lt_of_not_ge h
    rw [max_eq_right hlt.le]
    by_cases hy : ‖y‖ = 1
    · have hc : ‖c.val‖ < 1 := hy ▸ hlt
      have hy₀ : y ≠ 0 := norm_ne_zero_iff.mp (hy ▸ one_ne_zero)
      simp only [primitiveJacquet,jacquetPhase,if_neg hc.ne,hc,hy,true_and,if_true,if_neg hc.not_ge,
        dif_pos hy₀, residueTerm]
    · by_cases hc : ‖c.val‖ = 1
      · have hbig : 1 < ‖y‖ := hc ▸ hlt
        simp only [primitiveJacquet, if_pos hc, if_neg hbig.not_ge, if_neg hy]
      · simp only [primitiveJacquet, if_neg hc, hy, and_false, if_false]

private theorem phase_div_pow (c t : Kˣ) (y : K) :
    d.jacquetPhase p (c/t^n) (y/t.val^n) = d.jacquetPhase p c y := by
  have ht := pow_ne_zero n t.ne_zero
  have hnorm : 0 < ‖t.val‖^n := pow_pos (norm_pos_iff.mpr t.ne_zero) _
  have he : -(y/t.val^n) / (c/t^n).val = -y/c.val := by
    rw [Units.val_div_eq_div_val,Units.val_pow_eq_pow_val]
    field_simp
  have hcmp : ‖y/t.val^n‖ ≤ ‖(c/t^n).val‖ ↔ ‖y‖ ≤ ‖c.val‖ := by
    rw [Units.val_div_eq_div_val,Units.val_pow_eq_pow_val,norm_div,norm_div,norm_pow,
      div_le_div_iff_of_pos_right hnorm]
  unfold jacquetPhase
  rw [he]
  by_cases h : ‖y‖ ≤ ‖c.val‖
  · rw [if_pos h,if_pos (hcmp.mpr h)]
  have hy : y ≠ 0 := by rintro rfl; exact h (by simp)
  rw [if_neg h, if_neg (fun h' => h (hcmp.mp h')), dif_pos (div_ne_zero hy ht),dif_pos hy]
  have hu : Units.mk0 (y/t.val^n) (div_ne_zero hy ht) = Units.mk0 y hy / t^n := Units.ext (by simp only [Units.val_mk0, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val])
  apply congrArg (fun z : ℂ => z * d.character.localValue F (.inr p) (-y/c.val))
  let H : Kˣ →* Kˣ →* ℂˣ := d.unitPairing (.inr p)
  have hn (a b : Kˣ) : H a b ^ n = 1 := d.unitPairing_pow (.inr p) a b
  apply congrArg Units.val
  change H (c/t^n) (Units.mk0 (y/t.val^n) (div_ne_zero hy ht)) = H c (Units.mk0 y hy)
  rw [hu]
  simp only [map_div, map_pow, MonoidHom.div_apply, MonoidHom.pow_apply, hn, div_one]

private theorem primitive_div_pow
    (hψ : ∀ x : K, ‖x‖ ≤ 1 → d.character.localValue F (.inr p) x = 1)
    (c t : Kˣ) (y : K) : d.primitiveJacquet p (c/t^n) (y/t.val^n) =
      if max ‖c.val‖ ‖y‖ = ‖t.val‖^n then d.jacquetPhase p c y else 0 := by
  rw [d.primitive_eq_phase p hψ, d.phase_div_pow]
  simp only [Units.val_div_eq_div_val,Units.val_pow_eq_pow_val,norm_div,norm_pow,
    max_div_div_right (pow_nonneg (norm_nonneg _) _),
    div_eq_one_iff_eq (pow_ne_zero n (norm_ne_zero_iff.mpr t.ne_zero))]

local instance : MeasurableSpace K := borel _
local instance : BorelSpace K := ⟨rfl⟩

private theorem scaled_primitive_integral (hp : p.asIdeal.absNorm.Coprime n)
    (hψ : ∀ x : K, ‖x‖ ≤ 1 → d.character.localValue F (.inr p) x = 1)
    (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] (c t : Kˣ) :
    Integrable (fun y : K => d.primitiveJacquet p (c/t) (y/t.val)) μ ∧
    (∫ y : K, d.primitiveJacquet p (c/t) (y/t.val) ∂μ) =
      (μ.real (p.adicCompletionIntegers F : Set K) : ℂ) * (‖c.val‖ : ℂ) * d.localGauss p (c/t) := by
  let g := d.primitiveJacquet p (c/t)
  have he (y : K) : t⁻¹ • y = y/t.val := by simp [Units.smul_def,div_eq_inv_mul]
  constructor
  · have hg := (d.primitiveJacquet_integral p hp hψ (DomMulAct.mk t • μ) (c/t)).1
    have ht := (integrable_map_equiv (μ := μ) (MeasurableEquiv.smul t⁻¹) g).mp hg
    exact ht.congr (Filter.Eventually.of_forall (fun y => congrArg g (he y)))
  · have hv := integral_unit_mul_add μ t⁻¹ 0 g
    have ht (y : K) : t⁻¹.val * y = y/t.val := he y
    simp only [add_zero,inv_inv,ht] at hv
    have hh := (d.primitiveJacquet_integral p hp hψ μ (c/t)).2
    calc
      _ = (distribHaarChar K t : ℝ≥0) • ∫ y, g y ∂μ := hv
      _ = _ := by
        rw [FinitePlace.haarChar_eq_nnnorm, show (∫ y, g y ∂μ) = _ from hh,
          Units.val_div_eq_div_val,norm_div,NNReal.smul_def,Complex.real_smul,Complex.ofReal_div]
        change (‖t.val‖ : ℂ) * _ = _
        have hn : (‖t.val‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr t.ne_zero
        field_simp

private theorem basic_shell_sum (hp : p.asIdeal.absNorm.Coprime n)
    (hψ : ∀ x : K, ‖x‖ ≤ 1 → d.character.localValue F (.inr p) x = 1)
    (π c : Kˣ) (hπ : ‖π.val‖ = (p.asIdeal.absNorm : ℝ)⁻¹)
    (N : ℕ) (hN : ∀ k ≥ N, ‖π.val‖^(n*k) < ‖c.val‖) (y : K) :
    (d.basic (.inr p)).val.1 c y * d.character.localValue F (.inr p) (-y / c.val) =
      ∑ k ∈ Finset.range N, (p.asIdeal.absNorm : ℂ)^((n-1)*k) *
        d.primitiveJacquet p (c/π^(n*k)) (y/π.val^(n*k)) := by
  let r := max ‖c.val‖ ‖y‖
  let w (k : ℕ) : ℂ := (p.asIdeal.absNorm : ℂ)^((n-1)*k)
  have hr (k : ℕ) : ((p.asIdeal.absNorm : ℝ)^(n*k))⁻¹ = ‖π.val‖^(n*k) := by rw [hπ,inv_pow]
  have hcut (k : ℕ) (hk : k ∉ Finset.range N) : r ≠ ‖π.val‖^(n*k) :=
    ne_of_gt ((hN k (Nat.le_of_not_gt (fun h => hk (Finset.mem_range.mpr h)))).trans_le (le_max_left _ _))
  have hrep (k : ℕ) : d.primitiveJacquet p (c/π^(n*k)) (y/π.val^(n*k)) =
      if r = ‖π.val‖^(n*k) then d.jacquetPhase p c y else 0 := by
    have he := d.primitive_div_pow p hψ c (π^k) y
    simpa only [Units.val_pow_eq_pow_val,norm_pow,← pow_mul,Nat.mul_comm k n,r] using he
  rw [basic,dif_pos hp]
  change ((∑' k : ℕ, if r = ((p.asIdeal.absNorm : ℝ)^(n*k))⁻¹ then w k else 0) * _) * _ = _
  rw [mul_assoc]
  change (∑' k : ℕ, if r = ((p.asIdeal.absNorm : ℝ)^(n*k))⁻¹ then w k else 0) *
    d.jacquetPhase p c y = _
  simp_rw [hr,hrep]
  rw [tsum_eq_sum (s := Finset.range N) (fun k hk => if_neg (hcut k hk)), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp [w]

private theorem jacquet_basic_local (hp : p.asIdeal.absNorm.Coprime n)
    (hψ : ∀ x : K, ‖x‖ ≤ 1 → d.character.localValue F (.inr p) x = 1)
    (π c : Kˣ) (hπ : ‖π.val‖ = (p.asIdeal.absNorm : ℝ)⁻¹) :
    let v : Place F := .inr p
    let vol := (selfDual F d.character v).real {x | ‖x‖ ≤ 1}
    d.jacquet v (d.basic v) c = (vol : ℂ) * (modulus F v c.val : ℂ) *
      ∑' k : ℕ, (p.asIdeal.absNorm : ℂ)^((n-1)*k) * d.localGauss p (c / π^(n*k)) := by
  letI : NontriviallyNormedField K := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  let μ : Measure K := selfDual F d.character (.inr p)
  letI : μ.IsAddHaarMeasure := (existsUnique_selfDual F d.character (.inr p)).exists.choose_spec.1
  let q : ℝ := p.asIdeal.absNorm
  have hq : 1 < q := by dsimp [q]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  have ht : ‖π.val‖^n < 1 := pow_lt_one₀ (norm_nonneg _) (hπ ▸ inv_lt_one_of_one_lt₀ hq) (NeZero.ne n)
  obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr c.ne_zero) ht
  have hcut (k : ℕ) (hk : N ≤ k) : ‖π.val‖^(n*k) < ‖c.val‖ := by
    rw [pow_mul]
    exact (pow_le_pow_of_le_one (pow_nonneg (norm_nonneg _) _) ht.le hk).trans_lt hN
  let W (k : ℕ) : ℂ := (p.asIdeal.absNorm : ℂ)^((n-1)*k)
  let g (k : ℕ) (y : K) := d.primitiveJacquet p (c/π^(n*k)) (y/π.val^(n*k))
  have hlocal (k : ℕ) : Integrable (g k) μ ∧
      (∫ y, g k y ∂μ) = (μ.real (p.adicCompletionIntegers F : Set K) : ℂ) *
        (‖c.val‖ : ℂ) * d.localGauss p (c/π^(n*k)) := by
    simpa only [g,Units.val_pow_eq_pow_val] using d.scaled_primitive_integral p hp hψ μ c (π^(n*k))
  have hzero (k : ℕ) (hk : k ∉ Finset.range N) : d.localGauss p (c/π^(n*k)) = 0 := by
    have hbig : 1 < ‖(c/π^(n*k)).val‖ := by
      rw [Units.val_div_eq_div_val,Units.val_pow_eq_pow_val,norm_div,norm_pow,
        one_lt_div (pow_pos (norm_pos_iff.mpr π.ne_zero) _)]
      exact hcut k (by simpa using hk)
    have hmem : (c/π^(n*k)).val ∉ p.adicCompletionIntegers F := fun h =>
      hbig.not_ge ((mem_localIntegers_iff p _).mp h)
    simp only [localGauss,if_neg hbig.ne',dif_neg hmem]
  have hO : {x : K | ‖x‖ ≤ 1} = (p.adicCompletionIntegers F : Set K) :=
    Set.ext fun x => (mem_localIntegers_iff p x).symm
  change (∫ y : K, (d.basic (.inr p)).val.1 c y * d.character.localValue F (.inr p) (-y/c.val) ∂μ) =
    (μ.real {x : K | ‖x‖ ≤ 1} : ℂ) * (‖c.val‖ : ℂ) * ∑' k, W k * d.localGauss p (c/π^(n*k))
  rw [hO,tsum_eq_sum (s := Finset.range N) (fun k hk => by rw [hzero k hk,mul_zero])]
  simp_rw [d.basic_shell_sum p hp hψ π c hπ N hcut]
  change (∫ y, ∑ k ∈ Finset.range N, W k * g k y ∂μ) = _
  rw [integral_finsetSum _ (fun k _ => (hlocal k).1.const_mul (W k)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul,(hlocal k).2]
  ring

end Shell

theorem jacquet_basic (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n)
    (hψ : ∀ x : LocalField F (.inr p), ‖x‖ ≤ 1 → d.character.localValue F (.inr p) x = 1)
    (π c : (LocalField F (.inr p))ˣ) (hπ : ‖(π : LocalField F (.inr p))‖ = (p.asIdeal.absNorm : ℝ)⁻¹) :
    let v : Place F := .inr p
    let vol := (selfDual F d.character v).real {x | ‖x‖ ≤ 1}
    d.jacquet v (d.basic v) c = (vol : ℂ) * (modulus F v c : ℂ) *
      ∑' k : ℕ, (p.asIdeal.absNorm : ℂ)^((n-1)*k) * d.localGauss p (c / π^(n*k)) :=
  d.jacquet_basic_local p hp hψ π c hπ

end MetaplecticPoisson.Datum
