import MetaplecticSummation.Jacquet.Kernel
import MetaplecticSummation.BasicConductor

/-! The local degree-one Jacquet transform for test weights and basic vectors. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open MeasureTheory NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F]
/-- In degree one the local transform of a compactly supported test weight is inversion. -/
theorem dualWeight_degree_one (d : Datum F 1) (v : Place F) {W : Weight v} (hw : TestWeight v W)
    (c : (LocalField F v)ˣ) : d.dualWeight v W c = W c⁻¹ := by
  let A := d.kernelAmplitude v W c
  let G := d.hat v A
  have hh : d.hat v G (-c.val) = A c.val := by
    cases v with
    | inl w => simpa only [neg_neg] using congrFun (d.arch_hat_hat w A (d.arch_kernelAmplitude_bruhat w hw c)) (-c.val)
    | inr p => simpa only [neg_neg] using d.hat_hat_finite p (d.finite_kernelAmplitude_bruhat p hw c) (-c.val)
  have h1 : modulus F v 1 = 1 := by cases v <;> simp [modulus]
  have hm : modulus F v ((-c)⁻¹.val) = (modulus F v c.val)⁻¹ := by cases v <;> simp [modulus,inv_pow]
  have hs : d.symbol v c⁻¹ (-c) = 1 := by
    have h := congrArg (fun u : ℂˣ => (u : ℂ)) (d.unitPairing_pow v c⁻¹ (-c))
    simpa only [pow_one,coe_unitPairing,Units.val_one] using h
  have he (t : LocalField F v) : d.kernelIntegral v W c t = G ((t-0) * ((-c)⁻¹.val)) := by
    rw [d.kernelIntegral_eq_hat]
    simp only [G,A,pow_one,sub_zero,Units.val_inv_eq_inv_val,Units.val_neg,inv_neg]
    congr 1
    ring
  have aff := d.hat_affine v G 0 1 (-c)⁻¹

  simp only [one_div,Units.val_inv_eq_inv_val,Units.val_neg,inv_inv,hh,
    mul_zero,d.character.localValue_zero,mul_one] at aff
  have heq : d.dualWeight v W c = d.hat v (fun t => G ((t-0) * ((-c)⁻¹.val))) 1 := by
    simp only [dualWeight,Nat.cast_one,h1,Real.sqrt_one,Complex.ofReal_one,inv_one,one_mul,he,hat]
    congr 1
    funext t
    ring
  rw [heq]
  simp only [Units.val_inv_eq_inv_val,Units.val_neg]
  rw [aff]
  change d.kernelAmplitude v W c c.val / _ = _
  rw [d.kernelAmplitude_unit,hs,mul_one,show modulus F v (-c.val)⁻¹ = _ by simpa only [Units.val_inv_eq_inv_val,Units.val_neg] using hm,Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr (modulus_ne_zero v c)]

private theorem basicCharts_degree_one (d : Datum F 1) (p : Prime F)
    (c : (LocalField F (.inr p))ˣ) (y : LocalField F (.inr p)) :
    (d.basicCharts p).1 c y = if ‖c.val‖ ≤ 1 ∧ ‖y‖ ≤ 1 then 1 else 0 := by
  classical
  let q : ℝ := p.asIdeal.absNorm
  have hq : 1 < q := by dsimp [q]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  let g (r : ℝ) : ℂ := ∑' k : ℕ, if r = (q^k)⁻¹ then 1 else 0
  have weight (u : (LocalField F (.inr p))ˣ) : g ‖u.val‖ = if ‖u.val‖ ≤ 1 then 1 else 0 := by
    by_cases hu : ‖u.val‖ ≤ 1
    · obtain ⟨k,hk⟩ := integral_norm_power p u hu
      change ‖u.val‖ = (q^k)⁻¹ at hk
      rw [if_pos hu]
      simp only [g,hk,inv_inj,pow_right_inj₀ (zero_lt_one.trans hq) hq.ne']
      simp
    · have h (k : ℕ) : ‖u.val‖ ≠ (q^k)⁻¹ := fun e => hu (e ▸ inv_le_one_of_one_le₀ (one_le_pow₀ hq.le))
      simp [g,h,hu]
  have hs (x z : (LocalField F (.inr p))ˣ) : d.symbol (.inr p) x z = 1 := by
    simpa only [pow_one,coe_unitPairing,Units.val_one] using
      congrArg (fun u : ℂˣ => (u : ℂ)) (d.unitPairing_pow (.inr p) x z)
  by_cases hy : ‖y‖ ≤ ‖c.val‖
  · simpa only [g,q,basicCharts,one_mul,tsub_self,zero_mul,pow_zero,max_eq_left hy,if_pos hy,mul_one,
      and_iff_left_of_imp (fun h => hy.trans h)] using weight c
  · have hy₀ : y ≠ 0 := fun h => hy (by simp [h])
    convert (weight (Units.mk0 y hy₀)) using 1 <;> simp only [g,q,basicCharts,one_mul,tsub_self,zero_mul,pow_zero,max_eq_right (le_of_not_ge hy),
      if_neg hy,dif_pos hy₀,hs,mul_one,Units.val_mk0,and_iff_right_of_imp (fun h => (le_of_not_ge hy).trans h)]
    congr!

private theorem jacquet_basic_degree_one (d : Datum F 1) (p : Prime F)
    (b c : (LocalField F (.inr p))ˣ)
    (hb : ∀ x : LocalField F (.inr p), (∀ y, ‖y‖ ≤ 1 → d.character.localValue F (.inr p) (x*y) = 1) ↔ ‖x*b.val‖ ≤ 1) :
    d.jacquet (.inr p) (d.basic (.inr p)) c =
      if ‖c.val‖ ≤ 1 ∧ ‖b.val‖ ≤ ‖c.val‖ then
        ((selfDual F d.character (.inr p)).real {y | ‖y‖ ≤ 1} : ℂ) else 0 := by
  classical
  let bv : p.adicCompletion F := b.val
  let cv : p.adicCompletion F := c.val
  letI : MeasurableSpace (p.adicCompletion F) := borel _
  letI : BorelSpace (p.adicCompletion F) := ⟨rfl⟩
  let μ : Measure (p.adicCompletion F) := selfDual F d.character (.inr p)
  letI : μ.IsAddHaarMeasure := (existsUnique_selfDual F d.character (.inr p)).exists.choose_spec.1
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  let O := closedBallSubgroup (K := (p.adicCompletion F)) 1 zero_le_one
  let D := {x : (p.adicCompletion F) | ‖x*bv‖ ≤ 1}
  have mem (x : (p.adicCompletion F)) : x ∈ O ↔ ‖x‖ ≤ 1 := by
    change x ∈ Metric.closedBall (0:(p.adicCompletion F)) 1 ↔ _
    exact mem_closedBall_zero_iff
  have perp (x : (p.adicCompletion F)) : (∀ y ∈ O, d.character.localValue F (.inr p) (x*y) = 1) ↔ x ∈ D := by
    simp only [mem]
    exact hb x
  have hm : MeasurableSet (O : Set (p.adicCompletion F)) := by
    change MeasurableSet (Metric.closedBall (0:(p.adicCompletion F)) 1)
    exact Metric.isClosed_closedBall.measurableSet
  have h := hat_addSubgroup_indicator O D hm μ _ (d.character.localValue_add (.inr p)) perp (-cv⁻¹)
  rw [jacquet,basic,dif_pos (Nat.coprime_one_right _)]
  simp_rw [d.basicCharts_degree_one]
  by_cases hc : ‖c.val‖ ≤ 1
  · simp only [hc,true_and]
    have cond : -cv⁻¹ ∈ D ↔ ‖b.val‖ ≤ ‖c.val‖ := by
      change ‖-cv⁻¹ * bv‖ ≤ 1 ↔ _
      simp only [norm_mul,norm_neg,norm_inv,← div_eq_inv_mul,div_le_one (show 0 < ‖cv‖ from norm_pos_iff.mpr c.ne_zero)]
      rfl
    have setEq : (O : Set (p.adicCompletion F)) = {y | ‖y‖ ≤ 1} := Set.ext mem
    simp only [Set.indicator,cond,setEq,Set.mem_setOf_eq] at h
    refine Eq.trans ?_ h
    apply integral_congr_ae
    filter_upwards with x
    change _ * d.character.localValue F (.inr p) (-x/c.val) =
      _ * d.character.localValue F (.inr p) (x * (-c.val⁻¹))
    rw [show -x/c.val = x * (-c.val⁻¹) by ring]
    rfl
  · simp [hc]

/-- In degree one the Jacquet transform of the basic vector at any conductor
takes its value at the reciprocal argument. -/
theorem jacquet_basic_dual_degree_one (d : Datum F 1) (p : Prime F) (c : (LocalField F (.inr p))ˣ) :
    d.jacquet (.inr p) (d.fourier (.inr p) (d.basic (.inr p))) c =
      d.jacquet (.inr p) (d.basic (.inr p)) c⁻¹ := by
  obtain ⟨b,hb⟩ := d.exists_finite_conductor p
  have h := d.basicCharts_jacquet_dual p (Nat.coprime_one_right _) b hb c
  have eqn : d.jacquet (.inr p) (d.fourier (.inr p) (d.basic (.inr p))) c =
      d.jacquet (.inr p) (d.basic (.inr p)) (b*c) := by
    unfold jacquet
    rw [d.fourier_apply,basic,dif_pos (Nat.coprime_one_right _)]
    simpa only [pow_one] using h
  rw [eqn,d.jacquet_basic_degree_one p b _ hb,d.jacquet_basic_degree_one p b _ hb]
  have hc := norm_pos_iff.mpr c.ne_zero
  have hpos := norm_pos_iff.mpr b.ne_zero
  have hle : ‖b.val‖ * ‖c.val‖ ≤ 1 ↔ ‖b.val‖ ≤ ‖c.val‖⁻¹ := by
    rw [← one_div,le_div_iff₀ hc]
  simp only [Units.val_mul,norm_mul,Units.val_inv_eq_inv_val,norm_inv,hle,inv_le_one₀ hc,
    le_mul_iff_one_le_right hpos,and_comm]
end MetaplecticPoisson.Datum
