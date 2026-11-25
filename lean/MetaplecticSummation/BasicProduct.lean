import MetaplecticSummation.GaussFactorization
import MetaplecticSummation.JacquetBasic

/-! Expansion of the product of basic functions over the primes of the modulus. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField Set Filter
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable {S : Finset (Place F)}

/-- The product of the moduli at the primes dividing c is |c|_S⁻¹. -/
theorem prod_norm_modulusPrimes (hS : ∀ w, Sum.inl w ∈ S) (c : NonzeroInteger S) :
    (∏ p : modulusPrimes c, ‖diagonal F (.inr p.val) c.val‖) = (sNorm S (c.val : F))⁻¹ := by
  let r (p : Prime F) := ‖diagonal F (.inr p) c.val‖
  let g (p : Prime F) := if Sum.inr p ∈ S then 1 else r p
  have he (p : Prime F) : Real.sqrt ‖diagonal F (.inr p) ((fieldUnit c ^ 2 : Fˣ) : F)‖ = r p := by
    change Real.sqrt ‖diagonal F (.inr p) ((c.val : F)^2)‖ = _
    rw [map_pow,norm_pow,Real.sqrt_sq (norm_nonneg _)]
  have hm : 0 ≤ sNorm S (c.val : F) := Finset.prod_nonneg fun v _ => by cases v <;> simp [modulus,pow_nonneg]
  have hnorm : Real.sqrt (sNorm S ((fieldUnit c ^ 2 : Fˣ) : F)) = sNorm S (c.val : F) := by
    change Real.sqrt (sNorm S ((c.val : F)^2)) = _
    rw [pow_two,sNorm_mul,Real.sqrt_mul_self hm]
  have hprod := outside_sqrt_norm S hS (fieldUnit c ^ 2)
  simp_rw [he,hnorm] at hprod
  change finprod g = _ at hprod
  rw [finprod_eq_prod_of_mulSupport_subset (s := modulusPrimes c) _ (by
    intro p hp
    by_cases h : Sum.inr p ∈ S
    · exact (hp (if_pos h)).elim
    · apply (mem_modulusPrimes c p).mpr
      refine ⟨h,lt_of_le_of_ne (integer_norm_le_one c.val p h) (fun he => hp ?_)⟩
      exact (if_neg h).trans he)] at hprod
  rw [← Finset.prod_attach (modulusPrimes c)] at hprod
  refine Eq.trans (Finset.prod_congr rfl (fun p _ => ?_)) hprod
  exact (if_neg ((mem_modulusPrimes c p.val).mp p.property).1).symm

/-- The local series in the Jacquet formula for the basic vector. -/
def gaussSeries (p : Prime F) (π c : (p.adicCompletion F)ˣ) : ℂ :=
  ∑' k : ℕ, (p.asIdeal.absNorm : ℂ)^((n-1)*k) * d.localGauss p (c / π^(n*k))

/-- For an integral modulus, all the nontrivial Gauss series lie at its prime divisors. -/
theorem outsideBasic_gaussSeries (h : d.ClassicalSetting S) (b c : NonzeroInteger S)
    (π : (p : Prime F) → (p.adicCompletion F)ˣ)
    (hπ : ∀ p, ‖(π p).val‖ = (p.asIdeal.absNorm : ℝ)⁻¹) :
    let db := d.scaled (fieldUnit b)
    db.outsideBasic S (fieldUnit c) =
      (Real.sqrt (sNorm S (b.val : F)) : ℂ)⁻¹ * (sNorm S (c.val : F) : ℂ)⁻¹ *
      ∏ p : modulusPrimes c, db.gaussSeries p.val (π p.val) (atPlace (.inr p.val) (fieldUnit c)) := by
  let db := d.scaled (fieldUnit b)
  let U (p : Prime F) : (p.adicCompletion F)ˣ := atPlace (.inr p) (fieldUnit c)
  let T := modulusPrimes c
  let V (p : Prime F) : ℝ := if Sum.inr p ∈ S then 1 else Real.sqrt ‖diagonal F (.inr p) (b.val : F)‖
  let G (p : Prime F) : ℂ := if p ∈ T then (‖(U p).val‖ : ℂ) * db.gaussSeries p (π p) (U p) else 1
  have he (p : Prime F) : (if Sum.inr p ∈ S then 1 else db.jacquet (.inr p) (db.basic (.inr p)) (U p)) =
      (V p : ℂ) * G p := by
    by_cases hp : Sum.inr p ∈ S
    · have ht : p ∉ T := fun h => ((mem_modulusPrimes c p).mp h).1 hp
      simp [G,V,ht,hp]
    · have hg := (d.scaled_good h b).2.2 p hp
      by_cases ht : p ∈ T
      · have hh := db.jacquet_basic p hg.1 hg.2 (π p) (U p) (hπ p)
        have hvol := d.scaled_selfDual_volume p (h.unramified p hp) (fieldUnit b)
        simp only [hp,if_false,V,G,ht,if_true]
        apply hh.trans
        change ((selfDual F db.character (.inr p)).real {x | ‖x‖ ≤ 1} : ℂ) * (‖(U p).val‖ : ℂ) * _ = _
        rw [show (selfDual F db.character (.inr p)).real {x | ‖x‖ ≤ 1} = _ from hvol]
        exact mul_assoc _ _ _
      · have hunit : ‖(U p).val‖ = 1 := le_antisymm (integer_norm_le_one c.val p hp)
          (le_of_not_gt fun hl => ht ((mem_modulusPrimes c p).mpr ⟨hp,hl⟩))
        simp only [hp,if_false,V,G,ht,mul_one]
        exact d.scaled_basic_unit h b p hp (U p) hunit
  have hV : Function.HasFiniteMulSupport V := eventually_cofinite.mp (by
    filter_upwards [eventually_diagonal_norm_one (fieldUnit b).ne_zero] with p hp
    change ‖diagonal F (.inr p) (b.val : F)‖ = 1 at hp
    simp [V,hp])
  have hG : Function.mulSupport G ⊆ (T : Set (Prime F)) := fun p hp =>
    by_contra fun hn => hp (if_neg hn)
  change (∏ᶠ p, if Sum.inr p ∈ S then 1 else db.jacquet (.inr p) (db.basic (.inr p)) (U p)) = _
  simp_rw [he]
  rw [finprod_mul_distrib (hV.fun_comp (g := Complex.ofReal) Complex.ofReal_one) (T.finite_toSet.subset hG),
    finprod_eq_prod_of_mulSupport_subset _ hG, ← Finset.prod_attach T]
  have hvol : (∏ᶠ p, (V p : ℂ)) = (Real.sqrt (sNorm S (b.val : F)) : ℂ)⁻¹ :=
    (Complex.ofRealHom.toMonoidHom.map_finprod hV).symm.trans
      ((congrArg Complex.ofReal (outside_sqrt_norm S h.good.2.1 (fieldUnit b))).trans (Complex.ofReal_inv _))
  rw [hvol]
  have hg (p : T) : G p.val = (‖(U p.val).val‖ : ℂ) * db.gaussSeries p.val (π p.val) (U p.val) := if_pos p.property
  simp_rw [hg]
  rw [Finset.prod_mul_distrib,← mul_assoc]
  congr 2
  · change (∏ p : modulusPrimes c, (‖diagonal F (.inr p.val) (c.val : F)‖ : ℂ)) = _
    exact (Complex.ofReal_prod _ _).symm.trans ((congrArg Complex.ofReal (prod_norm_modulusPrimes h.good.2.1 c)).trans (Complex.ofReal_inv _))

/-- No n-th power of a local nonunit divides c outside S. -/
def LocallyPowerFree (n : ℕ) (c : NonzeroInteger S) : Prop :=
  ∀ (p : Prime F) (hp : Sum.inr p ∉ S) (t : p.adicCompletionIntegers F),
    t^n ∣ toLocalInteger p hp c.val → IsUnit t

theorem LocallyPowerFree.isUnit_of_pow_dvd {c : NonzeroInteger S} (hf : LocallyPowerFree n c)
    (t : SIntegers S) (ht : t^n ∣ c.val) : IsUnit t := by
  have hn : (t : F) ≠ 0 := by
    intro hz
    obtain ⟨k,hk⟩ := ht
    apply c.property
    rw [hk,show t = 0 from Subtype.ext hz,zero_pow (NeZero.ne n),zero_mul]
  have hinv : (t : F)⁻¹ ∈ SIntegers S := by
    intro p hp
    let e := toLocalInteger p hp
    have he : (e t)^n ∣ e c.val := e.map_pow t n ▸ map_dvd e ht
    have hnorm := (localInteger_isUnit_iff p (e t)).mp (hf p hp (e t) he)
    apply (diagonal_norm_le_one_iff _ p).mp
    rw [map_inv₀,norm_inv,show ‖diagonal F (.inr p) t‖ = 1 from hnorm,inv_one]
  exact isUnit_iff_exists_inv.mpr ⟨⟨_,hinv⟩,Subtype.ext (mul_inv_cancel₀ hn)⟩

private theorem gaussSeries_power_free (p : Prime F) (π c : (p.adicCompletion F)ˣ)
    (hπ : ‖π.val‖ < 1) (hc : c.val ∈ p.adicCompletionIntegers F)
    (hf : ∀ t : p.adicCompletionIntegers F, t^n ∣ (⟨c.val,hc⟩ : p.adicCompletionIntegers F) → IsUnit t) :
    d.gaussSeries p π c = d.localGauss p c := by
  unfold gaussSeries
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    have hlt := pow_lt_one₀ (norm_nonneg _) hπ hk
    let t : p.adicCompletionIntegers F := ⟨π.val^k,(mem_localIntegers_iff p _).mpr (by rw [norm_pow]; exact hlt.le)⟩
    let x := c/π^(n*k)
    have hx : x.val ∉ p.adicCompletionIntegers F := by
      intro h
      have hd : t ^ n ∣ (⟨c.val,hc⟩ : p.adicCompletionIntegers F) := by
        refine ⟨⟨x.val,h⟩,Subtype.ext ?_⟩
        change c.val = (π.val^k)^n * x.val
        rw [← pow_mul,Nat.mul_comm k n]
        simp only [x,Units.val_div_eq_div_val,Units.val_pow_eq_pow_val]
        field_simp
      have he := (localInteger_isUnit_iff p t).mp (hf t hd)
      change ‖π.val^k‖ = 1 at he
      rw [norm_pow] at he
      exact hlt.ne he
    have hn : ‖x.val‖ ≠ 1 := fun he => hx ((mem_localIntegers_iff p _).mpr he.le)
    change _ * d.localGauss p x = 0
    simp only [localGauss,if_neg hn,dif_neg hx,mul_zero]

/-- The product of basic functions for locally n-th-power-free moduli. -/
theorem outsideBasic_power_free (h : d.ClassicalSetting S) (b c : NonzeroInteger S)
    (hf : LocallyPowerFree n c) :
    (d.scaled (fieldUnit b)).outsideBasic S (fieldUnit c) =
      (Real.sqrt (sNorm S (b.val : F)) : ℂ)⁻¹ * d.normalizedGauss S b.val c.val := by
  choose π hπ using (fun p : Prime F => FinitePlace.exists_norm_uniformizer p)
  let db := d.scaled (fieldUnit b)
  have hs (p : modulusPrimes c) := (mem_modulusPrimes c p.val).mp p.property
  have he (p : modulusPrimes c) : db.gaussSeries p.val (π p.val) (atPlace (.inr p.val) (fieldUnit c)) =
      db.localGauss p.val (atPlace (.inr p.val) (fieldUnit c)) := by
    have hq : 1 < (p.val.asIdeal.absNorm : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p.val
    exact db.gaussSeries_power_free p.val _ _ (hπ p.val ▸ inv_lt_one_of_one_lt₀ hq)
      (localModulus c p).property (hf p.val (hs p).1)
  rw [d.outsideBasic_gaussSeries h b c π hπ,d.normalizedGauss_power_free h.good b c hf.isUnit_of_pow_dvd]
  change _ * _ * (∏ p : modulusPrimes c, db.gaussSeries p.val (π p.val) (atPlace (.inr p.val) (fieldUnit c))) = _
  simp_rw [he]
  rw [← d.gauss_eq_prod_localGauss b c h]
  ring

/-- When S contains the infinite places, its complement consists of the finite primes outside S. -/
theorem product_outside_eq_basic (hS : ∀ w, Sum.inl w ∈ S) (c : Fˣ) :
    (∏ᶠ v : {v : Place F // v ∉ S}, d.jacquet v.val (d.basic v.val) (atPlace v.val c)) =
      d.outsideBasic S c := by
  let e : {p : Prime F // Sum.inr p ∉ S} ≃ {v : Place F // v ∉ S} :=
    { toFun := fun p => ⟨.inr p.val, p.property⟩
      invFun := fun v => match v with
        | ⟨.inl w, h⟩ => (h (hS w)).elim
        | ⟨.inr p, h⟩ => ⟨p,h⟩
      left_inv := fun _ => rfl
      right_inv := fun v => by
        obtain ⟨w | p,h⟩ := v
        · exact (h (hS w)).elim
        · rfl }
  let g (p : Prime F) := d.jacquet (.inr p) (d.basic (.inr p)) (atPlace (.inr p) c)
  rw [← finprod_comp_equiv e]
  change (∏ᶠ p : {p : Prime F // Sum.inr p ∉ S}, g p.val) = _
  rw [finprod_subtype_eq_finprod_cond (fun p : Prime F => Sum.inr p ∉ S)]
  apply finprod_congr
  intro p
  rw [finprod_eq_if]
  by_cases hp : Sum.inr p ∈ S <;> simp [hp,g]

/-- The product formula for basic Jacquet functions at a locally n-th-power-free modulus. -/
theorem product_basic_power_free (h : d.ClassicalSetting S) (b c : NonzeroInteger S)
    (hf : LocallyPowerFree n c) :
    let db := d.scaled (fieldUnit b)
    (∏ᶠ v : {v : Place F // v ∉ S}, db.jacquet v.val (db.basic v.val) (atPlace v.val (fieldUnit c))) =
      (Real.sqrt (sNorm S (b.val : F)) : ℂ)⁻¹ * d.normalizedGauss S b.val c.val :=
  ((d.scaled (fieldUnit b)).product_outside_eq_basic h.good.2.1 _).trans
    (d.outsideBasic_power_free h b c hf)

/-- The product formula for basic Jacquet functions at a nonintegral modulus. -/
theorem product_basic_of_nonintegral (h : d.ClassicalSetting S) (b : NonzeroInteger S)
    (c : Fˣ) (hc : (c : F) ∉ SIntegers S) :
    let db := d.scaled (fieldUnit b)
    (∏ᶠ v : {v : Place F // v ∉ S}, db.jacquet v.val (db.basic v.val) (atPlace v.val c)) = 0 :=
  ((d.scaled (fieldUnit b)).product_outside_eq_basic h.good.2.1 _).trans
    (d.outsideBasic_zero_of_nonintegral h b c hc)

end MetaplecticPoisson.Datum
