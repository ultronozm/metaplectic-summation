import MetaplecticSummation.TwistedSummation

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable {S : Finset (Place F)} {f : NonzeroInteger S}

omit [NeZero n] in
private theorem split_twist_product (T : Twist (n := n) S f)
    (s : S → ℂ) (t : T.primes → ℂ) (base g : Place F → ℂ)
    (hb : Function.HasFiniteMulSupport base)
    (hs : ∀ (v : S), g v = s v * base v)
    (ht : ∀ (p : T.primes), g (.inr p.val) = t p * base (.inr p.val))
    (ho : ∀ v ∉ T.places, g v = base v) :
    (∏ᶠ v, g v) = (∏ v, s v) * (∏ p, t p) * ∏ᶠ v, base v := by
  let a (v : Place F) := if hv : v ∈ S then s ⟨v,hv⟩ else 1
  let b : Place F → ℂ
    | .inl _ => 1
    | .inr p => if hp : p ∈ T.primes then t ⟨p,hp⟩ else 1
  let P := T.primes.image (Sum.inr : Prime F → Place F)
  have ha : Function.mulSupport a ⊆ (S : Set (Place F)) := fun _ hx =>
    by_contra fun h => hx (dif_neg h)
  have hP : Function.mulSupport b ⊆ (P : Set (Place F)) := by
    rintro (w | p) hx
    · exact (hx rfl).elim
    · have hp : p ∈ T.primes := by_contra fun h => hx (dif_neg h)
      exact Finset.mem_image_of_mem _ hp
  have hsa : (∏ᶠ v, a v) = ∏ v, s v := by
    rw [finprod_eq_prod_of_mulSupport_subset _ ha, ← Finset.prod_attach S]
    exact Finset.prod_congr rfl fun v _ => dif_pos v.property
  have htb : (∏ᶠ v, b v) = ∏ p, t p := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hP]
    unfold P
    rw [Finset.prod_image (fun _ _ _ _ he => Sum.inr.inj he), ← Finset.prod_attach T.primes]
    exact Finset.prod_congr rfl fun p _ => dif_pos p.property
  rw [← hsa, ← htb, ← finprod_mul_distrib (S.finite_toSet.subset ha) (P.finite_toSet.subset hP)]
  have hab : Function.HasFiniteMulSupport (fun v => a v * b v) :=
    Function.HasFiniteMulSupport.mul (f := a) (g := b) (S.finite_toSet.subset ha) (P.finite_toSet.subset hP)
  rw [← finprod_mul_distrib hab hb]
  apply finprod_congr
  rintro (w | p)
  · by_cases hw : Sum.inl w ∈ S
    · simpa [a,b,hw] using hs ⟨_,hw⟩
    · simpa [a,b,hw] using ho (.inl w) (fun he => hw ((T.infinite_mem_places w).mp he))
  · by_cases hp : p ∈ T.primes
    · simpa [a,b,hp,T.outside p hp] using ht ⟨p,hp⟩
    · by_cases hv : Sum.inr p ∈ S
      · simpa [a,b,hp,hv] using hs ⟨_,hv⟩
      · simpa [a,b,hp,hv] using ho (.inr p) (by simp [T.finite_mem_places,hp,hv])

/-- The original adelic summand of Theorem 10.34 at an arbitrary field element. -/
theorem twistedGauss_original_factor (h : d.ClassicalSetting S) (b : NonzeroInteger S)
    (T : Twist (n := n) S f) (coprime : IsCoprime b.val f.val) (W : Weights S) (c : Fˣ) :
    (d.scaled (fieldUnit b)).globalWeight (T.weights W) false c =
      sWeight W c * twistValue T c *
        (if hc : (c : F) ∈ SIntegers S then
          (Real.sqrt (sNorm S (fieldUnit b)) : ℂ)⁻¹ * d.normalizedGauss S b.val ⟨_,hc⟩ else 0) := by
  let db := d.scaled (fieldUnit b)
  let J (v : Place F) := db.jacquet v (db.basic v) (atPlace v c)
  let base (v : Place F) := if v ∈ S then 1 else J v
  have hb : Function.HasFiniteMulSupport base :=
    Filter.eventually_cofinite.mp (eventually_place_of_finite (d.eventually_scaled_basic_one h b c))
  have hbase : (∏ᶠ v, base v) = ∏ᶠ v : {v : Place F // v ∉ S}, J v.val := by
    rw [finprod_subtype_eq_finprod_cond (fun v : Place F => v ∉ S)]
    apply finprod_congr
    intro v
    rw [finprod_eq_if]
    by_cases hv : v ∈ S <;> simp [base,hv]
  rw [← d.product_basic h b c, ← hbase]
  unfold globalWeight sWeight twistValue
  apply split_twist_product T _ _ base _ hb
  · rintro ⟨w | p,hv⟩
    · have he := (T.infinite_mem_places w).mpr hv
      simp [he,base,hv,Twist.weights]
    · have he := (T.finite_mem_places p).mpr (Or.inl hv)
      simp [he,base,hv,Twist.weights]
  · intro p
    have hv := T.outside _ p.property
    have he := (T.finite_mem_places p.val).mpr (Or.inr p.property)
    simp only [he,dif_pos,Bool.false_eq_true,if_false,T.weights_at_prime,base,if_neg hv]
    by_cases hu : ‖(atPlace (.inr p.val) c).val‖ = 1
    · have hj := d.scaled_basic_unit h b p.val hv (atPlace (.inr p.val) c) hu
      have hB := T.norm_frequency coprime p
      change ‖diagonal F (.inr p.val) (b.val : F)‖ = 1 at hB
      have hJ : J (.inr p.val) = 1 := by simpa only [hB,Real.sqrt_one,Complex.ofReal_one] using hj
      rw [hJ,mul_one]
    · have hnu : atPlace (.inr p.val) c ∉ integralUnits p.val := hu
      simp [charWeight,hnu]
  · intro v hv
    have hS : v ∉ S := fun he => hv (Finset.mem_union_left _ he)
    simp [base,J,db,hv,hS]

/-- At a prime outside both S and the twist conductor, reindexing the dual
basic vector contributes a single Hilbert symbol. -/
theorem twistedGauss_dual_basic (h : d.ClassicalSetting S) (b : NonzeroInteger S)
    (T : Twist (n := n) S f) (p : Prime F) (hp : Sum.inr p ∉ T.places) (c : Fˣ) :
    let v : Place F := .inr p
    let db := d.scaled (fieldUnit b)
    db.jacquet v (db.fourier v (db.basic v)) (atPlace v (c/(fieldUnit b^n * fieldUnit f^(n-1)))) =
      d.symbol v (atPlace v c) (atPlace v (fieldUnit f)) * db.jacquet v (db.basic v) (atPlace v c) := by
  let v : Place F := .inr p
  let B := atPlace v (fieldUnit b)
  let P := atPlace v (fieldUnit f)
  let X := atPlace v c
  let db := d.scaled (fieldUnit b)
  have hout := not_or.mp (fun h' => hp ((T.finite_mem_places p).mpr h'))
  have hP : ‖P.val‖ = 1 := T.unit_elsewhere p hout.1 hout.2
  have hU : ‖(P^(n-1))⁻¹.val‖ = 1 := by
    simp only [Units.val_inv_eq_inv_val,norm_inv,Units.val_pow_eq_pow_val,norm_pow,hP,one_pow,inv_one]
  have hexp : P^(n-1) * P = P^n := by rw [← pow_succ,Nat.sub_add_cancel (NeZero.pos n)]
  have symb : db.symbol v X (P^(n-1))⁻¹ = d.symbol v X P := by
    apply congrArg Units.val
    change d.unitPairing v X (P^(n-1))⁻¹ = d.unitPairing v X P
    have h1 : d.unitPairing v X (P^(n-1)) * d.unitPairing v X P = 1 := by
      rw [← map_mul,hexp,map_pow,d.unitPairing_pow]
    exact (inv_eq_of_mul_eq_one_right h1) ▸ map_inv _ _
  have hj := db.basic_dual p (h.good.2.2 p hout.1).1 B (integer_norm_le_one b.val p hout.1)
    (d.scaled_conductor (fieldUnit b) v (h.unramified p hout.1)) (X/(B^n*P^(n-1)))
  have harg : B^n*(X/(B^n*P^(n-1))) = (P^(n-1))⁻¹ * X := by
    rw [← mul_div_assoc,mul_div_mul_left_eq_div,div_eq_inv_mul]
  rw [harg] at hj
  have ht := db.jacquet_basic_unit_mul p (h.good.2.2 p hout.1).1 ((d.scaled_good h b).2.2 p hout.1).2
    (P^(n-1))⁻¹ X hU
  dsimp only at ht ⊢
  have he := (hj.trans ht).trans (congrArg (· * db.jacquet v (db.basic v) X) symb)
  simpa only [B,P,X,v,db,atPlace,map_div,map_mul,map_pow] using he

private def outsideSymbol (T : Twist (n := n) S f) (c : Fˣ) (v : Place F) :=
  if v ∈ T.places then 1 else d.symbol v (atPlace v c) (atPlace v (fieldUnit f))

private theorem outsideSymbol_product (h : d.ClassicalSetting S) (T : Twist (n := n) S f)
    (c : NonzeroInteger S) (ht : twistValue T (fieldUnit c) ≠ 0) :
    (∏ᶠ v, d.outsideSymbol T (fieldUnit c) v) = d.residue S (fieldUnit f) (fieldUnit c) := by
  let P := (modulusPrimes c).image (Sum.inr : Prime F → Place F)
  have hs : Function.mulSupport (d.outsideSymbol T (fieldUnit c)) ⊆ (P : Set _) := by
    rintro (w | p) hx
    · exact (hx (if_pos ((T.infinite_mem_places w).mpr (h.good.2.1 w)))).elim
    · have hp : Sum.inr p ∉ T.places := fun hi => hx (if_pos hi)
      have hout := not_or.mp (fun he => hp ((T.finite_mem_places p).mpr he))
      apply Finset.mem_image_of_mem
      apply (mem_modulusPrimes c p).mpr
      refine ⟨hout.1, lt_of_le_of_ne (integer_norm_le_one c.val p hout.1) ?_⟩
      intro hu
      apply hx
      rw [outsideSymbol,if_neg hp]
      exact congrArg Units.val (d.unitPairing_tame_units p (h.good.2.2 p hout.1).1
        (atPlace _ (fieldUnit c)) (atPlace _ (fieldUnit f)) hu (T.unit_elsewhere p hout.1 hout.2))
  rw [finprod_eq_prod_of_mulSupport_subset _ hs,d.residue_on_modulus_primes]
  unfold P
  rw [Finset.prod_image (fun _ _ _ _ he => Sum.inr.inj he)]
  apply Finset.prod_congr rfl
  intro p hp
  obtain ⟨hS,hc⟩ := (mem_modulusPrimes c p).mp hp
  have hT : p ∉ T.primes := by
    intro hpT
    apply ht
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨p,hpT⟩ : T.primes))
    exact dif_neg (show atPlace (.inr p) (fieldUnit c) ∉ integralUnits p from hc.ne)
  rw [outsideSymbol, if_neg (fun he => ((T.finite_mem_places p).mp he).elim hS hT),
    if_pos (T.unit_elsewhere p hS hT)]

private theorem dual_scaled_shift (b : NonzeroInteger S) (W : Weights S) (hW : Admissible W)
    (c : Fˣ) (v : S) :
    (d.scaled (fieldUnit b)).dualWeight v.val (W v)
      (atPlace _ (c/(fieldUnit b^n*fieldUnit f^(n-1)))) =
    d.dualWeight v.val (fun x => W v x * d.symbol v.val x (atPlace _ (fieldUnit b)))
      (atPlace _ (c/(fieldUnit b*fieldUnit f^(n-1)))) := by
  rw [d.dual_scaled _ _ (hW v)]
  congr 1
  simp only [atPlace,map_div,map_pow,map_mul]
  have hn (B : (LocalField F v.val)ˣ) : B^(n-1)*B = B^n := by
    rw [← pow_succ,Nat.sub_add_cancel (NeZero.pos n)]
  rw [← hn, mul_assoc, ← mul_div_assoc, mul_div_mul_left_eq_div]

/-- The reindexed dual summand, including the zero terms at nonintegral
arguments and at arguments sharing a prime with the conductor. -/
theorem twistedGauss_dual_factor (h : d.ClassicalSetting S) (b : NonzeroInteger S)
    (T : Twist (n := n) S f) (coprime : IsCoprime b.val f.val) (W : Weights S)
    (hW : Admissible W) (c : Fˣ) :
    (d.scaled (fieldUnit b)).globalWeight (T.weights W) true
      (c/(fieldUnit b^n * fieldUnit f^(n-1))) =
    d.sDual (fun v x => W v x * d.symbol v.val x (atPlace _ (fieldUnit b)))
        (c/(fieldUnit b * fieldUnit f^(n-1))) *
      (d.epsilon T (fieldUnit b) * (starRingEnd ℂ) (twistValue T c) * d.residue S c (fieldUnit f)) *
      (d.residue S (fieldUnit f) c *
        (if hc : (c : F) ∈ SIntegers S then
          (Real.sqrt (sNorm S (fieldUnit b)) : ℂ)⁻¹ * d.normalizedGauss S b.val ⟨_,hc⟩ else 0)) := by
  let db := d.scaled (fieldUnit b)
  let X := c/(fieldUnit b^n * fieldUnit f^(n-1))
  let s (v : S) := d.dualWeight v.val (fun x => W v x * d.symbol v.val x (atPlace _ (fieldUnit b)))
    (atPlace _ (c/(fieldUnit b * fieldUnit f^(n-1))))
  let t (p : T.primes) := db.dualWeight (.inr p.val) (charWeight (T.character p)) (atPlace _ X)
  let J (v : Place F) := db.jacquet v (db.basic v) (atPlace v c)
  let base (v : Place F) := if v ∈ S then 1 else J v
  let H := d.outsideSymbol T c
  have hb : Function.HasFiniteMulSupport base :=
    Filter.eventually_cofinite.mp (eventually_place_of_finite (d.eventually_scaled_basic_one h b c))
  have hh : Function.HasFiniteMulSupport H := by
    apply Filter.eventually_cofinite.mp
    filter_upwards [(d.symbol_reciprocity c (fieldUnit f)).1] with v hv
    simp [H,outsideSymbol,hv]
  have hprod : db.globalWeight (T.weights W) true X =
      (∏ v, s v) * (∏ p, t p) * ∏ᶠ v, H v * base v := by
    unfold globalWeight
    apply split_twist_product T s t (fun v => H v * base v) _ (Function.HasFiniteMulSupport.mul hh hb)
    · rintro ⟨w | p,hv⟩
      · have he := (T.infinite_mem_places w).mpr hv
        simpa only [he,dif_pos,if_true,Twist.weights,H,outsideSymbol,base,hv,one_mul,mul_one,s,X,db] using
          d.dual_scaled_shift (f := f) b W hW c ⟨.inl w,hv⟩
      · have he := (T.finite_mem_places p).mpr (Or.inl hv)
        simpa only [he,dif_pos,if_true,Twist.weights,H,outsideSymbol,base,hv,one_mul,mul_one,s,X,db] using
          d.dual_scaled_shift (f := f) b W hW c ⟨.inr p,hv⟩
    · intro p
      have hv := T.outside _ p.property
      have he := (T.finite_mem_places p.val).mpr (Or.inr p.property)
      simp only [he,dif_pos,if_true,T.weights_at_prime,H,outsideSymbol,one_mul,base,if_neg hv]
      change t p = t p * J (.inr p.val)
      by_cases hu : ‖(atPlace (.inr p.val) c).val‖ = 1
      · have hB := T.norm_frequency coprime p
        change ‖diagonal F (.inr p.val) (b.val : F)‖ = 1 at hB
        have hj := d.scaled_basic_unit h b p.val hv (atPlace (.inr p.val) c) hu
        have hJ : J (.inr p.val) = 1 := by simpa only [hB,Real.sqrt_one,Complex.ofReal_one] using hj
        rw [hJ,mul_one]
      · have hnu : atPlace (.inr p.val) c ∉ integralUnits p.val := hu
        have hz := d.dual_conductor_factor h f b T coprime p (atPlace (.inr p.val) c)
        have ht : t p = 0 := by
          simpa only [t,db,X,atPlace,map_div,map_mul,map_pow,charWeight,dif_neg hnu,map_zero,mul_zero,zero_mul] using hz
        simp [ht]
    · rintro (w | p) hv
      · exact (hv ((T.infinite_mem_places w).mpr (h.good.2.1 w))).elim
      · have hS : Sum.inr p ∉ S := fun hi => hv ((T.finite_mem_places p).mpr (Or.inl hi))
        simpa only [dif_neg hv,if_neg hv,if_true,base,if_neg hS,H,outsideSymbol,J,X,db] using d.twistedGauss_dual_basic h b T p hv c
  have hbase : (∏ᶠ v, base v) = ∏ᶠ v : {v : Place F // v ∉ S}, J v.val := by
    rw [finprod_subtype_eq_finprod_cond (fun v : Place F => v ∉ S)]
    apply finprod_congr
    intro v
    rw [finprod_eq_if]
    by_cases hv : v ∈ S <;> simp [base,hv]
  have ht := d.conductor_product h b T coprime c
  change (∏ p, t p) = _ at ht
  change db.globalWeight (T.weights W) true X = (∏ v, s v) * _ * _
  rw [hprod,ht,finprod_mul_distrib hh hb,hbase]
  have hj := d.product_basic h b c
  change (∏ᶠ v : {v : Place F // v ∉ S}, J v.val) = _ at hj
  rw [hj]
  by_cases hi : (c : F) ∈ SIntegers S
  · by_cases hz : twistValue T c = 0
    · simp [hz]
    · let a : NonzeroInteger S := ⟨⟨c,hi⟩,fun e => c.ne_zero (congrArg Subtype.val e)⟩
      have ha : fieldUnit a = c := Units.ext rfl
      have hp := d.outsideSymbol_product h T a (ha ▸ hz)
      rw [ha] at hp
      rw [show (∏ᶠ v, H v) = _ from hp]
  · simp [hi]

end MetaplecticPoisson.Datum
