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

end MetaplecticPoisson.Datum
