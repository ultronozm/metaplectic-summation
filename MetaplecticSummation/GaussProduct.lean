import MetaplecticSummation.BasicProduct
import MetaplecticSummation.GaussRamanujan
import MetaplecticSummation.PowerDivisors

/-! Identification of the product of the basic Jacquet functions with the global power-divisor sum. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable {S : Finset (Place F)}

private def localArgument (p : Prime F) (a : NonzeroInteger S) : (p.adicCompletion F)ˣ :=
  atPlace (.inr p) (fieldUnit a)

private theorem gaussSeries_eq_sum (p : Prime F) (hp : Sum.inr p ∉ S) (c : NonzeroInteger S)
    (π : (p.adicCompletion F)ˣ) (hπ : ‖π.val‖ = (p.asIdeal.absNorm : ℝ)⁻¹) :
    let C : (p.adicCompletion F)ˣ := localArgument p c
    d.gaussSeries p π C = ∑ k : Fin (primeOrder p c.val / n + 1),
      (p.asIdeal.absNorm : ℂ)^((n-1)*k.val) * d.localGauss p (C/π^(n*k.val)) := by
  let C : (p.adicCompletion F)ˣ := localArgument p c
  let e := primeOrder p c.val
  let r := (p.asIdeal.absNorm : ℝ)⁻¹
  have hq : 1 < (p.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
  have hr : 0 < r := inv_pos.mpr (zero_lt_one.trans hq)
  let term (k : ℕ) := (p.asIdeal.absNorm : ℂ)^((n-1)*k) * d.localGauss p (C/π^(n*k))
  change (∑' k, term k) = ∑ k : Fin (e/n+1), term k.val
  rw [Fin.sum_univ_eq_sum_range term]
  apply tsum_eq_sum
  intro k hk
  have hlt : e < n*k := by
    rw [mul_comm]
    apply lt_of_not_ge
    intro h
    exact hk (Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le (NeZero.pos n)).mpr h)))
  let x := C / π^(n*k)
  have hx : 1 < ‖x.val‖ := by
    simp only [x,Units.val_div_eq_div_val,Units.val_pow_eq_pow_val]
    rw [norm_div,norm_pow,hπ, show ‖C.val‖ = r^e from norm_primeOrder p hp c]
    exact (one_lt_div (pow_pos hr _)).mpr (pow_lt_pow_right_of_lt_one₀ hr (inv_lt_one_of_one_lt₀ hq) hlt)
  have hO : x.val ∉ p.adicCompletionIntegers F := fun h => hx.not_ge ((mem_localIntegers_iff p _).mp h)
  change _ * d.localGauss p x = 0
  simp only [localGauss,if_neg hx.ne',dif_neg hO,mul_zero]

/-- A product at the primes of a divisor can be extended over the primes of any multiple
when the omitted unit factors equal one. -/
private theorem extend_divisor_product {M : Type*} [CommMonoid M] (a c : NonzeroInteger S)
    (hd : a.val ∣ c.val) (g : Prime F → M)
    (hg : ∀ p : Prime F, Sum.inr p ∉ S → ‖diagonal F (.inr p) a.val‖ = 1 → g p = 1) :
    (∏ p : modulusPrimes a, g p.val) = ∏ p : modulusPrimes c, g p.val := by
  have hsub : modulusPrimes a ⊆ modulusPrimes c := by
    intro p hp
    obtain ⟨hS,ha⟩ := (mem_modulusPrimes a p).mp hp
    obtain ⟨z,hz⟩ := hd
    refine (mem_modulusPrimes c p).mpr ⟨hS,?_⟩
    rw [hz]
    change ‖diagonal F (.inr p) ((a.val : F) * z)‖ < 1
    rw [map_mul,norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (integer_norm_le_one z p hS)).trans_lt ha
  change (∏ p ∈ (modulusPrimes a).attach, g p.val) = ∏ p ∈ (modulusPrimes c).attach, g p.val
  rw [Finset.prod_attach,Finset.prod_attach]
  apply Finset.prod_subset hsub
  intro p hp ha
  have hS := ((mem_modulusPrimes c p).mp hp).1
  exact hg p hS (le_antisymm (integer_norm_le_one a.val p hS)
    (le_of_not_gt fun hl => ha ((mem_modulusPrimes a p).mpr ⟨hS,hl⟩)))

theorem normalizedGauss_divisorExponents (h : d.ClassicalSetting S) (b c : NonzeroInteger S) :
    letI := h.principal
    d.normalizedGauss S b.val c.val = (sNorm S c.val : ℂ)⁻¹ *
      ∑ k : DivisorExponents c n, d.powerDivisorTerm S b.val c.val (divisorMonomial c (fun p => (k p).val)).val := by
  letI := h.principal
  let e := powerDivisorEquiv c n
  let D := {t : Associates (SIntegers S) // t^n ∣ Associates.mk c.val}
  letI : Fintype D := Fintype.ofEquiv (DivisorExponents c n) e
  let f (a : Associates (SIntegers S)) := d.powerDivisorTerm S b.val c.val (Quotient.out a)
  unfold normalizedGauss
  congr 1
  change (∑ᶠ a, f a) = _
  have restrict : (∑ᶠ a : D, f a.val) = ∑ᶠ a, f a := by
    rw [finsum_subtype_eq_finsum_cond (fun a : Associates (SIntegers S) => a^n ∣ Associates.mk c.val)]
    apply finsum_congr
    intro a
    rw [finsum_eq_if]
    split_ifs with ha
    · rfl
    · have hn : ¬ (Quotient.out a)^n ∣ c.val := by
        intro hd
        apply ha
        rw [← show Associates.mk (Quotient.out a) = a from Quotient.out_eq a, ← Associates.mk_pow]
        exact Associates.mk_dvd_mk.mpr hd
      simp [f,powerDivisorTerm,hn]
  rw [← restrict,finsum_eq_sum_of_fintype,← e.sum_comp (fun a : D => f a.val)]
  apply Finset.sum_congr rfl
  intro k _
  exact d.powerDivisorTerm_congr h.good b.val c (Associates.mk_quot_out _)

private theorem norm_monomial {c : NonzeroInteger S} [IsPrincipalIdealRing (SIntegers S)]
    (k : DivisorExponents c n) (hS : ∀ w, Sum.inl w ∈ S) :
    let a := divisorMonomial c (fun p => (k p).val)
    (sNorm S a.val : ℂ) = ∏ p : modulusPrimes c, (p.val.asIdeal.absNorm : ℂ)^(k p).val := by
  let a := divisorMonomial c (fun p => (k p).val)
  have hd : a.val ∣ c.val := (dvd_pow_self _ (NeZero.ne n)).trans (divisorMonomial_pow_dvd c k)
  have he := extend_divisor_product a c hd (fun p => ‖diagonal F (.inr p) a.val‖) (fun _ _ h => h)
  have H := (prod_norm_modulusPrimes hS a).symm.trans he
  have loc (p : modulusPrimes c) : ‖diagonal F (.inr p.val) a.val‖ = ((p.val.asIdeal.absNorm : ℝ)^(k p).val)⁻¹ := by
    have hp := ((mem_modulusPrimes c p.val).mp p.property).1
    rw [norm_primeOrder p.val hp a, show primeOrder p.val a.val = _ from primeOrder_divisorMonomial c _ p.val hp,
      dif_pos p.property,inv_pow]
  simp_rw [loc] at H
  rw [Finset.prod_inv_distrib,inv_inj] at H
  exact_mod_cast H

private theorem monomial_term (h : d.ClassicalSetting S) (b c : NonzeroInteger S)
    (π : (p : Prime F) → (p.adicCompletion F)ˣ) (hπ : ∀ p, ‖(π p).val‖ = (p.asIdeal.absNorm : ℝ)⁻¹)
    (k : DivisorExponents c n) :
    letI := h.principal
    d.powerDivisorTerm S b.val c.val (divisorMonomial c (fun p => (k p).val)).val =
      ∏ p : modulusPrimes c, (p.val.asIdeal.absNorm : ℂ)^((n-1)*(k p).val) *
        (d.scaled (fieldUnit b)).localGauss p.val
          ((localArgument p.val c : (p.val.adicCompletion F)ˣ) / π p.val^(n*(k p).val)) := by
  letI := h.principal
  let db := d.scaled (fieldUnit b)
  let a := divisorMonomial c (fun p => (k p).val)
  have hd : a.val^n ∣ c.val := divisorMonomial_pow_dvd c k
  let z : NonzeroInteger S := ⟨hd.choose, fun hz => c.property (by simpa [hz] using hd.choose_spec)⟩
  have hz : c.val = a.val^n * z.val := hd.choose_spec
  have hz' : z.val ∣ c.val := ⟨a.val^n,hz.trans (mul_comm _ _)⟩
  have hg := (d.gauss_eq_prod_localGauss b z h).trans (extend_divisor_product z c hz'
    (fun p => db.localGauss p (localArgument p z)) (fun p _ hu => by
      change ‖(localArgument p z : (p.adicCompletion F)ˣ).val‖ = 1 at hu
      simp only [localGauss,if_pos hu]))
  have loc (p : modulusPrimes c) :
      db.localGauss p.val (localArgument p.val z) =
        db.localGauss p.val ((localArgument p.val c : (p.val.adicCompletion F)ˣ) / π p.val^(n*(k p).val)) := by
    have hp := ((mem_modulusPrimes c p.val).mp p.property).1
    let A : (p.val.adicCompletion F)ˣ := localArgument p.val a
    let Z : (p.val.adicCompletion F)ˣ := localArgument p.val z
    let C : (p.val.adicCompletion F)ˣ := localArgument p.val c
    let u := A / (π p.val)^(k p).val
    have hu : ‖u.val‖ = 1 := by
      simp only [u,Units.val_div_eq_div_val,Units.val_pow_eq_pow_val]
      rw [norm_div,norm_pow,hπ,show ‖A.val‖ = _ from norm_primeOrder p.val hp a,
        show primeOrder p.val a.val = _ from primeOrder_divisorMonomial c _ p.val hp,dif_pos p.property]
      exact div_self (pow_ne_zero _ (inv_ne_zero (by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm p.val))))))
    have hC : C = A^n*Z := by
      apply Units.ext
      change diagonal F (.inr p.val) (c.val : F) = _
      rw [hz]
      change diagonal F (.inr p.val) ((a.val : F)^n * z.val) = _
      rw [map_mul,map_pow]
      rfl
    have he : C / π p.val ^ (n*(k p).val) = u^n * Z := by
      rw [hC,div_pow,← pow_mul,Nat.mul_comm (k p).val n]
      simp only [div_eq_mul_inv]
      ac_rfl
    change db.localGauss p.val Z = db.localGauss p.val (C / _)
    rw [he]
    have good := (d.scaled_good h b).2.2 p.val hp
    exact (db.gaussRamanujan_unit_pow p.val good.1 good.2 u Z hu).1.symm
  change d.powerDivisorTerm S b.val c.val a.val = _
  rw [powerDivisorTerm,dif_pos hd, show hd.choose = z.val from rfl,hg,
    show (sNorm S a.val : ℂ) = _ from norm_monomial k h.good.2.1, ← Finset.prod_pow, Finset.prod_mul_distrib]
  congr 1
  · apply Finset.prod_congr rfl
    intro p _
    rw [← pow_mul,Nat.mul_comm]
  · exact Finset.prod_congr rfl (fun p _ => loc p)

/-- The product of the basic Jacquet factors outside S for every nonzero integral modulus. -/
theorem outsideBasic_integral (h : d.ClassicalSetting S) (b c : NonzeroInteger S) :
    (d.scaled (fieldUnit b)).outsideBasic S (fieldUnit c) =
      (Real.sqrt (sNorm S (b.val : F)) : ℂ)⁻¹ * d.normalizedGauss S b.val c.val := by
  letI := h.principal
  choose π hπ using (fun p : Prime F => FinitePlace.exists_norm_uniformizer p)
  let db := d.scaled (fieldUnit b)
  let W (p : modulusPrimes c) (k : Fin (primeOrder p.val c.val / n + 1)) :=
    (p.val.asIdeal.absNorm : ℂ)^((n-1)*k.val) *
      db.localGauss p.val (localArgument p.val c / π p.val^(n*k.val))
  have loc (p : modulusPrimes c) :
      db.gaussSeries p.val (π p.val) (localArgument p.val c) = ∑ k, W p k :=
    db.gaussSeries_eq_sum p.val ((mem_modulusPrimes c p.val).mp p.property).1 c (π p.val) (hπ p.val)
  rw [d.outsideBasic_gaussSeries h b c π hπ,d.normalizedGauss_divisorExponents h b c,← mul_assoc]
  congr 1
  change (∏ p : modulusPrimes c, db.gaussSeries p.val (π p.val) (localArgument p.val c)) = _
  simp_rw [loc]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl (fun k _ => (d.monomial_term h b c π hπ k).symm)

end MetaplecticPoisson.Datum
