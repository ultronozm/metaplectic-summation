import MetaplecticSummation.GaussProduct

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory
open Classical
open scoped ComplexConjugate
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [hn : NeZero n] (d : Datum F n)

omit hn in
theorem scaled_one : d.scaled 1 = d := by
  have he : (d.scaled 1).character.toChar = d.character.toChar := by
    apply AddChar.ext
    intro x
    simpa only [scaled,Units.val_one,map_one,one_mul] using (d.exists_scaled 1).choose_spec x
  have extChar (a b : Character F) (h : a.toChar = b.toChar) : a = b := by
    cases a
    cases b
    congr
  have hc := extChar _ _ he
  exact congrArg (fun ψ => {d with character := ψ}) hc

private theorem globalWeight_untwisted {S : Finset (Place F)} (h : d.ClassicalSetting S)
    (W : Weights S) (dual : Bool) (c : Fˣ) :
    d.globalWeight W dual c = (if dual then d.sDual W c else sWeight W c) *
      (if hc : (c : F) ∈ SIntegers S then d.normalizedGauss S 1 ⟨_,hc⟩ else 0) := by
  let b : NonzeroInteger S := ⟨1,one_ne_zero⟩
  have hb : fieldUnit b = 1 := Units.ext rfl
  have hbNorm : sNorm S (fieldUnit b : F) = 1 := sNorm_unit h.good.2.1 1
  let w (v : S) := (if dual then d.dualWeight v.val (W v) else W v) (atPlace v.val c)
  let inside (v : Place F) := if hv : v ∈ S then w ⟨v,hv⟩ else 1
  let J (v : Place F) := d.jacquet v (d.basic v) (atPlace v c)
  let outside (v : Place F) := if v ∈ S then 1 else J v
  have fixed (v : Place F) (hv : v ∉ S) :
      d.jacquet v (d.fourier v (d.basic v)) (atPlace v c) = J v := by
    obtain v | p := v
    · exact (hv (h.good.2.1 v)).elim
    · have conductor (x : LocalField F (.inr p)) :
          (∀ y : LocalField F (.inr p), ‖y‖ ≤ 1 → d.character.localValue F (.inr p) (x*y) = 1) ↔
          ‖x * (1 : (LocalField F (.inr p))ˣ)‖ ≤ 1 := by simpa using h.unramified p hv x
      simpa only [one_pow,one_mul,J] using
        d.basic_dual p (h.good.2.2 p hv).1 1 (by simp) conductor (atPlace (.inr p) c)
  have hI : Function.mulSupport inside ⊆ (S : Set (Place F)) :=
    fun v h => by_contra fun hv => h (dif_neg hv)
  have hO : Function.HasFiniteMulSupport outside := by
    apply Filter.eventually_cofinite.mp
    apply eventually_place_of_finite
    have hu := d.eventually_scaled_basic_one h b c
    rw [hb,d.scaled_one] at hu
    exact hu
  have splitProduct : d.globalWeight W dual c = (∏ᶠ v, inside v) * ∏ᶠ v, outside v := by
    rw [← finprod_mul_distrib (S.finite_toSet.subset hI) hO]
    unfold globalWeight
    apply finprod_congr
    intro v
    by_cases hv : v ∈ S
    · simp only [hv,dif_pos,inside,outside,w,if_true,mul_one]
    · cases dual <;> simp [inside,outside,J,hv,fixed v hv]
  have hi : (∏ᶠ v, inside v) = if dual then d.sDual W c else sWeight W c := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hI,← Finset.prod_attach S]
    have hw (v : S) : inside v.val = w v := dif_pos v.property
    simp_rw [hw]
    cases dual <;> rfl
  have ho : (∏ᶠ v, outside v) = ∏ᶠ v : {v : Place F // v ∉ S}, J v.val := by
    rw [finprod_subtype_eq_finprod_cond (fun v : Place F => v ∉ S)]
    apply finprod_congr
    intro v
    rw [finprod_eq_if]
    by_cases hv : v ∈ S <;> simp [outside,hv]
  have hp := d.product_basic h b c
  dsimp only at hp
  have db_eq : d.scaled (fieldUnit b) = d := hb ▸ d.scaled_one
  rw [db_eq] at hp
  simp only [hbNorm,Real.sqrt_one,Complex.ofReal_one,inv_one,one_mul] at hp
  exact splitProduct.trans (congrArg₂ (· * ·) hi (ho.trans hp))

theorem fieldUnit_injective {S : Finset (Place F)} : Function.Injective (fieldUnit (S := S)) :=
  fun _ _ he => Subtype.ext (Subtype.ext (congrArg Units.val he))

private theorem globalWeight_integer {S : Finset (Place F)} (h : d.ClassicalSetting S)
    (W : Weights S) (dual : Bool) (c : NonzeroInteger S) :
    d.globalWeight W dual (fieldUnit c) =
      (if dual then d.sDual W (fieldUnit c) else sWeight W (fieldUnit c)) *
        d.normalizedGauss S 1 c.val := by
  rw [d.globalWeight_untwisted h W dual (fieldUnit c),
    dif_pos (show (fieldUnit c : F) ∈ SIntegers S from c.val.property)]
  rfl

/-- Both series of normalized Gauss sums in the untwisted S-integer identity
converge absolutely for admissible test weights. -/
theorem summable_untwistedGauss {S : Finset (Place F)} (h : d.ClassicalSetting S)
    (W : Weights S) (hW : Admissible W) (dual : Bool) :
    Summable (fun c : NonzeroInteger S =>
      ‖(if dual then d.sDual W (fieldUnit c) else sWeight W (fieldUnit c)) *
        d.normalizedGauss S 1 c.val‖) := by
  have line := (d.lineSummation S h.good).exists.choose_spec W hW
  have hs : Summable (fun c => ‖d.globalWeight W dual c‖) := by
    cases dual
    · exact line.1
    · exact line.2.1
  exact (hs.comp_injective (fieldUnit_injective (S := S))).congr
    (fun c => congrArg norm (d.globalWeight_integer h W dual c))

private theorem tsum_globalWeight_untwisted {S : Finset (Place F)} (h : d.ClassicalSetting S)
    (W : Weights S) (dual : Bool) :
    (∑' c : Fˣ, d.globalWeight W dual c) =
      ∑' c : NonzeroInteger S, (if dual then d.sDual W (fieldUnit c) else sWeight W (fieldUnit c)) *
        d.normalizedGauss S 1 c.val := by
  have hs : Function.support (d.globalWeight W dual) ⊆ Set.range (fieldUnit (S := S)) := by
    intro x hx
    by_cases hxS : (x : F) ∈ SIntegers S
    · exact ⟨⟨⟨x,hxS⟩,fun hz => x.ne_zero (congrArg Subtype.val hz)⟩,Units.ext rfl⟩
    · apply (hx _).elim
      rw [d.globalWeight_untwisted h W dual x,dif_neg hxS,mul_zero]
  rw [← fieldUnit_injective.tsum_eq hs]
  exact tsum_congr (d.globalWeight_integer h W dual)

/-- The untwisted S-integer formula preceding Theorem 10.34. -/
theorem untwistedGaussSummation {S : Finset (Place F)} (h : d.ClassicalSetting S)
    (W : Weights S) (hW : Admissible W) :
    let ρ := (d.lineSummation S h.good).exists.choose
    (∑' c : NonzeroInteger S, sWeight W (fieldUnit c) * d.normalizedGauss S 1 c.val) =
      (∑' c : NonzeroInteger S, d.sDual W (fieldUnit c) * d.normalizedGauss S 1 c.val) +
        ∑ᶠ β, ρ β * d.moment W β := by
  have he := ((d.lineSummation S h.good).exists.choose_spec W hW).2.2
  rw [d.tsum_globalWeight_untwisted h W false, d.tsum_globalWeight_untwisted h W true] at he
  exact he

/-- Theorem 10.34. The primes of the conductor determine whether the main term occurs. -/
theorem twistedGaussSummation {S : Finset (Place F)} (h : d.ClassicalSetting S)
    (f b : NonzeroInteger S) (T : Twist (n := n) S f) (coprime : IsCoprime b.val f.val)
    (W : Weights S) (hW : Admissible W) :
    ‖d.epsilon T (fieldUnit b)‖ = 1 ∧
    (∑' c : NonzeroInteger S, sWeight W (fieldUnit c) * twistValue T (fieldUnit c) *
      d.normalizedGauss S b.val c.val) =
    d.epsilon T (fieldUnit b) * (∑' c : NonzeroInteger S,
      d.sDual (fun v x => W v x * d.symbol v.val x (atPlace _ (fieldUnit b)))
        (fieldUnit c / (fieldUnit b * fieldUnit f ^ (n-1))) *
      conj (twistValue T (fieldUnit c)) * d.residue S (fieldUnit c) (fieldUnit f) *
      d.residue S (fieldUnit f) (fieldUnit c) * d.normalizedGauss S b.val c.val) +
      (if T.primes.card = 0 then d.mainTerm h b W else 0) := by sorry

/-- Every embedding sends the two square roots of unity to the same signs. -/
def quadraticDatum : Datum F 2 := by
  let e := (Classical.arbitrary (InfinitePlace F)).embedding
  exact { root := -1
          primitive := IsPrimitiveRoot.neg_one 0 (by decide)
          embedding := (Units.map e.toMonoidHom).comp (rootsOfUnity 2 F).subtype
          injective := (Units.map_injective e.injective).comp Subtype.val_injective
          character := d.character }

/-- Corollary 10.40. The quadratic datum uses the same number field;
the quadratic Hilbert symbol has a unique complex embedding. -/
theorem quadraticDual {S : Finset (Place F)} (hS : d.ClassicalSetting S)
    (odd : Odd n)
    (awayTwo : ∀ p : Prime F, Sum.inr p ∉ S → Odd p.asIdeal.absNorm)
    (h : NonzeroInteger S) (nonunit : ¬ IsUnit h.val) (squarefree : Squarefree h.val) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ W : Weights S, Admissible W →
      (∑' c : NonzeroInteger S, sWeight W (fieldUnit c) * d.quadraticDatum.residue S (fieldUnit c) (fieldUnit h) *
        d.residue S (fieldUnit c) (fieldUnit h) ^ 2 * d.normalizedGauss S 1 c.val) =
      ε * ∑' c : NonzeroInteger S, d.sDual W (fieldUnit c / fieldUnit h ^ (n-1)) *
        d.sSymbol S (fieldUnit h) (fieldUnit c) * d.quadraticDatum.residue S (fieldUnit c) (fieldUnit h) *
        d.normalizedGauss S 1 c.val := by sorry

/-- In degree three the twist on the left of Corollary 10.40 is the
sextic residue symbol for the compatible embedding of μ₆. -/
theorem sextic_to_quadratic (a : Datum F 3) (six : Datum F 6)
    (compatible : ∀ z : Mu F 3,
      six.embedding ⟨z.val, rootsOfUnity_le_of_dvd (by decide : 3 ∣ 6) z.property⟩ = a.embedding z)
    {S : Finset (Place F)} (hS : a.ClassicalSetting S)
    (awayTwo : ∀ p : Prime F, Sum.inr p ∉ S → Odd p.asIdeal.absNorm)
    (h : NonzeroInteger S) (nonunit : ¬ IsUnit h.val) (squarefree : Squarefree h.val) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ W : Weights S, Admissible W →
      (∑' c : NonzeroInteger S, sWeight W (fieldUnit c) * six.residue S (fieldUnit c) (fieldUnit h) *
        a.normalizedGauss S 1 c.val) =
      ε * ∑' c : NonzeroInteger S, a.sDual W (fieldUnit c / fieldUnit h ^ 2) *
        a.sSymbol S (fieldUnit h) (fieldUnit c) * a.quadraticDatum.residue S (fieldUnit c) (fieldUnit h) *
        a.normalizedGauss S 1 c.val := by sorry

end MetaplecticPoisson.Datum
