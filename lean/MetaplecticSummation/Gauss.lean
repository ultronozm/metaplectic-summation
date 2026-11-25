import MetaplecticSummation.TwistedGaussFactors
import MetaplecticSummation.SexticResidue
import MetaplecticSummation.QuadraticTwist

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

/-- Restrict the original adelic sum to the nonzero S-integers and recover the
normalizing factor for the scaled additive character. -/
theorem tsum_twistedGauss_original {S : Finset (Place F)} (h : d.ClassicalSetting S)
    {f : NonzeroInteger S} (b : NonzeroInteger S) (T : Twist (n := n) S f)
    (coprime : IsCoprime b.val f.val) (W : Weights S) :
    (∑' c : Fˣ, (d.scaled (fieldUnit b)).globalWeight (T.weights W) false c) =
      (Real.sqrt (sNorm S (fieldUnit b)) : ℂ)⁻¹ * ∑' c : NonzeroInteger S,
        sWeight W (fieldUnit c) * twistValue T (fieldUnit c) * d.normalizedGauss S b.val c.val := by
  let g := (d.scaled (fieldUnit b)).globalWeight (T.weights W) false
  have hs : Function.support g ⊆ Set.range (fieldUnit (S := S)) := by
    intro c hc
    by_cases hi : (c : F) ∈ SIntegers S
    · exact ⟨⟨⟨c,hi⟩,fun hz => c.ne_zero (congrArg Subtype.val hz)⟩,Units.ext rfl⟩
    · apply (hc _).elim
      simp only [g,d.twistedGauss_original_factor h b T coprime W c,dif_neg hi,mul_zero]
  rw [← fieldUnit_injective.tsum_eq hs, ← tsum_mul_left]
  apply tsum_congr
  intro c
  dsimp only [g]
  rw [d.twistedGauss_original_factor h b T coprime W (fieldUnit c),
    dif_pos (show (fieldUnit c : F) ∈ SIntegers S from c.val.property)]
  ring_nf
  rfl

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

/-- The untwisted S-integer formula preceding Theorem 10.33. -/
theorem untwistedGaussSummation {S : Finset (Place F)} (h : d.ClassicalSetting S)
    (W : Weights S) (hW : Admissible W) :
    let ρ := (d.lineSummation S h.good).exists.choose
    (∑' c : NonzeroInteger S, sWeight W (fieldUnit c) * d.normalizedGauss S 1 c.val) =
      (∑' c : NonzeroInteger S, d.sDual W (fieldUnit c) * d.normalizedGauss S 1 c.val) +
        ∑ᶠ β, ρ β * d.moment W β := by
  have he := ((d.lineSummation S h.good).exists.choose_spec W hW).2.2
  rw [d.tsum_globalWeight_untwisted h W false, d.tsum_globalWeight_untwisted h W true] at he
  exact he

/-- The dual adelic sum after division of the index by the frequency and
conductor powers and restriction to nonzero S-integers. -/
theorem tsum_twistedGauss_dual {S : Finset (Place F)} (h : d.ClassicalSetting S)
    {f : NonzeroInteger S} (b : NonzeroInteger S) (T : Twist (n := n) S f)
    (coprime : IsCoprime b.val f.val) (W : Weights S) (hW : Admissible W) :
    (∑' c : Fˣ, (d.scaled (fieldUnit b)).globalWeight (T.weights W) true c) =
      (Real.sqrt (sNorm S (fieldUnit b)) : ℂ)⁻¹ * (d.epsilon T (fieldUnit b) * ∑' c : NonzeroInteger S,
        d.sDual (fun v x => W v x * d.symbol v.val x (atPlace _ (fieldUnit b)))
          (fieldUnit c / (fieldUnit b * fieldUnit f^(n-1))) *
        conj (twistValue T (fieldUnit c)) * d.residue S (fieldUnit c) (fieldUnit f) *
        d.residue S (fieldUnit f) (fieldUnit c) * d.normalizedGauss S b.val c.val) := by
  let g := (d.scaled (fieldUnit b)).globalWeight (T.weights W) true
  let e := Equiv.divRight (fieldUnit b^n * fieldUnit f^(n-1))
  have hs : Function.support (fun c => g (e c)) ⊆ Set.range (fieldUnit (S := S)) := by
    intro c hc
    by_cases hi : (c : F) ∈ SIntegers S
    · exact ⟨⟨⟨c,hi⟩,fun hz => c.ne_zero (congrArg Subtype.val hz)⟩,Units.ext rfl⟩
    · apply (hc _).elim
      exact (d.twistedGauss_dual_factor h b T coprime W hW c).trans (by simp [hi])
  change (∑' c, g c) = _
  rw [← e.tsum_eq g, ← fieldUnit_injective.tsum_eq hs, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro c
  have he := d.twistedGauss_dual_factor h b T coprime W hW (fieldUnit c)
  rw [dif_pos (show (fieldUnit c : F) ∈ SIntegers S from c.val.property)] at he
  apply he.trans
  ring_nf
  rfl

private theorem globalWeight_empty_twist {S : Finset (Place F)} {f : NonzeroInteger S}
    (T : Twist (n := n) S f) (empty : T.primes = ∅) (W : Weights S) (dual : Bool) (c : Fˣ) :
    d.globalWeight (T.weights W) dual c = d.globalWeight W dual c := by
  unfold globalWeight
  apply finprod_congr
  intro v
  have he : T.places = S := by simp [Twist.places,empty]
  by_cases hv : v ∈ S
  · have ht : v ∈ T.places := he.symm ▸ hv
    have hw : T.weights W ⟨v,ht⟩ = W ⟨v,hv⟩ := by
      cases v with
      | inl w => rfl
      | inr p => exact dif_pos hv
    simp only [hv,ht,dif_pos,hw]
  · rw [dif_neg (show v ∉ T.places from he.symm ▸ hv), dif_neg hv]

omit hn in
theorem sNorm_pos {S : Finset (Place F)} (b : Fˣ) : 0 < sNorm S (b : F) := by
  apply Finset.prod_pos
  intro v _
  apply lt_of_le_of_ne _ (modulus_ne_zero v (atPlace v b)).symm
  cases v <;> simp [modulus]

/-- Absolute convergence of the two S-integer series in the twisted formula. -/
theorem summable_twistedGauss {S : Finset (Place F)} (h : d.ClassicalSetting S)
    {f : NonzeroInteger S} (b : NonzeroInteger S) (T : Twist (n := n) S f)
    (coprime : IsCoprime b.val f.val) (W : Weights S) (hW : Admissible W) :
    Summable (fun c : NonzeroInteger S => ‖sWeight W (fieldUnit c) * twistValue T (fieldUnit c) *
      d.normalizedGauss S b.val c.val‖) ∧
    Summable (fun c : NonzeroInteger S => ‖d.sDual (fun v x => W v x * d.symbol v.val x (atPlace _ (fieldUnit b)))
        (fieldUnit c / (fieldUnit b * fieldUnit f ^ (n-1))) *
      conj (twistValue T (fieldUnit c)) * d.residue S (fieldUnit c) (fieldUnit f) *
      d.residue S (fieldUnit f) (fieldUnit c) * d.normalizedGauss S b.val c.val‖) := by
  let m : ℂ := (Real.sqrt (sNorm S (fieldUnit b)) : ℂ)⁻¹
  have hm : ‖m‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (sNorm_pos _)).ne'))
  let db := d.scaled (fieldUnit b)
  have line := (db.lineSummation T.places (T.good_places (d.scaled_good h b))).exists.choose_spec
    (T.weights W) (T.admissible_weights W hW)
  constructor
  · apply (summable_mul_left_iff hm).mp
    apply (line.1.comp_injective (fieldUnit_injective (S := S))).congr
    intro c
    dsimp only [Function.comp_def,db]
    rw [d.twistedGauss_original_factor h b T coprime W (fieldUnit c),
      dif_pos (show (fieldUnit c : F) ∈ SIntegers S from c.val.property), ← norm_mul]
    apply congrArg norm
    change _ * (m * d.normalizedGauss S b.val c.val) = _
    ring
  · let e := Equiv.divRight (fieldUnit b^n * fieldUnit f^(n-1))
    have he := d.epsilon_norm h f b T coprime
    apply (summable_mul_left_iff hm).mp
    apply (line.2.1.comp_injective (e.injective.comp (fieldUnit_injective (S := S)))).congr
    intro c
    have hc := d.twistedGauss_dual_factor h b T coprime W hW (fieldUnit c)
    rw [dif_pos (show (fieldUnit c : F) ∈ SIntegers S from c.val.property)] at hc
    apply (congrArg norm hc).trans
    simp only [norm_mul,he,one_mul,m]
    ring_nf
    rfl

/-- Theorem 10.33. The primes of the conductor determine whether the main term occurs. -/
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
      (if T.primes.card = 0 then d.mainTerm h b W else 0) := by
  refine ⟨d.epsilon_norm h f b T coprime,?_⟩
  let db := d.scaled (fieldUnit b)
  let m : ℂ := Real.sqrt (sNorm S (fieldUnit b))
  have hm : m ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (sNorm_pos _)).ne'
  have leftSum := d.tsum_twistedGauss_original h b T coprime W
  have rightSum := d.tsum_twistedGauss_dual h b T coprime W hW
  by_cases empty : T.primes = ∅
  · have line := ((db.lineSummation S (d.scaled_good h b)).exists.choose_spec W hW).2.2
    have equivWeight (dual : Bool) :
        db.globalWeight (T.weights W) dual = db.globalWeight W dual :=
      funext fun c => db.globalWeight_empty_twist T empty W dual c
    rw [← equivWeight false,← equivWeight true,leftSum,rightSum] at line
    simp only [empty,Finset.card_empty,if_true,mainTerm]
    have he := congrArg (m * ·) line
    simpa only [mul_add,← mul_assoc,mul_inv_cancel₀ hm,one_mul,m,db] using he
  · obtain ⟨_,_,line⟩ := d.twisted_lineSummation h b T (Finset.nonempty_iff_ne_empty.mpr empty) W hW
    rw [leftSum,rightSum] at line
    rw [if_neg (fun he => empty (Finset.card_eq_zero.mp he)),add_zero]
    exact mul_left_cancel₀ (inv_ne_zero hm) line

/-- Every embedding sends the two square roots of unity to the same signs. -/
def quadraticDatum : Datum F 2 := by
  let e := (Classical.arbitrary (InfinitePlace F)).embedding
  exact { root := -1
          primitive := IsPrimitiveRoot.neg_one 0 (by decide)
          embedding := (Units.map e.toMonoidHom).comp (rootsOfUnity 2 F).subtype
          injective := (Units.map_injective e.injective).comp Subtype.val_injective
          character := d.character }

/-- Corollary 10.39. The quadratic datum uses the same number field;
the quadratic Hilbert symbol has a unique complex embedding. -/
theorem quadraticDual {S : Finset (Place F)} (hS : d.ClassicalSetting S)
    (odd : Odd n)
    (awayTwo : ∀ p : Prime F, Sum.inr p ∉ S → Odd p.asIdeal.absNorm)
    (h : NonzeroInteger S) (nonunit : ¬ IsUnit h.val) (squarefree : Squarefree h.val) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ W : Weights S, Admissible W →
      Summable (fun c : NonzeroInteger S => ‖sWeight W (fieldUnit c) *
        d.quadraticDatum.residue S (fieldUnit c) (fieldUnit h) *
        d.residue S (fieldUnit c) (fieldUnit h) ^ 2 * d.normalizedGauss S 1 c.val‖) ∧
      Summable (fun c : NonzeroInteger S => ‖d.sDual W (fieldUnit c / fieldUnit h ^ (n-1)) *
        d.sSymbol S (fieldUnit h) (fieldUnit c) * d.quadraticDatum.residue S (fieldUnit c) (fieldUnit h) *
        d.normalizedGauss S 1 c.val‖) ∧
      (∑' c : NonzeroInteger S, sWeight W (fieldUnit c) * d.quadraticDatum.residue S (fieldUnit c) (fieldUnit h) *
        d.residue S (fieldUnit c) (fieldUnit h) ^ 2 * d.normalizedGauss S 1 c.val) =
      ε * ∑' c : NonzeroInteger S, d.sDual W (fieldUnit c / fieldUnit h ^ (n-1)) *
        d.sSymbol S (fieldUnit h) (fieldUnit c) * d.quadraticDatum.residue S (fieldUnit c) (fieldUnit h) *
        d.normalizedGauss S 1 c.val := by
  let one : NonzeroInteger S := ⟨1,one_ne_zero⟩
  let T := d.quadraticTwist d.quadraticDatum hS odd awayTwo h nonunit squarefree
  have h1 : fieldUnit one = 1 := Units.ext rfl
  have cop : IsCoprime one.val h.val := isCoprime_one_left
  refine ⟨d.epsilon T (fieldUnit one),d.epsilon_norm hS h one T cop,fun W hW => ?_⟩
  have hT : T.primes.card ≠ 0 := (Finset.card_pos.mpr
    (d.quadraticTwist_nonempty d.quadraticDatum hS odd awayTwo h nonunit squarefree)).ne'
  have idW : (fun (v : S) x => W v x * d.symbol v.val x (atPlace _ (fieldUnit one))) = W := by
    funext v x
    rw [h1,show atPlace v.val (1 : Fˣ) = 1 from map_one _]
    change W v x * ((d.unitPairing v.val x 1 : ℂˣ) : ℂ) = W v x
    rw [map_one,Units.val_one,mul_one]
  have he := (d.twistedGaussSummation hS h one T cop W hW).2
  have hs := d.summable_twistedGauss hS one T cop W hW
  rw [if_neg hT,add_zero,idW] at he
  rw [idW] at hs
  simp only [h1,one_mul] at he hs ⊢
  have eL (c : NonzeroInteger S) : sWeight W (fieldUnit c) * twistValue T (fieldUnit c) *
      d.normalizedGauss S 1 c.val = sWeight W (fieldUnit c) *
      d.quadraticDatum.residue S (fieldUnit c) (fieldUnit h) *
      d.residue S (fieldUnit c) (fieldUnit h) ^ 2 * d.normalizedGauss S 1 c.val := by
    rw [show twistValue T (fieldUnit c) = _ from
      d.quadraticTwist_value d.quadraticDatum hS odd awayTwo h nonunit squarefree (fieldUnit c)]
    ring
  have eR (c : NonzeroInteger S) : d.sDual W (fieldUnit c / fieldUnit h ^ (n-1)) *
      conj (twistValue T (fieldUnit c)) * d.residue S (fieldUnit c) (fieldUnit h) *
      d.residue S (fieldUnit h) (fieldUnit c) * d.normalizedGauss S 1 c.val =
      d.sDual W (fieldUnit c / fieldUnit h ^ (n-1)) *
      d.sSymbol S (fieldUnit h) (fieldUnit c) * d.quadraticDatum.residue S (fieldUnit c) (fieldUnit h) *
      d.normalizedGauss S 1 c.val := by
    have H := d.quadraticTwist_dual_value d.quadraticDatum hS odd awayTwo h nonunit squarefree c
    change conj (twistValue T _) * _ * _ = _ at H
    linear_combination d.sDual W (fieldUnit c / fieldUnit h ^ (n-1)) *
      d.normalizedGauss S 1 c.val * H
  refine ⟨hs.1.congr fun c => by rw [eL c],hs.2.congr fun c => by rw [eR c],?_⟩
  exact (tsum_congr eL).symm.trans (he.trans (congrArg _ (tsum_congr eR)))

/-- In degree three the twist on the left of Corollary 10.39 is the
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
        a.normalizedGauss S 1 c.val := by
  obtain ⟨ε,hε,H⟩ := a.quadraticDual hS (by decide) awayTwo h nonunit squarefree
  refine ⟨ε,hε,fun W hW => ?_⟩
  rw [← (H W hW).2.2]
  apply tsum_congr
  intro c
  rw [sextic_residue six a a.quadraticDatum compatible hS.good awayTwo (fieldUnit c) h]
  ring

end MetaplecticPoisson.Datum
