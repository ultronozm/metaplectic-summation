import MetaplecticSummation.Poisson
import MetaplecticSummation.RayFourier

noncomputable section
namespace MetaplecticPoisson
namespace Datum

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped ContDiff Topology
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [hn : NeZero n] (d : Datum F n)

abbrev Weight (v : Place F) := (LocalField F v)ˣ → ℂ

def jacquet (v : Place F) (Φ : d.schwartz v) (c : (LocalField F v)ˣ) : ℂ :=
  ∫ y, Φ.val.1 c y * d.character.localValue F v (-y / (c : LocalField F v))
    ∂(selfDual F d.character v)

def lineIntegral (v : Place F) (f : Weight v) : ℂ := by
  classical
  exact ∫ x, if h : x ≠ 0 then f (Units.mk0 x h) / (modulus F v x : ℂ) else 0
    ∂(selfDual F d.character v)

omit hn in
theorem lineIntegral_const_mul (v : Place F) (z : ℂ) (f : Weight v) :
    d.lineIntegral v (fun x => z * f x) = z * d.lineIntegral v f := by
  classical
  unfold lineIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  split_ifs <;> ring

omit hn in
/-- Multiplicative Haar integration is invariant under translation by a unit. -/
theorem lineIntegral_mul (v : Place F) (u : (LocalField F v)ˣ) (f : Weight v) :
    d.lineIntegral v (fun x => f (u*x)) = d.lineIntegral v f := by
  classical
  let g (w : Weight v) (x : LocalField F v) : ℂ :=
    if h : x ≠ 0 then w (Units.mk0 x h) / (modulus F v x : ℂ) else 0
  let m : ℂ := modulus F v u.val
  have hm : m ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v u)
  have hmod (x : LocalField F v) : modulus F v (u.val*x) = modulus F v u.val * modulus F v x := by
    cases v <;> simp [modulus,norm_mul,mul_pow]
  have he (x : LocalField F v) : g f (u.val*x) = g (fun a => f (u*a)) x / m := by
    by_cases hx : x = 0
    · simp [g,hx]
    · have hux := mul_ne_zero u.ne_zero hx
      simp only [g,dif_pos hux,dif_pos hx,hmod,Complex.ofReal_mul]
      rw [show Units.mk0 (u.val*x) hux = u * Units.mk0 x hx from Units.ext rfl]
      ring
  have h := d.integral_local_mul v u (g f)
  dsimp only at h
  simp_rw [he] at h
  rw [integral_div] at h
  exact (div_left_inj' hm).mp h

def archSmooth {K L : Type} [Field K] [NormedField L] [NormedAlgebra ℝ L]
    (e : K ≃+* L) (W : Kˣ → ℂ) : Prop := by
  classical
  exact ContDiffOn ℝ ∞ (fun x => if h : e.symm x ≠ 0 then W (Units.mk0 _ h) else 0) {0}ᶜ

def TestWeight (v : Place F) (W : Weight v) : Prop :=
  HasCompactSupport W ∧ (by
    classical
    cases v with
    | inr p => exact IsLocallyConstant W
    | inl w =>
      by_cases h : w.IsReal
      · exact archSmooth (InfinitePlace.Completion.ringEquivRealOfIsReal h) W
      · exact archSmooth (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp h)) W)

def kernelIntegral (v : Place F) (W : Weight v) (c : (LocalField F v)ˣ) (t : LocalField F v) :=
  d.lineIntegral v fun x => W x * d.symbol v x (-c) *
    d.character.localValue F v (-(t ^ n) / ((c : LocalField F v) * x))

/-- Proposition 10.8 at λ = 1, used for compactly supported test weights. -/
def dualWeight (v : Place F) (W : Weight v) (c : (LocalField F v)ˣ) : ℂ :=
  (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ *
    ∫ t, d.character.localValue F v t * d.kernelIntegral v W c t ∂(selfDual F d.character v)

theorem jacquet_test_lift (v : Place F) (W : Weight v) (h : TestWeight v W) :
    ∃ Φ : d.schwartz v, Φ.val ∈ d.testSet v ∧ d.jacquet v Φ = W := by sorry

theorem jacquet_fourier_test (v : Place F) (Φ : d.schwartz v) (h : TestWeight v (d.jacquet v Φ)) :
    d.jacquet v (d.fourier v Φ) = d.dualWeight v (d.jacquet v Φ) := by sorry

theorem root_fourier (v : Place F) (W : Weight v) (_h : TestWeight v W)
    (c lam : (LocalField F v)ˣ) :
    d.dualWeight v W (c * lam ^ n) =
      (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹ * (modulus F v lam : ℂ) *
        ∫ t, d.kernelIntegral v W c t * d.character.localValue F v (t * lam)
          ∂(selfDual F d.character v) := by
  let ψ := d.character.localValue F v
  let m : ℂ := modulus F v lam.val
  have hm : m ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_ne_zero v lam)
  have symb (x : (LocalField F v)ˣ) :
      d.symbol v x (-(c*lam^n)) = d.symbol v x (-c) := by
    change ((d.unitPairing v x (-(c*lam^n))).val) = _
    rw [← neg_mul, map_mul, map_pow, d.unitPairing_pow, mul_one]
    rfl
  have kernel (t : LocalField F v) :
      d.kernelIntegral v W (c*lam^n) (lam.val*t) = d.kernelIntegral v W c t := by
    unfold kernelIntegral
    congr 1
    funext x
    rw [symb, Units.val_mul, Units.val_pow_eq_pow_val, mul_pow]
    congr 2
    field_simp
  have he := d.integral_local_mul v lam (fun t => ψ t * d.kernelIntegral v W (c*lam^n) t)
  dsimp only at he
  simp_rw [kernel,mul_comm lam.val _,mul_comm (ψ (_ * lam.val)) _] at he
  unfold dualWeight
  rw [← (eq_div_iff hm).mp he]
  ring

def GoodOutside (S : Finset (Place F)) : Prop :=
  S.Nonempty ∧ (∀ w, Sum.inl w ∈ S) ∧ ∀ p : HeightOneSpectrum (𝓞 F), Sum.inr p ∉ S →
    p.asIdeal.absNorm.Coprime n ∧ ∀ x : LocalField F (.inr p), ‖x‖ ≤ 1 →
      d.character.localValue F (.inr p) x = 1

/-- The hypotheses of the global line formula hold away from a finite set of places. -/
theorem exists_goodOutside : ∃ S : Finset (Place F), d.GoodOutside S := by
  classical
  let good (p : HeightOneSpectrum (𝓞 F)) := p.asIdeal.absNorm.Coprime n ∧
    ∀ x : LocalField F (.inr p), ‖x‖ ≤ 1 → d.character.localValue F (.inr p) x = 1
  have hgood : ∀ᶠ p in Filter.cofinite, good p :=
    (eventually_tame (F := F) (n := n)).and (eventually_trivial_on_integers d.character)
  have hbad : {p | ¬ good p}.Finite := hgood
  let S : Finset (Place F) := Finset.univ.image Sum.inl ∪ hbad.toFinset.image Sum.inr
  have arch (w : InfinitePlace F) : Sum.inl w ∈ S := Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ w))
  refine ⟨S, ⟨_, arch (Classical.arbitrary _)⟩, arch, fun p hp => ?_⟩
  by_contra h
  exact hp (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hbad.mem_toFinset.mpr h)))

abbrev Weights (S : Finset (Place F)) := (v : S) → Weight v.val
abbrev Admissible {S : Finset (Place F)} (W : Weights S) := ∀ v, TestWeight v.val (W v)
abbrev PowerClass (n : ℕ) (v : Place F) := (LocalField F v)ˣ ⧸ (powMonoidHom n :
  (LocalField F v)ˣ →* (LocalField F v)ˣ).range
abbrev Classes (n : ℕ) (S : Finset (Place F)) := (v : S) → PowerClass n v.val

include hn in
theorem finite_power_classes (v : Place F) : Finite (PowerClass n v) := by
  cases v with
  | inl w =>
    letI : NontriviallyNormedField w.Completion := {
      non_trivial := by
        refine ⟨algebraMap F w.Completion (2 : F), ?_⟩
        have h := InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm (2 : F))
        change 1 < ‖algebraMap F w.Completion (2 : F)‖
        rw [show ‖algebraMap F w.Completion (2 : F)‖ = w (2 : F) from h]
        simpa only [← Nat.cast_ofNat (R := F) (n := 2), w.map_natCast] using (by norm_num : (1:ℝ) < (2:ℕ)) }
    letI : ProperSpace w.Completion := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
    letI : CharZero w.Completion := charZero_of_injective_ringHom (algebraMap F w.Completion).injective
    exact finite_unit_power_quotient (K := w.Completion) n (Nat.cast_ne_zero.mpr (NeZero.ne n))
  | inr p =>
    letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
    letI : ProperSpace (p.adicCompletion F) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
    letI : CharZero (p.adicCompletion F) := charZero_of_injective_ringHom (algebraMap F (p.adicCompletion F)).injective
    exact finite_unit_power_quotient (K := p.adicCompletion F) n (Nat.cast_ne_zero.mpr (NeZero.ne n))

def moment {S : Finset (Place F)} (W : Weights S) (β : Classes n S) : ℂ := by
  classical
  exact ∏ v : S, d.lineIntegral v.val fun x =>
    if (QuotientGroup.mk x : PowerClass n v.val) = β v then
      W v x * ((modulus F v.val x ^ (1 / (n : ℝ)) : ℝ) : ℂ) else 0

def globalWeight {S : Finset (Place F)} (W : Weights S) (dual : Bool) (c : Fˣ) : ℂ := by
  classical
  exact ∏ᶠ v, if hv : v ∈ S then
    (if dual then d.dualWeight v (W ⟨v,hv⟩) else W ⟨v,hv⟩) (atPlace v c)
    else d.jacquet v (if dual then d.fourier v (d.basic v) else d.basic v) (atPlace v c)

/-- The constants are chosen once for all test weights. -/
def LineFormula (S : Finset (Place F)) (ρ : Classes n S → ℂ) : Prop :=
  ∀ W : Weights S, Admissible W →
    Summable (fun c => ‖d.globalWeight W false c‖) ∧
    Summable (fun c => ‖d.globalWeight W true c‖) ∧
    (∑' c, d.globalWeight W false c) = (∑' c, d.globalWeight W true c) +
      ∑ᶠ β, ρ β * d.moment W β

theorem lineSummation (S : Finset (Place F)) (hS : d.GoodOutside S) :
    ∃! ρ, d.LineFormula S ρ := by sorry

theorem line_degree_one (a : Datum F 1) (S : Finset (Place F)) (hS : a.GoodOutside S) :
    a.LineFormula S (fun _ => 0) := by sorry

end Datum
end MetaplecticPoisson
