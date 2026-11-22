import MetaplecticSummation.Jacquet.ArchWeak
import MetaplecticSummation.Jacquet.DegreeOne

noncomputable section
namespace MetaplecticPoisson
namespace Datum

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped ContDiff Topology
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [hn : NeZero n] (d : Datum F n)

theorem jacquet_fourier_test (v : Place F) (Φ : d.schwartz v) (h : TestWeight v (d.jacquet v Φ)) :
    d.jacquet v (d.fourier v Φ) = d.dualWeight v (d.jacquet v Φ) := by
  cases v with
  | inr p => exact d.finite_jacquet_fourier_test p Φ h
  | inl w =>
    obtain ⟨Ξ,hJ,hF,hi⟩ := d.exists_integrable_jacquet_representative (.inl w) Φ
    simpa only [hJ,hF] using d.arch_jacquet_fourier_of_integrable_chart w Ξ (hJ ▸ h) hi

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

open Set in
open Classical in
/-- The original adelic weight has finite support on nonzero rational points:
the tests at S have compact support and each basic Jacquet factor outside S
vanishes on nonintegral elements. -/
theorem globalWeight_finiteSupport {S : Finset (Place F)} (hS : d.GoodOutside S)
    (W : Weights S) (hW : Admissible W) : Function.HasFiniteSupport (d.globalWeight W false) := by
  let factor (c : Fˣ) (v : Place F) := if hv : v ∈ S then W ⟨v,hv⟩ (atPlace v c)
    else d.jacquet v (d.basic v) (atPlace v c)
  have product (c : Fˣ) : d.globalWeight W false c = ∏ᶠ v, factor c v := by
    simp [globalWeight,factor]
  have finite (c : Fˣ) : Function.HasFiniteMulSupport (factor c) := eventually_cofinite.mp (by
    apply eventually_place_of_finite
    have hout : ∀ᶠ p : Prime F in cofinite, Sum.inr p ∉ S :=
      eventually_cofinite.mpr (by simp only [not_not]; exact S.finite_toSet.preimage Sum.inr_injective.injOn)
    filter_upwards [hout,eventually_diagonal_norm_one c.ne_zero,d.eventually_selfDual_volume_one] with p hp hc hv
    obtain ⟨ht,hψ⟩ := hS.2.2 p hp
    have he := d.jacquet_basic_unit p ht hψ (atPlace (.inr p) c) hc
    simp only [factor,dif_neg hp,he,hv,Complex.ofReal_one])
  have bound (v : S) : ∃ R : ℝ, 0 < R ∧ ∀ x ∈ tsupport (W v), modulus F v.val x.val ≤ R := by
    have hc : Continuous (modulus F v.val) := by
      rcases v with ⟨w,_⟩
      cases w with
      | inl w => exact continuous_norm.pow _
      | inr p => exact continuous_norm
    obtain ⟨C,hC⟩ := (hW v).1.bddAbove_image (hc.comp Units.continuous_val).continuousOn
    exact ⟨max 1 C,zero_lt_one.trans_le (le_max_left ..),
      fun x hx => (hC ⟨x,hx,rfl⟩).trans (le_max_right ..)⟩
  choose R hR hbound using bound
  let r (v : Place F) := if h : v ∈ S then R ⟨v,h⟩ else 1
  have box {c : Fˣ} (hc : d.globalWeight W false c ≠ 0) (v : Place F) :
      modulus F v (diagonal F v c.val) ≤ r v := by
    have hn : factor c v ≠ 0 := fun hz => hc ((product c).trans (finprod_eq_zero _ v hz (finite c)))
    by_cases hv : v ∈ S
    · rw [show r v = _ from dif_pos hv]
      apply hbound ⟨v,hv⟩ (atPlace v c) (subset_tsupport _ ?_)
      change W ⟨v,hv⟩ (atPlace v c) ≠ 0
      simpa only [factor,dif_pos hv] using hn
    · cases v with
      | inl w => exact (hv (hS.2.1 w)).elim
      | inr p =>
        rw [show r (.inr p) = 1 from dif_neg hv]
        by_contra! h
        exact hn ((dif_neg hv).trans (d.jacquet_basic_nonintegral p (hS.2.2 p hv).1 _ h))
  obtain ⟨C,_,hC⟩ := rational_box_count (F := F)
  obtain ⟨m,hm⟩ := exists_nat_gt (C * ∏ᶠ v, r v)
  by_contra hinf
  obtain ⟨T,hT,hcard⟩ := Set.Infinite.exists_subset_card_eq hinf m
  let e : Fˣ ↪ F := ⟨Units.val,Units.val_injective⟩
  have outside : ∀ᶠ v in cofinite, v ∉ S := S.finite_toSet.compl_mem_cofinite
  have count := hC r (fun v => by
    dsimp only [r]
    split <;> first | apply hR | exact zero_lt_one)
    (outside.mono fun v hv => dif_neg hv) (T.map e) (by
      intro x hx
      obtain ⟨c,hc,rfl⟩ := Finset.mem_map.mp hx
      exact ⟨c.ne_zero,box (hT hc)⟩)
  simp only [Finset.card_map,hcard] at count
  exact (not_lt_of_ge count) hm

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
    a.LineFormula S (fun _ => 0) := by
  classical
  intro W hW
  have dual (c : Fˣ) : a.globalWeight W true c = a.globalWeight W false c⁻¹ := by
    unfold globalWeight
    apply finprod_congr
    intro v
    by_cases hv : v ∈ S
    · simpa only [dif_pos hv,Bool.false_eq_true,ite_true,ite_false,atPlace,map_inv] using
        a.dualWeight_degree_one v (hW ⟨v,hv⟩) (atPlace v c)
    · cases v with
      | inl w => exact (hv (hS.2.1 w)).elim
      | inr p =>
        simpa only [dif_neg hv,Bool.false_eq_true,ite_true,ite_false,atPlace,map_inv] using
          a.jacquet_basic_dual_degree_one p (atPlace (.inr p) c)
  have hs : Summable (fun c => ‖a.globalWeight W false c‖) := by
    apply summable_of_hasFiniteSupport
    apply (a.globalWeight_finiteSupport hS W hW).subset
    intro x hx h
    exact hx (by simp [h])
  refine ⟨hs,?_,?_⟩
  · exact (hs.comp_injective (Equiv.inv Fˣ).injective).congr (fun c => congrArg norm (dual c).symm)
  · simp only [zero_mul,finsum_zero,add_zero,dual]
    exact ((Equiv.inv Fˣ).tsum_eq (a.globalWeight W false)).symm

end Datum
end MetaplecticPoisson
