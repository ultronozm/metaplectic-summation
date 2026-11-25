import MetaplecticSummation.FourierCoefficients.Basic
import MetaplecticSummation.FourierCoefficients.LocalFactors
import MetaplecticSummation.Jacquet.ArchWeak
import MetaplecticSummation.Jacquet.DegreeOne
import MetaplecticSummation.Jacquet.PowerAverage

/-! The local Jacquet identities and the adelic weights on the two sides of the line formula. -/
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

theorem globalWeight_original_summable {S : Finset (Place F)} (hS : d.GoodOutside S)
    (W : Weights S) (hW : Admissible W) : Summable (fun c => ‖d.globalWeight W false c‖) := by
  apply summable_of_hasFiniteSupport
  apply (d.globalWeight_finiteSupport hS W hW).subset
  intro x hx h
  exact hx (by simp [h])

/-- The constants are chosen once for all test weights. -/
def LineFormula (S : Finset (Place F)) (ρ : Classes n S → ℂ) : Prop :=
  ∀ W : Weights S, Admissible W →
    Summable (fun c => ‖d.globalWeight W false c‖) ∧
    Summable (fun c => ‖d.globalWeight W true c‖) ∧
    (∑' c, d.globalWeight W false c) = (∑' c, d.globalWeight W true c) +
      ∑ᶠ β, ρ β * d.moment W β

open Classical in
theorem lineFormula_unique {S : Finset (Place F)} {ρ σ : Classes n S → ℂ}
    (hρ : d.LineFormula S ρ) (hσ : d.LineFormula S σ) : ρ = σ := by
  funext α
  obtain ⟨W,hW,hM⟩ := d.exists_moment_single α
  have eval (a : Classes n S → ℂ) : ∑ᶠ β, a β * d.moment W β = a α := by
    rw [finsum_eq_single _ α (fun β hβ => by rw [hM,if_neg hβ,mul_zero]),hM,if_pos rfl,mul_one]
  exact add_left_cancel (by simpa only [eval] using ((hρ W hW).2.2.symm.trans (hσ W hW).2.2))

/-- Lift the weights simultaneously to a pure tensor. Unfolding it and its
Fourier transform gives the two absolutely convergent adelic sums. -/
theorem lineWeights_unfold {S : Finset (Place F)} (W : Weights S) (hW : Admissible W) :
    ∃ Φ : (v : Place F) → d.schwartz v,
      (∀ v : S, (Φ v.val).val ∈ d.testSet v.val ∧ d.jacquet v.val (Φ v.val) = W v) ∧
      (∀ v ∉ S, Φ v = d.basic v) ∧
      (∀ v : S, ∃ β, (Φ v.val).val = d.jacquetLift v.val (W v) β) ∧
      ∀ b : Bool, Summable (fun c => ‖d.globalWeight W b c‖) ∧
        d.coefficient (fun v => if b then d.fourier v (Φ v) else Φ v) 1 =
          ∑' c, d.globalWeight W b c := by
  classical
  choose β hβ using fun v : S => d.exists_jacquetLift_auxiliary v.val
  let L (v : S) : d.schwartz v.val := ⟨d.jacquetLift v.val (W v) (β v),
    Submodule.subset_span (Or.inl ((hβ v).2 _ (hW v)))⟩
  have hT (v : S) : (L v).val ∈ d.testSet v.val := (hβ v).2 _ (hW v)
  have hJ (v : S) : d.jacquet v.val (L v) = W v := d.jacquet_jacquetLift _ _ _ (hβ v).1 (hT v)
  have hF (v : S) : d.jacquet v.val (d.fourier v.val (L v)) = d.dualWeight v.val (W v) :=
    d.jacquetLift_dual v.val (hW v) (hβ v)
  let Φ (v : Place F) := if h : v ∈ S then L ⟨v,h⟩ else d.basic v
  have hout (v) (hv : v ∉ S) : Φ v = d.basic v := dif_neg hv
  refine ⟨Φ,fun v => by simpa only [Φ,dif_pos v.property] using And.intro (hT v) (hJ v),hout,?_,fun b => ?_⟩
  · exact fun v => ⟨β v,by simp only [Φ,dif_pos v.property]; rfl⟩
  let Ψ (v : Place F) := if b then d.fourier v (Φ v) else Φ v
  have he : ∀ᶠ v in cofinite, Ψ v = d.basic v := by
    filter_upwards [S.finite_toSet.compl_mem_cofinite,d.eventually_fourier_basic] with v hv hfix
    simp [Ψ,hout v hv,hfix]
  have eqn (c : Fˣ) : (∏ᶠ v, d.jacquet v (Ψ v) (atPlace v c)) = d.globalWeight W b c := by
    unfold globalWeight
    apply finprod_congr
    intro v
    by_cases hv : v ∈ S
    · cases b
      · simpa only [Ψ,Φ,dif_pos hv,Bool.false_eq_true,ite_false] using congrFun (hJ ⟨v,hv⟩) (atPlace v c)
      · simpa only [Ψ,Φ,dif_pos hv,ite_true] using congrFun (hF ⟨v,hv⟩) (atPlace v c)
    · cases b <;> simp only [Ψ,Φ,dif_neg hv,Bool.false_eq_true,ite_false,ite_true]
  simpa only [eqn] using (d.unfolding Ψ he).2

/-- A zero vector of local moments kills the entire main term, by the
two local vanishing conditions in the Poisson formula. -/
theorem lineSummation_of_zero_moments {S : Finset (Place F)} (W : Weights S) (hW : Admissible W)
    (v : S) (hz : ∀ β, d.classMoment v.val (W v) β = 0) :
    (∑' c, d.globalWeight W false c) = ∑' c, d.globalWeight W true c := by
  classical
  obtain ⟨Φ,hT,hout,hLift,h⟩ := d.lineWeights_unfold W hW
  have hf : ∀ᶠ q in cofinite, Φ q = d.basic q := by
    filter_upwards [S.finite_toSet.compl_mem_cofinite] with q hq
    exact hout q hq
  have zero : d.leading v.val (Φ v.val) = 0 := by
    rcases v with ⟨q,hq⟩
    cases q with
    | inl w => exact d.leading_archTest_eq_zero w _ (hT ⟨_,hq⟩).1
    | inr p => exact d.leading_finiteTest_eq_zero p _ (hT ⟨_,hq⟩).1
  obtain ⟨β,hβ⟩ := hLift v
  have zeroDual : d.leading v.val (d.fourier v.val (Φ v.val)) = 0 := by
    rw [d.leading_fourier_test _ _ (hT v).1,hβ,d.powerAverage_jacquetLift_eq_zero _ _ _ hz]
    have hI : d.intertwiner v.val 0 = 0 := by
      apply Prod.ext <;> funext x y <;> simp [intertwiner,radon]
    rw [hI,smul_zero]
  have e := d.coefficient_eq_fourier_of_local_vanishing Φ hf v.val v.val zero zeroDual 1
  simpa only [Bool.false_eq_true,ite_false,ite_true] using
    ((h false).2.symm.trans (e.trans (h true).2))

end Datum
end MetaplecticPoisson
