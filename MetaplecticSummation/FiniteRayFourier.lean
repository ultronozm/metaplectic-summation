import MetaplecticSummation.FiniteLeading
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Field.Ultra

/-! One-dimensional Fourier transforms of bounded families of Schwartz–Bruhat
functions over a finite completion, as used in §§4 and 8. -/

noncomputable section
namespace MetaplecticPoisson
open Filter Set MeasureTheory Metric
open scoped Topology ENNReal
open Classical

/-- A continuous circle-valued additive character on an ultrametric field
has open kernel: every positive integral multiple stays in the same ball at zero. -/
theorem locallyConstant_addChar {K : Type*} [NormedField K] [IsUltrametricDist K]
    (χ : AddChar K Circle) (hc : Continuous χ) : IsLocallyConstant χ := by
  have h1 : (1 : Circle) ∈ Circle.centeredArc (Real.pi / 2) := by
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  have he : ∀ᶠ x in 𝓝 (0 : K), χ x ∈ Circle.centeredArc (Real.pi / 2) :=
    (hc.tendsto 0).eventually ((Circle.isOpen_centeredArc _).mem_nhds (by simpa using h1))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp he
  have hk (x : K) (hx : ‖x‖ < r) : χ x = 1 := by
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro n _
    rw [← χ.map_nsmul_eq_pow]
    apply hball
    rw [mem_ball_zero_iff, nsmul_eq_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K n)).trans_lt hx
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy
  have h := χ.map_add_eq_mul (y-x) x
  simpa [hk _ (show ‖y-x‖ < r by simpa [mem_ball,dist_eq_norm] using hy)] using h

/-- Nontriviality follows already from Plancherel on the indicator of the unit ball.
For a trivial character its transform would be a nonzero constant on a field of infinite measure. -/
private theorem nontrivial_of_plancherel {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [ProperSpace K] [MeasurableSpace K] [BorelSpace K] (dx : Measure K) [dx.IsAddHaarMeasure]
    (ψ : K → ℂ) (hP : ∀ f : K → ℂ, Continuous f → HasCompactSupport f →
      (∫⁻ y, ‖∫ x, f x * ψ (x*y) ∂dx‖ₑ ^ 2 ∂dx) = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂dx) :
    ∃ x, ψ x ≠ 1 := by
  by_contra! hψ
  let B := ball (0 : K) 1
  let g := B.indicator (fun _ => (1 : ℂ))
  have hc : IsClopen B := IsUltrametricDist.isClopen_ball _ _
  have hk : IsCompact B := (isCompact_closedBall (0 : K) 1).of_isClosed_subset hc.isClosed ball_subset_closedBall
  have hpos : 0 < dx B := hc.isOpen.measure_pos _ ⟨0, mem_ball_self one_pos⟩
  have hfin := hk.measure_lt_top (μ := dx)
  have he := hP g (hc.continuous_indicator continuous_const)
    (HasCompactSupport.intro hk (fun _ hx => indicator_of_notMem hx _))
  have hi : (∫ x, g x ∂dx) = (dx.real B : ℂ) := by
    simp [g,integral_indicator hc.isOpen.measurableSet,Measure.real]
  have hr : (∫⁻ x, ‖g x‖ₑ ^ 2 ∂dx) = dx B := by
    have eg (x : K) : ‖g x‖ₑ ^ 2 = B.indicator (fun _ => (1 : ℝ≥0∞)) x := by
      by_cases hx : x ∈ B <;> simp [g,hx]
    simp_rw [eg]
    simp [lintegral_indicator hc.isOpen.measurableSet]
  have hn : (dx.real B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  simp only [hψ, mul_one, hi, lintegral_const, measure_univ_of_isAddLeftInvariant, hr] at he
  rw [ENNReal.mul_top (pow_ne_zero 2 (enorm_ne_zero.mpr hn))] at he
  exact hfin.ne he.symm

namespace Character
open NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] (χ : Character F)

theorem locallyConstant_finiteValue (p : HeightOneSpectrum (𝓞 F)) :
    IsLocallyConstant (χ.localValue F (.inr p)) := by
  let v : Place F := .inr p
  let ψ : AddChar (p.adicCompletion F) Circle :=
    χ.toChar.compAddMonoidHom
      { toFun := singleAdele F v
        map_zero' := singleAdele_zero v
        map_add' := singleAdele_add v }
  exact (locallyConstant_addChar ψ (χ.continuous_toChar.comp (continuous_singleAdele v))).comp Subtype.val

theorem nontrivial_finiteValue (p : HeightOneSpectrum (𝓞 F)) :
    ∃ x, χ.localValue F (.inr p) x ≠ 1 := by
  let v : Place F := .inr p
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace (p.adicCompletion F) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  letI : MeasurableSpace (p.adicCompletion F) := borel _
  letI : BorelSpace (p.adicCompletion F) := ⟨rfl⟩
  let dx : Measure (p.adicCompletion F) := selfDual F χ v
  obtain ⟨hh,hP⟩ := (existsUnique_selfDual F χ v).exists.choose_spec
  letI : dx.IsAddHaarMeasure := hh
  exact nontrivial_of_plancherel dx _ hP

end Character

namespace SmoothFiniteFamily
variable {P K : Type*} [TopologicalSpace P] [WeaklyLocallyCompactSpace P] [NormedField K]
    [ProperSpace K] [MeasurableSpace K] [BorelSpace K]

/-- Fourier transformation in the field variable preserves the finite-place
Schwartz–Bruhat bounds uniformly on each compact set of parameters. -/
theorem fourier {g : P → K → ℂ} (hg : SmoothFiniteFamily g) (dx : Measure K) [dx.IsAddHaarMeasure]
    {ψ : K → ℂ} (hc : IsLocallyConstant ψ) (ha : ∀ x y, ψ (x+y) = ψ x * ψ y)
    (hn : ∃ x, ψ x ≠ 1) : SmoothFiniteFamily (fun p u => ∫ t, g p t * ψ (u*t) ∂dx) := by
  apply smoothFiniteFamily_of_support
  · let G (w : (P × K) × K) := g w.1.1 w.2 * ψ (w.1.2*w.2)
    have hG : IsLocallyConstant G :=
      (hg.1.comp_continuous ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).mul
        (hc.comp_continuous ((continuous_snd.comp continuous_fst).mul continuous_snd))
    have hs (q : P × K) : ∃ C : Set K, IsCompact C ∧ ∀ᶠ w in 𝓝 q, ∀ t ∉ C, G (w,t) = 0 := by
      obtain ⟨T,hT,hq⟩ := exists_compact_mem_nhds q.1
      obtain ⟨C,hC,hvan⟩ := (hg.2 T hT).2.1
      refine ⟨C,hC,?_⟩
      filter_upwards [(continuous_fst.tendsto q).eventually hq] with w hw t ht
      dsimp [G]
      rw [hvan _ hw _ ht,zero_mul]
    exact (locallyConstant_slices_of_localSupport hG hs).comp (fun s => ∫ t, s t ∂dx)
  · intro T hT
    obtain ⟨b,hb⟩ := hn
    obtain ⟨r,hr,hper⟩ := Metric.mem_nhds_iff.mp ((hg.2 T hT).2.2)
    refine ⟨closedBall 0 (‖b‖/r),isCompact_closedBall _ _,?_⟩
    intro p hp u hu
    have hlt : ‖b‖/r < ‖u‖ := by simpa [mem_closedBall,dist_zero_right] using hu
    have hu₀ : u ≠ 0 := norm_pos_iff.mp ((div_nonneg (norm_nonneg b) hr.le).trans_lt hlt)
    let h := b/u
    have hh : h ∈ ball 0 r := by
      rw [mem_ball_zero_iff,norm_div, div_lt_iff₀ (norm_pos_iff.mpr hu₀)]
      simpa [mul_comm] using (div_lt_iff₀ hr).mp hlt
    let f (t : K) := g p t * ψ (u*t)
    have he (t : K) : f (t+h) = f t * ψ b := by
      dsimp [f]
      rw [hper hh p hp t,mul_add,ha,show u*h = b by dsimp [h]; field_simp, mul_assoc]
    have hi := integral_add_right_eq_self (μ := dx) f h
    simp_rw [he] at hi
    rw [integral_mul_const] at hi
    exact by_contra fun hne => hb ((mul_eq_left₀ hne).mp hi)

end SmoothFiniteFamily

end MetaplecticPoisson
