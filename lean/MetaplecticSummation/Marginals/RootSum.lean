import MetaplecticSummation.Marginals.DifferenceConvergence
import MetaplecticSummation.TamePowers

/-! The root-sum form of the reverse marginal formula (Appendix A). -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Set Filter Polynomial
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

private theorem difference_root_sum (p : HeightOneSpectrum (𝓞 F)) {f ρ : LocalField F (.inr p) → ℂ}
    (hf : Bruhat (.inr p) f) (hρ : Bruhat (.inr p) ρ) (h₀ : ρ 0 = 0) (a : (LocalField F (.inr p))ˣ)
    (hpow : (∀ u, d.symbol (.inr p) u a = 1) → ∃ b, b^n = a) :
    let v : Place F := .inr p
    (∫ t, d.hat v ρ t * d.differenceIntegral v f a (t^n-a.val) ∂(selfDual F d.character v)) =
      f 0 * ∑ r ∈ nthRootsFinset n a.val, d.lineIntegral v (fun μ => ρ μ.val * d.character.localValue F v (μ.val*r)) := by
  by_cases hp : ∃ b, b^n = a
  · obtain ⟨b,rfl⟩ := hp
    exact d.finite_root_contribution p hf hρ h₀ b
  obtain ⟨he,hz⟩ := d.differenceIntegral_nonpower (.inr p) f a hp
    (fun c => d.marginalDifference_finite_integrable p hf a c)
    (by simpa only [not_forall] using mt hpow hp)
  dsimp only
  simp only [hz,mul_zero,integral_zero,he,Finset.sum_empty]

/-- Pairing the transformed marginal with an arbitrary test supported away from
zero gives the sum of the Fourier integrals over the local n-th roots. -/
theorem finite_tested_root_sum_on_test (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (hΦ : Φ.val ∈ d.testSet (.inr p)) (s : (LocalField F (.inr p))ˣ)
    (hpow : ∀ a : (LocalField F (.inr p))ˣ, (∀ u, d.symbol (.inr p) u a = 1) → ∃ b, b^n = a)
    {ρ : LocalField F (.inr p) → ℂ} (hρ : Bruhat (.inr p) ρ) (h₀ : ρ 0 = 0) :
    let v : Place F := .inr p
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) *
      d.lineIntegral v (fun μ => d.marginal v (d.transformTest v Φ hΦ) (μ^n*s) * ρ μ.val) =
      ∫ y, (if hy : y ≠ 0 then d.axis v Φ (Units.mk0 y hy) else 0) *
        ∑ r ∈ nthRootsFinset n (-(s.val*y)), d.lineIntegral v (fun μ => ρ μ.val * d.character.localValue F v (μ.val*r))
        ∂(selfDual F d.character v) := by
  refine (d.finite_tested_marginal_difference_on_test p Φ hΦ s hρ h₀).trans (integral_congr_ae ?_)
  filter_upwards with y
  by_cases hy : y = 0
  · simp [hy]
  · let Y := Units.mk0 y hy
    have he := d.difference_root_sum p (d.finiteTest_axisSlice p hΦ Y) hρ h₀ (-(s*Y)) (hpow _)
    simpa only [Y,Units.val_neg,Units.val_mul,Units.val_mk0,sub_neg_eq_add,dif_pos hy,axis] using he


private instance finiteProper (p : HeightOneSpectrum (𝓞 F)) : ProperSpace (LocalField F (.inr p)) := by
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)

/-- The marginal of a Schwartz section is locally constant on the units:
its transverse support lies in the projection of one fixed compact set. -/
theorem finite_marginal_locallyConstant (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p)) :
    IsLocallyConstant (d.marginal (.inr p) Φ) := by
  let v : Place F := .inr p
  let K := LocalField F v
  let dx := selfDual F d.character v
  obtain ⟨L,hL⟩ := d.exists_leading_finite p
  obtain ⟨C,hC,hout⟩ := (d.finite_support_and_germ_of_isLeadingTerm p Φ (hL Φ)).1
  have hl := (d.locallyConstant_finite_schwartz p Φ).1
  have hs := locallyConstant_slices_of_localSupport hl (fun a => ⟨Prod.snd '' C,hC.image continuous_snd,
    Eventually.of_forall (fun (b : Kˣ) (y : K) hy => by
      have h := (hout (b.val,y) (fun hin => hy ⟨_,hin,rfl⟩)).1
      simpa only [xChart,dif_pos b.ne_zero,Units.mk0_val] using h)⟩)
  exact hs.comp (fun f => ∫ y, f y ∂dx)

theorem axis_roots_bounded (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (hΦ : Φ.val ∈ d.testSet (.inr p)) (s : (LocalField F (.inr p))ˣ) :
    ∃ B : ℝ, ∀ (y : (LocalField F (.inr p))ˣ), d.axis (.inr p) Φ y ≠ 0 →
      ∀ r ∈ nthRootsFinset n (-(s.val*y.val)), ‖r‖ ≤ B := by
  let K := LocalField F (.inr p)
  obtain ⟨C,hC,_,hvan⟩ := (show finiteTest Φ.val from hΦ.2).2.2
  obtain ⟨R,hR⟩ := (hC.image continuous_snd).exists_bound_of_continuousOn (f := id) continuous_id.continuousOn
  refine ⟨max 1 (‖s.val‖*R),fun y hy r hr => ?_⟩
  have hm : ((0 : K),y.val) ∈ C := by
    by_contra ho
    exact hy (by simpa only [axis,yChart,dif_pos y.ne_zero,Units.mk0_val] using (hvan _ ho).2)
  have hv := congrArg norm ((mem_nthRootsFinset (NeZero.pos n) _).mp hr)
  simp only [norm_pow,norm_neg,norm_mul] at hv
  by_cases h : ‖r‖ ≤ 1
  · exact h.trans (le_max_left _ _)
  apply le_trans _ (le_max_right _ _)
  calc
    ‖r‖ ≤ ‖r‖ ^ n := le_self_pow₀ (le_of_not_ge h) (NeZero.ne n)
    _ = _ := hv
    _ ≤ _ := mul_le_mul_of_nonneg_left (hR y.val ⟨_,hm,rfl⟩) (norm_nonneg _)

omit [NeZero n] in
/-- Localize frequency to a compact open ball on which the marginal and all
phases with root in C are constant. The ball has positive multiplicative mass. -/
private theorem root_frequency_test (p : HeightOneSpectrum (𝓞 F)) (μ₀ : (LocalField F (.inr p))ˣ)
    (m : (LocalField F (.inr p))ˣ → ℂ) (hm : IsLocallyConstant m)
    (C : Set (LocalField F (.inr p))) (hC : IsCompact C) :
    let v : Place F := .inr p
    ∃ (ρ : LocalField F v → ℂ) (c : ℂ), Bruhat v ρ ∧ ρ 0 = 0 ∧ c ≠ 0 ∧
      d.lineIntegral v (fun u => m u * ρ u.val) = m μ₀ * c ∧
      ∀ a ∈ C, d.lineIntegral v (fun u => ρ u.val * d.character.localValue F v (u.val*a)) =
        d.character.localValue F v (μ₀.val*a) * c := by
  let v : Place F := .inr p
  let K := LocalField F v
  letI : IsUltrametricDist K := inferInstanceAs (IsUltrametricDist (p.adicCompletion F))
  let ψ := d.character.localValue F v
  have hl := d.character.locallyConstant_finiteValue p
  let E : Set (K × K) := {z | ψ (z.1*z.2) = ψ (μ₀.val*z.2)}
  have he : IsOpen E := ((hl.comp_continuous (continuous_fst.mul continuous_snd)).prodMk
    (hl.comp_continuous (continuous_const.mul continuous_snd))) {z | z.1 = z.2}
  obtain ⟨T,V,hT,_,hμ,hCV,hTV⟩ := generalized_tube_lemma (isCompact_singleton (x := μ₀.val)) hC he
    (by rintro ⟨x,a⟩ ⟨rfl : x = μ₀.val,_⟩; rfl)
  have phase (x a : K) (hx : x ∈ T) (ha : a ∈ C) : ψ (x*a) = ψ (μ₀.val*a) := by
    change (x,a) ∈ E
    apply hTV
    exact ⟨hx,hCV ha⟩
  obtain ⟨W,hW,hpre⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.mp (hm {m μ₀})
  have hμW : μ₀.val ∈ W := by
    change μ₀ ∈ Units.val ⁻¹' W
    rw [hpre]
    rfl
  let U := T ∩ W ∩ ({0} : Set K)ᶜ
  have hu : U ∈ 𝓝 μ₀.val := ((hT.inter hW).inter isClosed_singleton.isOpen_compl).mem_nhds ⟨⟨hμ rfl,hμW⟩,μ₀.ne_zero⟩
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp hu
  let S := Metric.closedBall μ₀.val (r/2)
  have hS : IsClopen S := IsUltrametricDist.isClopen_closedBall (μ₀.val : K) (half_pos hr).ne'
  have hSU : S ⊆ U := (Metric.closedBall_subset_ball (half_lt_self hr)).trans hrU
  have hn : (0 : K) ∉ S := fun h => (hSU h).2 rfl
  let ρ := S.indicator (fun _ => (1 : ℂ))
  let D := (Units.val : Kˣ → K) ⁻¹' S
  have hD : IsOpen D := hS.isOpen.preimage Units.continuous_val
  have hd : IsCompact D := Units.isEmbedding_val₀.isInducing.isCompact_preimage' (isCompact_closedBall _ _) (by
    intro x hx
    exact ⟨Units.mk0 x (fun h => hn (h ▸ hx)),rfl⟩)
  let ν := d.lineMeasure v
  let c : ℂ := ν.real D
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos
    (hD.measure_ne_zero ν ⟨μ₀,Metric.mem_closedBall_self (half_pos hr).le⟩) hd.measure_ne_top).ne'
  have mass : d.lineIntegral v (fun u => ρ u.val) = c := by
    rw [← d.integral_lineMeasure]
    change (∫ u, D.indicator (fun _ => (1 : ℂ)) u ∂ν) = c
    exact (integral_indicator (μ := ν) (f := fun _ : Kˣ => (1 : ℂ)) hD.measurableSet).trans (by
      simp [c,Measure.real])
  refine ⟨ρ,c,⟨?_,HasCompactSupport.intro (isCompact_closedBall _ _) (fun _ hx => indicator_of_notMem hx _)⟩,
    indicator_of_notMem hn _,hc,?_,?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ S
    · filter_upwards [hS.isOpen.mem_nhds hx] with z hz
      simp [ρ,hz,hx]
    · filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hx] with z hz
      simp [ρ,hx,(show z ∉ S from hz)]
  · rw [← mass,← d.lineIntegral_const_mul]
    congr 1
    funext u
    by_cases hu : u.val ∈ S
    · have h : u ∈ Units.val ⁻¹' W := (hSU hu).1.2
      rw [hpre] at h
      exact congrArg (· * ρ u.val) (show m u = m μ₀ from h)
    · simp [ρ,hu]
  · intro a ha
    change d.lineIntegral v (fun u => ρ u.val * ψ (u.val*a)) = ψ (μ₀.val*a)*c
    rw [← mass,← d.lineIntegral_const_mul]
    apply congrArg (d.lineIntegral v)
    funext u
    by_cases hu : u.val ∈ S
    · have e := phase u.val a (hSU hu).1.1 ha
      change ρ u.val * ψ (u.val*a) = ψ (μ₀.val*a) * ρ u.val
      rw [e,mul_comm]
    · simp [ρ,hu]

/-- The diagonal embedding identifies the global roots with all local roots
when the ground field contains a primitive n-th root. -/
def localRootsEquiv (v : Place F) : Mu F n ≃* rootsOfUnity n (LocalField F v) :=
  rootsOfUnityEquivOfPrimitiveRoots (diagonal F v).injective
    ⟨d.root,(mem_primitiveRoots (NeZero.pos n)).2 d.primitive⟩

/-- Transport the right kernel of a local symbol in the arithmetic Frobenius
convention to the power criterion used in the root-sum formula. -/
theorem symbol_power_of_local_right_kernel (v : Place F)
    (B : (LocalField F v)ˣ → (LocalField F v)ˣ → rootsOfUnity n (LocalField F v))
    (compare : ∀ u a, d.localRootsEquiv v (d.family v u a) = (B u a)⁻¹)
    (kernel : ∀ a, (∀ u, B u a = 1) ↔ a ∈ (powMonoidHom n : (LocalField F v)ˣ →* _).range)
    (a : (LocalField F v)ˣ) (ha : ∀ u, d.symbol v u a = 1) : ∃ b, b^n = a := by
  apply (kernel a).mp
  intro u
  have h : d.family v u a = 1 := by
    apply d.injective
    rw [map_one]
    exact Units.ext (ha u)
  have e := compare u a
  rw [h,map_one,eq_comm,inv_eq_one] at e
  exact e

/-- The right radical at every finite place is the subgroup of powers. -/
theorem finite_symbol_power (p : HeightOneSpectrum (𝓞 F)) (a : (LocalField F (.inr p))ˣ)
    (ha : ∀ u, d.symbol (.inr p) u a = 1) : ∃ b, b^n = a := by
  let m : ℕ+ := ⟨n, NeZero.pos n⟩
  have he : d.family = Hilbert.family m d.primitive :=
    IsHilbertFamily.unique d.primitive d.family_spec (Hilbert.family_spec m d.primitive)
  apply (Hilbert.finiteValue_right_kernel m d.primitive p a).mp
  intro u
  change Hilbert.family m d.primitive (.inr p) u a = 1
  rw [← he]
  exact d.injective ((Units.ext (ha u)).trans d.embedding.map_one.symm)

/-- Equation (axis-marginal-roots) of Appendix A. The arithmetic hypothesis
is exactly property 2(b) at the chosen completion. -/
theorem finite_marginal_root_formula_on_test (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (hΦ : Φ.val ∈ d.testSet (.inr p)) (s μ : (LocalField F (.inr p))ˣ)
    (hpow : ∀ a : (LocalField F (.inr p))ˣ, (∀ u, d.symbol (.inr p) u a = 1) → ∃ b, b^n = a) :
    let v : Place F := .inr p
    (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ) * d.marginal v (d.transformTest v Φ hΦ) (μ^n*s) =
      ∫ y, (if hy : y ≠ 0 then d.axis v Φ (Units.mk0 y hy) else 0) *
        ∑ a ∈ nthRootsFinset n (-(s.val*y)), d.character.localValue F v (μ.val*a)
        ∂(selfDual F d.character v) := by
  let v : Place F := .inr p
  let K := LocalField F v
  let m (u : Kˣ) := d.marginal v (d.transformTest v Φ hΦ) (u^n*s)
  have hm : IsLocallyConstant m := (d.finite_marginal_locallyConstant p _).comp_continuous
    ((continuous_id.pow n).mul continuous_const)
  obtain ⟨B,hB⟩ := d.axis_roots_bounded p Φ hΦ s
  obtain ⟨ρ,c,hρ,h₀,hc,hmc,hphase⟩ := d.root_frequency_test p μ m hm (Metric.closedBall (0 : K) B) (isCompact_closedBall _ _)
  have h := d.finite_tested_root_sum_on_test p Φ hΦ s hpow hρ h₀
  dsimp only at h ⊢
  apply mul_right_cancel₀ hc
  rw [mul_assoc,← hmc,← integral_mul_const]
  apply h.trans
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y = 0
  · simp [hy]
  · simp only [dif_pos hy]
    by_cases hz : d.axis (.inr p) Φ (Units.mk0 y hy) = 0
    · simp [hz]
    · rw [mul_assoc,Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun a ha => hphase a (mem_closedBall_zero_iff.mpr (hB (Units.mk0 y hy) hz a ha))


end MetaplecticPoisson.Datum
