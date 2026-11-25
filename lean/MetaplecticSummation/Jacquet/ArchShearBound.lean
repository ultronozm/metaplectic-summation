import MetaplecticSummation.Jacquet.ShearRegion
import MetaplecticSummation.FourierDifferences
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.ZPow


/-! The third difference of order three behind Lemma 10.4 at real and complex
places. On the far part of the vertical cone the X-chart of a test section has
rapidly decaying third derivatives along vertical lines. For the transform of a
test section, the power-ray formula expresses the third difference as the Fourier
integral of a third difference of Y-chart Radon slices, which the substitution
y = βw makes smooth in the second coordinate of the output vector. -/

open Metric Set Filter
open scoped ContDiff Topology Nat

namespace MetaplecticPoisson

/-- Real derivatives of the inverse on a normed field over the reals. -/
theorem norm_iteratedFDeriv_real_inv_le {L : Type*} [NontriviallyNormedField L] [NormedAlgebra ℝ L]
    (k : ℕ) {β : L} (hβ : β ≠ 0) :
    ‖iteratedFDeriv ℝ k (fun x : L => x⁻¹) β‖ ≤ k ! * ‖β‖⁻¹^(k+1) := by
  have h : ContDiffAt L k (fun x : L => x⁻¹) β := contDiffAt_inv L hβ
  rw [← h.restrictScalars_iteratedFDeriv (𝕜 := ℝ),Function.comp_apply,
    ContinuousMultilinearMap.norm_restrictScalars,norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_eq_iterate]
  change ‖deriv^[k] Inv.inv β‖ ≤ _
  rw [iter_deriv_inv,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_zpow,
    show (-1 - k : ℤ) = -((k+1 : ℕ) : ℤ) by push_cast; ring,zpow_neg,zpow_natCast,inv_pow]
  gcongr
  exact (Nat.norm_cast_le _).trans_eq (by simp)

/-- The forward-difference bound for a function smooth only on an open set
containing the closed ball spanned by the steps. -/
theorem norm_fwdDiff_iter_le_of_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℂ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (h z : E) (j : ℕ) {M : ℝ} (hball : closedBall z (j*‖h‖) ⊆ U)
    (hM : ∀ y ∈ closedBall z (j*‖h‖), ‖iteratedFDeriv ℝ j f y‖ ≤ M) :
    ‖(fwdDiff h)^[j] f z‖ ≤ M*‖h‖^j := by
  set r := (j:ℝ)*‖h‖
  have hr : 0 ≤ r := by positivity
  obtain ⟨δ,hδ,hsub⟩ := (isCompact_closedBall z r).exists_cthickening_subset_open hU hball
  rw [cthickening_closedBall hδ.le hr] at hsub
  let χ : ContDiffBump z := ⟨r + δ/2, r + δ, by linarith, by linarith⟩
  let g : E → ℂ := fun x => (χ x : ℂ) * f x
  have htsupp : tsupport χ ⊆ U := by rw [χ.tsupport_eq]; exact (closedBall_subset_closedBall (by simp [χ,add_comm])).trans hsub
  have hg : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact (Complex.ofRealCLM.contDiff.comp χ.contDiff).contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
    · have hn : x ∉ tsupport χ := fun h => hx (htsupp h)
      apply contDiffAt_const (c := (0:ℂ)).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
      simp [g,hy]
  have hone : ∀ y ∈ ball z (r + δ/2), g =ᶠ[𝓝 y] f := fun y hy => by
    filter_upwards [isOpen_ball.mem_nhds hy] with x hx
    simp [g,χ.one_of_mem_closedBall (ball_subset_closedBall hx)]
  have hin : closedBall z r ⊆ ball z (r + δ/2) := closedBall_subset_ball (by linarith)
  have heq : (fwdDiff h)^[j] g z = (fwdDiff h)^[j] f z := by
    rw [fwdDiff_iter_eq_sum_shift,fwdDiff_iter_eq_sum_shift]
    refine Finset.sum_congr rfl fun k hk => ?_
    congr 1
    have hk' : z + k • h ∈ closedBall z r := by
      rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left]
      exact norm_nsmul_le.trans (mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) (norm_nonneg _))
    exact (hone _ (hin hk')).eq_of_nhds
  rw [← heq]
  apply norm_fwdDiff_iter_le hg h z j
  intro y hy
  rw [((hone y (hin hy)).iteratedFDeriv ℝ j).eq_of_nhds]
  exact hM y hy


theorem norm_iteratedFDeriv_clm_le {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (Λ : E →L[ℝ] G) (x : E) {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i Λ x‖ ≤ ‖Λ‖ := by
  obtain ⟨k,rfl⟩ : ∃ k, i = k+1 := ⟨i-1,by omega⟩
  rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply,LinearIsometryEquiv.norm_map]
  have hf : (fun y => fderiv ℝ Λ y) = fun _ => Λ := funext fun y => Λ.fderiv
  rw [hf]
  rcases k with _|k
  · simp
  · rw [iteratedFDeriv_const_of_ne (by omega),Pi.zero_apply]
    exact ContinuousMultilinearMap.opNorm_zero.trans_le (norm_nonneg Λ)


/-- Derivatives of the inner map in the substituted Y-chart Radon integral. -/
theorem norm_iteratedFDeriv_radon_inner_le {L : Type*} [NontriviallyNormedField L] [NormedAlgebra ℝ L]
    (A T W : L) {β : L} (hβ : 1/2 ≤ ‖β‖) {i : ℕ} (hi : 1 ≤ i) (hi3 : i ≤ 3) :
    ‖iteratedFDeriv ℝ i (fun β : L => (A + T*β⁻¹, β*W)) β‖ ≤ (16*((1+‖T‖)*(1+‖W‖)))^i := by
  have hβ0 : β ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hβ)
  let Λ₁ : L →L[ℝ] L := ContinuousLinearMap.mul ℝ L T
  let Λ₂ : L →L[ℝ] L := (ContinuousLinearMap.mul ℝ L).flip W
  have hinv : ContDiffAt ℝ ∞ (fun x : L => x⁻¹) β := contDiffAt_inv ℝ hβ0
  have h₁ : ContDiffAt ℝ ∞ (fun x : L => A + T*x⁻¹) β := contDiffAt_const.add (Λ₁.contDiff.contDiffAt.comp β hinv)
  have h₂ : ContDiffAt ℝ ∞ (fun x : L => x*W) β := Λ₂.contDiff.contDiffAt
  rw [iteratedFDeriv_prodMk h₁ h₂ (by exact_mod_cast le_top),ContinuousMultilinearMap.opNorm_prod]
  have e₁ : ‖iteratedFDeriv ℝ i (fun x : L => A + T*x⁻¹) β‖ ≤ ‖T‖ * (i ! * 2^(i+1)) := by
    have hadd := iteratedFDeriv_add_apply (i := i) (f := fun _ : L => A) (g := fun x : L => T*x⁻¹)
      (contDiffAt_const.of_le (by exact_mod_cast le_top)) ((Λ₁.contDiff.contDiffAt.comp β hinv).of_le (by exact_mod_cast le_top))
    have hfun : (fun x : L => A + T*x⁻¹) = (fun _ : L => A) + fun x : L => T*x⁻¹ := rfl
    rw [hfun,hadd,iteratedFDeriv_const_of_ne (by omega),Pi.zero_apply,zero_add]
    have hc := Λ₁.norm_iteratedFDeriv_comp_left (n := i) hinv (by exact_mod_cast le_top)
    have hΛ : ‖Λ₁‖ ≤ ‖T‖ := ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun x => by
      simp [Λ₁,norm_mul]
    have hb := norm_iteratedFDeriv_real_inv_le i hβ0
    have hpow : ‖β‖⁻¹^(i+1) ≤ 2^(i+1) := by
      apply pow_le_pow_left₀ (by positivity)
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      linarith
    calc ‖iteratedFDeriv ℝ i (fun x : L => T*x⁻¹) β‖ = ‖iteratedFDeriv ℝ i (Λ₁ ∘ fun x : L => x⁻¹) β‖ := rfl
      _ ≤ ‖Λ₁‖ * ‖iteratedFDeriv ℝ i (fun x : L => x⁻¹) β‖ := hc
      _ ≤ ‖T‖ * (i ! * 2^(i+1)) := by
          gcongr
          exact hb.trans (by gcongr)
  have e₂ : ‖iteratedFDeriv ℝ i (fun x : L => x*W) β‖ ≤ ‖W‖ := by
    refine (norm_iteratedFDeriv_clm_le Λ₂ β hi).trans ?_
    exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg W) fun x => by simp [Λ₂,norm_mul]
  set X := (1+‖T‖)*(1+‖W‖)
  have hT : ‖T‖ ≤ X := by nlinarith [norm_nonneg T,norm_nonneg W]
  have hW : ‖W‖ ≤ X := by nlinarith [norm_nonneg T,norm_nonneg W]
  have hX : 1 ≤ X := by nlinarith [norm_nonneg T,norm_nonneg W]
  have hfac : (i ! : ℝ) * 2^(i+1) ≤ 96 := by
    interval_cases i <;> norm_num [Nat.factorial]
  have key : ‖T‖ * (i ! * 2^(i+1)) ≤ (16*X)^i ∧ ‖W‖ ≤ (16*X)^i := by
    have h16 : 16*X ≤ (16*X)^i := le_self_pow₀ (by linarith) (by omega)
    constructor
    · interval_cases i
      · norm_num [Nat.factorial] at *; nlinarith
      · norm_num [Nat.factorial] at *; nlinarith
      · norm_num [Nat.factorial] at *; nlinarith [le_self_pow₀ hX (show 3 ≠ 0 by norm_num)]
    · linarith
  exact max_le (e₁.trans key.1) (e₂.trans key.2)

private theorem min_pow_le (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    min (x^N) ((x^N)⁻¹) ≤ 2^N * ((1+x)^N)⁻¹ := by
  rcases le_total x 1 with h|h
  · refine (min_le_left _ _).trans ((pow_le_one₀ hx h).trans ?_)
    rw [← div_eq_mul_inv,one_le_div (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (by linarith) N
  · refine (min_le_right _ _).trans ?_
    rw [← div_eq_mul_inv,inv_eq_one_div,div_le_div_iff₀ (by positivity) (by positivity),one_mul,← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) N

/-- Third differences in the second coordinate of the substituted Y-chart
integrand, uniformly for unit base points and small steps. -/
theorem radon_integrand_third_difference {L : Type} [NontriviallyNormedField L] [NormedAlgebra ℝ L]
    [FiniteDimensional ℝ L] {Y : L × L → ℂ} (hY : rapidChart {p : L × L | p.2 ≠ 0} Y) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ A T W b h : L, W ≠ 0 → ‖A‖ ≤ ‖W‖ → ‖b‖ = 1 → 6*‖h‖ ≤ 1 →
      ‖(fwdDiff h)^[3] (fun β => Y (A + T*β⁻¹, β*W)) b‖ ≤
        K*‖h‖^3*(((1+‖T‖)*(1+‖W‖))^3)⁻¹ := by
  choose C hC using fun i => hY.2 i 12
  let Cm := |C 0| + |C 1| + |C 2| + |C 3|
  have hCm : 0 ≤ Cm := by positivity
  have hCi (i : ℕ) (hi : i ≤ 3) : C i ≤ Cm := by
    interval_cases i <;> simp only [Cm] <;> linarith [le_abs_self (C 0),le_abs_self (C 1),le_abs_self (C 2),
      le_abs_self (C 3),abs_nonneg (C 0),abs_nonneg (C 1),abs_nonneg (C 2),abs_nonneg (C 3)]
  let K := 6*Cm*2^12*16^3*10^6
  refine ⟨K,by positivity,fun A T W b h hW hA hb hh => ?_⟩
  let U : Set L := {β | β ≠ 0}
  let V : Set (L × L) := {p | p.2 ≠ 0}
  have hU : IsOpen U := isOpen_ne
  have hV : IsOpen V := isOpen_ne_fun continuous_snd continuous_const
  let γ : L → L × L := fun β => (A + T*β⁻¹, β*W)
  have hγ : ContDiffOn ℝ ∞ γ U := fun β hβ =>
    ((contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_inv ℝ hβ))).prodMk
      (contDiffAt_id.mul contDiffAt_const)).contDiffWithinAt
  have hmaps : MapsTo γ U V := fun β hβ => mul_ne_zero hβ hW
  have hφ : ContDiffOn ℝ ∞ (fun β => Y (A + T*β⁻¹, β*W)) U := hY.1.comp hγ hmaps
  set X := (1+‖T‖)*(1+‖W‖)
  have hX : 1 ≤ X := by nlinarith [norm_nonneg T,norm_nonneg W]
  have hball : closedBall b (3*‖h‖) ⊆ closedBall b (1/2) := closedBall_subset_closedBall (by linarith)
  have hnorm (β : L) (hβ : β ∈ closedBall b (1/2)) : 1/2 ≤ ‖β‖ ∧ ‖β‖ ≤ 3/2 := by
    rw [mem_closedBall,dist_eq_norm] at hβ
    constructor
    · have := norm_sub_norm_le b (b - β); rw [sub_sub_cancel,hb,norm_sub_rev] at this; linarith
    · have := norm_le_insert' β b; rw [hb] at this; linarith [norm_sub_rev β b]
  have bound (β : L) (hβ : β ∈ closedBall b (3*‖h‖)) :
      ‖iteratedFDeriv ℝ 3 (fun β => Y (A + T*β⁻¹, β*W)) β‖ ≤ K*(X^3)⁻¹ := by
    obtain ⟨hβ1,hβ2⟩ := hnorm β (hball hβ)
    have hβ0 : β ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hβ1)
    have hβU : β ∈ U := hβ0
    have hγV : γ β ∈ V := hmaps hβU
    have hγ1 : ‖A + T*β⁻¹‖ ≤ ‖γ β‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    have hγ2 : ‖β*W‖ ≤ ‖γ β‖ := by rw [Prod.norm_def]; exact le_max_right _ _
    set G := ‖γ β‖
    have hG : 0 ≤ G := norm_nonneg _
    have hWG : ‖W‖ ≤ 2*G := by
      have := hγ2
      rw [norm_mul] at this; nlinarith [norm_nonneg W]
    have hTG : ‖T‖ ≤ 5*G := by
      have h1 := hγ1
      have h2 : ‖T*β⁻¹‖ ≤ 3*G := by
        have := norm_sub_le (A + T*β⁻¹) A; rw [add_sub_cancel_left] at this; linarith
      have h3 : ‖T‖ = ‖T*β⁻¹‖*‖β‖ := by rw [← norm_mul,inv_mul_cancel_right₀ hβ0]
      rw [h3]; nlinarith [norm_nonneg (T*β⁻¹)]
    have hXG : X ≤ 10*(1+G)^2 := by
      have : (1+‖T‖)*(1+‖W‖) ≤ (5*(1+G))*(2*(1+G)) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      linarith
    have hC' (i : ℕ) (hi : i ≤ 3) : ‖iteratedFDerivWithin ℝ i Y V (γ β)‖ ≤ Cm*(2^12*((1+G)^12)⁻¹) := by
      rw [iteratedFDerivWithin_of_isOpen i hV hγV]
      refine (hC i (γ β) hγV).trans ?_
      have hm := min_pow_le G hG 12
      calc C i * min (G^12) ((G^12)⁻¹) ≤ Cm * min (G^12) ((G^12)⁻¹) :=
            mul_le_mul_of_nonneg_right (hCi i hi) (le_min (by positivity) (by positivity))
        _ ≤ Cm*(2^12*((1+G)^12)⁻¹) := mul_le_mul_of_nonneg_left hm hCm
    have hD' (i : ℕ) (hi : 1 ≤ i) (hi3 : i ≤ 3) : ‖iteratedFDerivWithin ℝ i γ U β‖ ≤ (16*X)^i := by
      rw [iteratedFDerivWithin_of_isOpen i hU hβU]
      exact norm_iteratedFDeriv_radon_inner_le A T W hβ1 hi hi3
    have hfb := norm_iteratedFDerivWithin_comp_le hY.1 hγ (n := 3) (by simp)
      hV.uniqueDiffOn hU.uniqueDiffOn hmaps hβU hC' hD'
    rw [iteratedFDerivWithin_of_isOpen 3 hU hβU] at hfb
    refine hfb.trans ?_
    have hX6 : X^3*X^3 ≤ 10^6*(1+G)^12 := by
      calc X^3*X^3 = X^6 := by ring
        _ ≤ (10*(1+G)^2)^6 := pow_le_pow_left₀ (by positivity) hXG 6
        _ = 10^6*(1+G)^12 := by ring
    have hpos : 0 < (1+G)^12 := by positivity
    have hX3 : 0 < X^3 := pow_pos (zero_lt_one.trans_le hX) 3
    have key : X^3/(1+G)^12 ≤ 10^6/X^3 := by
      rw [div_le_div_iff₀ hpos hX3]; linarith
    rw [show ((3:ℕ)! : ℝ) = 6 by norm_num [Nat.factorial],mul_pow]
    calc 6*(Cm*(2^12*((1+G)^12)⁻¹))*(16^3*X^3) = 6*Cm*2^12*16^3*(X^3/(1+G)^12) := by ring
      _ ≤ 6*Cm*2^12*16^3*(10^6/X^3) := by gcongr
      _ = K*(X^3)⁻¹ := by simp only [K]; ring
  have hres := norm_fwdDiff_iter_le_of_contDiffOn hU hφ h b 3 (hball.trans fun β hβ => by
    have := (hnorm β hβ).1; exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) this)) bound
  calc _ ≤ K*(X^3)⁻¹*‖h‖^3 := by simpa using hres
    _ = K*‖h‖^3*(X^3)⁻¹ := by ring

end MetaplecticPoisson

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (w : InfinitePlace F)
local notation "vw" => (Sum.inl w : Place F)
local notation "K" => LocalField F vw

private theorem unit_pow_of_field_pow' {A B : Type*} [Field A] [Field B] (e : A ≃+* B) (a : Aˣ)
    {z : B} (hz : z ^ n = e (a : A)) : ∃ u : Aˣ, u ^ n = a := by
  have hz₀ : z ≠ 0 := by
    intro h
    exact (e.injective.ne a.ne_zero) (by simpa [h, zero_pow (NeZero.ne n)] using hz.symm)
  refine ⟨Units.mk0 (e.symm z) (by simpa using hz₀), Units.ext (e.injective ?_)⟩
  simpa using hz

/-- At an infinite place every unit within distance one of one is an n-th power. -/
theorem arch_pow_of_near_one (ρ : Kˣ) (hρ : ‖ρ.val - 1‖ < 1) : ∃ r : Kˣ, r ^ n = ρ := by
  by_cases hw : w.IsReal
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have he := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero e.map_zero
    let x : w.Completion := ρ.val
    have hx : ‖x - 1‖ < 1 := hρ
    have hpos : 0 ≤ e x := by
      have h1 : ‖e x - 1‖ < 1 := by
        have := lt_of_eq_of_lt (he (x - 1)) hx
        simp only [map_sub,map_one] at this
        exact this
      rw [Real.norm_eq_abs,abs_lt] at h1
      linarith
    exact unit_pow_of_field_pow' e ρ (Real.rpow_inv_natCast_pow hpos (NeZero.ne n))
  · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp hw)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e ρ.val) (NeZero.pos n)
    exact unit_pow_of_field_pow' e ρ hz

/-- The symbol at an infinite place is unchanged when the second argument moves by
less than its own norm. -/
theorem arch_symbol_near (a b b' : Kˣ) (hb : ‖b'.val - b.val‖ < ‖b.val‖) :
    d.symbol vw a b' = d.symbol vw a b := by
  obtain ⟨r,hr⟩ := arch_pow_of_near_one (n := n) w (b'/b) (by
    rw [Units.val_div_eq_div_val,div_sub_one b.ne_zero,norm_div]
    exact (div_lt_one (norm_pos_iff.mpr b.ne_zero)).mpr hb)
  have hb' : b' = b * r^n := by rw [hr]; simp
  rw [hb',← coe_unitPairing,← coe_unitPairing,map_mul,map_pow,d.unitPairing_pow,mul_one]

/-- The same for the first argument. -/
theorem arch_symbol_near_left (a a' b : Kˣ) (ha : ‖a'.val - a.val‖ < ‖a.val‖) :
    d.symbol vw a' b = d.symbol vw a b := by
  obtain ⟨r,hr⟩ := arch_pow_of_near_one (n := n) w (a'/a) (by
    rw [Units.val_div_eq_div_val,div_sub_one a.ne_zero,norm_div]
    exact (div_lt_one (norm_pos_iff.mpr a.ne_zero)).mpr ha)
  have ha' : a' = a * r^n := by rw [hr]; simp
  rw [ha',← coe_unitPairing,← coe_unitPairing,map_mul,map_pow,MonoidHom.mul_apply,MonoidHom.pow_apply,
    d.unitPairing_pow,mul_one]

end MetaplecticPoisson.Datum

namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v
local notation "dx" => selfDual F d.character v
local notation "m" => modulus F v

/-- A bound of order three in the ratio of the coordinates on the far part of the
vertical cone gives absolute integrability on the whole vertical region. -/
theorem integrableOn_vertical_of_bound (Ξ : d.schwartz v) {C₀ B : ℝ} (hB : 0 ≤ B)
    (h : ∀ (c : Kˣ) (y : K), m c.val < 1 → C₀ * ‖c.val‖ ≤ ‖y‖ →
      ‖Ξ.val.1 c y‖ ≤ B * (m c.val)^(-growthExponent n) * (‖c.val‖/‖y‖)^3) :
    IntegrableOn (Function.uncurry Ξ.val.1)
      {z : Kˣ × K | m z.1.val < 1 ∧ ‖z.1.val‖ < ‖z.2‖} ((d.lineMeasure v).prod dx) := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let P := {z : Kˣ × K | m z.1.val < 1 ∧ ‖z.1.val‖ < ‖z.2‖}
  have cm : Continuous fun a : Kˣ => m a.val := by
    cases v <;> first | exact Units.continuous_val.norm.pow _ | exact Units.continuous_val.norm
  have hP : MeasurableSet P := (isOpen_lt (cm.comp continuous_fst) continuous_const).measurableSet.inter
    (isOpen_lt (Units.continuous_val.comp continuous_fst).norm continuous_snd.norm).measurableSet
  let G := P.indicator (Function.uncurry Ξ.val.1)
  have hg : StronglyMeasurable G := (d.continuous_schwartz_charts v Ξ).1.stronglyMeasurable.indicator hP
  apply (integrable_indicator_iff hP).mp
  apply (integrable_prod_iff hg.aestronglyMeasurable).mpr
  refine ⟨.of_forall (fun a => (d.integrable_jacquet_slice v Ξ a).norm.mono'
    (hg.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (.of_forall fun y => ?_)),?_⟩
  · change ‖G (a,y)‖ ≤ _
    by_cases hz : (a,y) ∈ P <;> simp [G,hz,Function.uncurry]
  obtain ⟨Cg,hCg,H⟩ := d.schwartz_chart_growth v Ξ 3 (by decide)
  let γ := growthExponent n
  let e := 1/(n:ℝ)
  have he : 0 < e := one_div_pos.mpr (by exact_mod_cast NeZero.pos n)
  have hk : 1 - γ = e := by
    dsimp only [γ,growthExponent,e]; rw [Nat.cast_sub (NeZero.one_le : 1 ≤ n),Nat.cast_one]
    field_simp [show (n:ℝ) ≠ 0 by exact_mod_cast NeZero.ne n]; ring
  let A := max (8*B) (Cg*(1+C₀)^3)
  let J := ∫ t : K, ((1+‖t‖)^3)⁻¹ ∂dx
  apply ((d.integrable_modulus_min_rpow v he).const_mul (A*J)).mono'
    hg.aestronglyMeasurable.norm.integral_prod_right'
  filter_upwards with a
  let r := m a.val
  have hr : 0 < r := by cases v <;> simp [r,modulus,norm_pos_iff,a.ne_zero,pow_pos]
  have hA : 0 ≤ A := le_max_of_le_left (by positivity)
  by_cases ha : r < 1
  swap
  · have hz (y : K) : G (a,y) = 0 := indicator_of_notMem (fun hz => ha hz.1) _
    simp only [hz,norm_zero,integral_zero,norm_zero]
    exact mul_nonneg (mul_nonneg hA (integral_nonneg fun _ => by positivity)) (le_min (by positivity) (by positivity))
  have hmin : min (r^e) (r^(-e)) = r^e :=
    min_eq_left (Real.rpow_le_rpow_of_exponent_ge hr ha.le (by linarith))
  have bound (t : K) : r*‖G (a,a.val*t)‖ ≤ (A*r^e)*((1+‖t‖)^3)⁻¹ := by
    rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
    by_cases hp : (a,a.val*t) ∈ P
    swap
    · rw [show G (a,a.val*t) = 0 from indicator_of_notMem hp _,norm_zero,mul_zero,zero_mul]
      positivity
    rw [show G (a,a.val*t) = Ξ.val.1 a (a.val*t) from indicator_of_mem hp _]
    have ht1 : 1 < ‖t‖ := by
      have := hp.2
      rw [norm_mul] at this
      exact (lt_mul_iff_one_lt_right (norm_pos_iff.mpr a.ne_zero)).mp this
    have hγ : r^(-γ) * r = r^e := by
      rw [← hk,Real.rpow_sub hr,Real.rpow_one,Real.rpow_neg hr.le]; field_simp
    by_cases hfar : C₀ * ‖a.val‖ ≤ ‖a.val*t‖
    · have hb := h a (a.val*t) ha hfar
      have hq : ‖a.val‖/‖a.val*t‖ = ‖t‖⁻¹ := by
        rw [norm_mul,div_mul_eq_div_div,div_self (norm_ne_zero_iff.mpr a.ne_zero),one_div]
      rw [hq] at hb
      have h2 : (1+‖t‖)^3 ≤ 8*‖t‖^3 := by
        have : 1+‖t‖ ≤ 2*‖t‖ := by linarith
        calc (1+‖t‖)^3 ≤ (2*‖t‖)^3 := pow_le_pow_left₀ (by positivity) this 3
          _ = 8*‖t‖^3 := by ring
      have htp : 0 < ‖t‖ := by linarith
      calc r*‖Ξ.val.1 a (a.val*t)‖*(1+‖t‖)^3
          ≤ r*(B*r^(-γ)*(‖t‖⁻¹)^3)*(8*‖t‖^3) := by gcongr
        _ = 8*B*(r^(-γ)*r) := by field_simp
        _ ≤ A*r^e := by rw [hγ]; gcongr; exact le_max_left _ _
    · have hn : (a.val,a.val*t) ≠ (0 : K × K) := fun h => a.ne_zero (congrArg Prod.fst h)
      have hb := (H _ hn).1
      simp only [xChart,ne_eq,a.ne_zero,not_false_eq_true,dite_true,Units.mk0_val] at hb
      have hb' : ‖Ξ.val.1 a (a.val*t)‖ ≤ Cg*r^(-γ) := by
        refine hb.trans (mul_le_mul_of_nonneg_left ((min_le_left _ _).trans ?_) hCg)
        exact Real.rpow_le_rpow_of_nonpos hr (le_max_left _ _) (neg_nonpos.mpr (growthExponent_nonneg n))
      have hnear : ‖t‖ ≤ C₀ := by
        rw [norm_mul] at hfar
        nlinarith [norm_pos_iff.mpr a.ne_zero, not_le.mp hfar]
      calc r*‖Ξ.val.1 a (a.val*t)‖*(1+‖t‖)^3 ≤ r*(Cg*r^(-γ))*(1+C₀)^3 := by gcongr
        _ = Cg*(1+C₀)^3*(r^(-γ)*r) := by ring
        _ ≤ A*r^e := by rw [hγ]; gcongr; exact le_max_right _ _
  have H' := integral_mono_of_nonneg (μ := dx) (.of_forall (fun t => mul_nonneg hr.le (norm_nonneg _)))
    ((d.integrable_local_inv_cube v).const_mul (A*r^e)) (.of_forall bound)
  simp only [integral_const_mul] at H'
  have eqn := d.integral_local_mul v a (fun y => (‖G (a,y)‖ : ℂ))
  rw [eq_div_iff (Complex.ofReal_ne_zero.mpr hr.ne')] at eqn
  simp only [integral_complex_ofReal,← Complex.ofReal_mul,Complex.ofReal_inj] at eqn
  change ‖∫ y, ‖G (a,y)‖ ∂dx‖ ≤ A*J*min (r^e) (r^(-e))
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _),← eqn,mul_comm,hmin]
  exact H'.trans_eq (by dsimp only [J]; ring)


end MetaplecticPoisson.Datum

namespace MetaplecticPoisson
open MeasureTheory Set Metric
open scoped ContDiff

/-- A chart that is rapid on the open half plane where the first coordinate is
nonzero has third differences of order three along each vertical line. -/
theorem rapid_third_difference {K L : Type} [NormedField K] [NormedField L] [NormedAlgebra ℝ L]
    (e : K ≃+* L) (he : Isometry e) {F : L × L → ℂ} (hF : rapidChart {p : L × L | p.1 ≠ 0} F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Kˣ) (y h : K), 6*‖h‖ ≤ ‖y‖ →
      ‖∑ j ∈ Finset.range (3+1), ((-1 : ℤ)^(3-j) * (3:ℕ).choose j) • F (e c.val, e (y + j • h))‖ ≤
        C * ‖h‖^3 * (‖y‖^3)⁻¹ := by
  have norm_e := he.norm_map_of_map_zero e.map_zero
  obtain ⟨C₃,H₃⟩ := hF.2 3 3
  refine ⟨8*max C₃ 0,by positivity,fun c y h hy => ?_⟩
  by_cases hy0 : y = 0
  · have : h = 0 := norm_le_zero_iff.mp (by simp [hy0] at hy; linarith [norm_nonneg h])
    simp [hy0,this,Finset.sum_range_succ]
    ring
  have hyp : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hc : e c.val ≠ 0 := (map_ne_zero e).mpr c.ne_zero
  let φl : L → ℂ := fun s => F (e c.val, s)
  let A : L →L[ℝ] L × L := ContinuousLinearMap.inr ℝ L L
  have hφl : ContDiff ℝ ∞ φl := contDiff_iff_contDiffAt.mpr fun s =>
    (hF.1.contDiffAt ((isOpen_ne_fun continuous_fst continuous_const).mem_nhds (show (e c.val,s).1 ≠ 0 from hc))).comp s
      ((contDiff_const.prodMk contDiff_id).contDiffAt)
  have hsum : ∑ j ∈ Finset.range (3+1), ((-1 : ℤ)^(3-j) * (3:ℕ).choose j) • F (e c.val, e (y + j • h)) =
      (fwdDiff (e h))^[3] φl (e y) := by
    rw [fwdDiff_iter_eq_sum_shift]
    simp only [φl,map_add,map_nsmul]
  rw [hsum]
  have bound (s : L) (hs : s ∈ closedBall (e y) (3*‖e h‖)) :
      ‖iteratedFDeriv ℝ 3 φl s‖ ≤ 8*max C₃ 0*(‖y‖^3)⁻¹ := by
    have hderiv : iteratedFDeriv ℝ 3 φl s =
        (iteratedFDeriv ℝ 3 F (e c.val,s)).compContinuousLinearMap (fun _ => A) := by
      have hU : IsOpen {p : L × L | p.1 ≠ 0} := isOpen_ne_fun continuous_fst continuous_const
      let V := (fun q : L × L => (e c.val,0) + q) ⁻¹' {p : L × L | p.1 ≠ 0}
      have hV : IsOpen V := hU.preimage (continuous_const.add continuous_id)
      have hG : ContDiffOn ℝ ∞ (fun q : L × L => F ((e c.val,0)+q)) V :=
        hF.1.comp ((contDiff_const.add contDiff_id).contDiffOn) (fun _ h => h)
      have pre : A ⁻¹' V = univ := eq_univ_of_forall fun t => by
        change ((e c.val,0) + (0,t)).1 ≠ 0
        simp [hc]
      have hmem : A s ∈ V := by rw [← Set.mem_preimage, pre]; trivial
      have h := A.iteratedFDerivWithin_comp_right hG hV.uniqueDiffOn
        (by rw [pre]; exact uniqueDiffOn_univ) hmem (i := 3) (by simp)
      rw [pre,iteratedFDerivWithin_univ, iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn
        ((hG.contDiffAt (hV.mem_nhds hmem)).of_le (by simp)) hmem,
        iteratedFDeriv_comp_add_left] at h
      convert h using 2
      · funext t; simp [φl,A]
      · simp [A]
    have hp : ‖y‖/2 ≤ ‖(e c.val,s)‖ := by
      rw [mem_closedBall,dist_eq_norm,norm_e] at hs
      have h1 : ‖e y‖ - ‖s - e y‖ ≤ ‖s‖ := by
        have := norm_sub_norm_le (e y) (e y - s); rw [sub_sub_cancel] at this
        rw [norm_sub_rev]; linarith
      rw [norm_e] at h1
      have h2 : ‖s‖ ≤ ‖(e c.val,s)‖ := by rw [Prod.norm_def]; exact le_max_right _ _
      linarith
    have hp0 : 0 < ‖(e c.val,s)‖ := lt_of_lt_of_le (by positivity) hp
    have hd := H₃ (e c.val,s) hc
    rw [hderiv]
    calc ‖(iteratedFDeriv ℝ 3 F (e c.val,s)).compContinuousLinearMap (fun _ => A)‖
        ≤ ‖iteratedFDeriv ℝ 3 F (e c.val,s)‖ * ∏ _ : Fin 3, ‖A‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖iteratedFDeriv ℝ 3 F (e c.val,s)‖ * 1 := by
          gcongr
          rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
          exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one _ _ _)
      _ ≤ max C₃ 0 * ((‖(e c.val,s)‖^3)⁻¹) := by
          rw [mul_one]
          exact hd.trans (mul_le_mul (le_max_left _ _) (min_le_right _ _) (by positivity) (le_max_right _ _))
      _ ≤ max C₃ 0 * (((‖y‖/2)^3)⁻¹) := by gcongr
      _ = 8*max C₃ 0*(‖y‖^3)⁻¹ := by field_simp; ring
  have := norm_fwdDiff_iter_le hφl (e h) (e y) 3 (by simpa using bound)
  rw [norm_e] at this
  calc _ ≤ 8*max C₃ 0*(‖y‖^3)⁻¹*‖h‖^3 := this
    _ = _ := by ring

end MetaplecticPoisson

namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v
local notation "m" => modulus F v

/-- The bound of order three on the far part of the vertical cone for the
third normalized shear difference, as in the proof of Lemma 10.4. -/
def ShearVerticalBound (u : K) (g : d.Operators v) (Φ : d.schwartz v) : Prop :=
  ∃ C₀ B : ℝ, 0 ≤ B ∧ ∀ (c : Kˣ) (y : K), m c.val < 1 → C₀ * ‖c.val‖ ≤ ‖y‖ →
    ‖((d.jacquetDifference v u g)^[3] Φ).val.1 c y‖ ≤ B * (m c.val)^(-growthExponent n) * (‖c.val‖/‖y‖)^3

private theorem iterate_eq_pow (u : K) (g : d.Operators v) (Φ : d.schwartz v) :
    (d.jacquetDifference v u g)^[3] Φ = (d.jacquetDifference v u g ^ 3) Φ :=
  (Module.End.pow_apply _ 3 Φ).symm

theorem shearVerticalBound_add (u : K) (g : d.Operators v) {Φ Ψ : d.schwartz v}
    (hΦ : d.ShearVerticalBound v u g Φ) (hΨ : d.ShearVerticalBound v u g Ψ) :
    d.ShearVerticalBound v u g (Φ + Ψ) := by
  obtain ⟨C₁,B₁,hB₁,h₁⟩ := hΦ
  obtain ⟨C₂,B₂,hB₂,h₂⟩ := hΨ
  refine ⟨max C₁ C₂,B₁+B₂,add_nonneg hB₁ hB₂,fun c y hc hy => ?_⟩
  have hc₁ : C₁*‖c.val‖ ≤ ‖y‖ := (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)).trans hy
  have hc₂ : C₂*‖c.val‖ ≤ ‖y‖ := (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)).trans hy
  rw [iterate_eq_pow,map_add]
  change ‖((d.jacquetDifference v u g ^ 3) Φ).val.1 c y + ((d.jacquetDifference v u g ^ 3) Ψ).val.1 c y‖ ≤ _
  rw [← iterate_eq_pow,← iterate_eq_pow]
  exact (norm_add_le _ _).trans ((add_le_add (h₁ c y hc hc₁) (h₂ c y hc hc₂)).trans_eq (by ring))

theorem shearVerticalBound_smul (u : K) (g : d.Operators v) (r : ℂ) {Φ : d.schwartz v}
    (hΦ : d.ShearVerticalBound v u g Φ) : d.ShearVerticalBound v u g (r • Φ) := by
  obtain ⟨C₁,B₁,hB₁,h₁⟩ := hΦ
  refine ⟨C₁,‖r‖*B₁,by positivity,fun c y hc hy => ?_⟩
  rw [iterate_eq_pow,map_smul]
  change ‖r * ((d.jacquetDifference v u g ^ 3) Φ).val.1 c y‖ ≤ _
  rw [← iterate_eq_pow,norm_mul]
  exact (mul_le_mul_of_nonneg_left (h₁ c y hc hy) (norm_nonneg r)).trans_eq (by ring)

theorem shearVerticalBound_zero (u : K) (g : d.Operators v) : d.ShearVerticalBound v u g 0 := by
  refine ⟨0,0,le_rfl,fun c y _ _ => ?_⟩
  rw [iterate_eq_pow,map_zero]
  simp

variable (w : InfinitePlace F)

/-- Test sections satisfy the bound: their X-chart is smooth on every vertical
line away from the axis, with rapidly decaying third derivatives. -/
theorem shearVerticalBound_test (u : LocalField F (.inl w)) {g : d.Operators (.inl w)}
    (hg : d.IsUpper (.inl w) u g) (Φ : d.schwartz (.inl w)) (hΦ : Φ.val ∈ d.testSet (.inl w)) :
    d.ShearVerticalBound (.inl w) u g Φ := by
  have go {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : LocalField F (.inl w) ≃+* L) (he : Isometry e)
      (htest : archTest e Φ.val) : d.ShearVerticalBound (.inl w) u g Φ := by
    obtain ⟨C,hC,H⟩ := rapid_third_difference e he htest.1
    let a := (d.character.localValue F (.inl w) u - 1)⁻¹
    refine ⟨6*‖u‖,‖a‖^3*C*‖u‖^3,by positivity,fun c y hc hy => ?_⟩
    have hy' : 6*‖u*c.val‖ ≤ ‖y‖ := by rw [norm_mul]; linarith
    have hX := d.jacquetDifference_iterate_X (.inl w) u hg Φ 3 c y
    have hval (y' : LocalField F (.inl w)) :
        (fun p : L × L => xChart Φ.val (e.symm p.1,e.symm p.2)) (e c.val,e y') = Φ.val.1 c y' := by
      simp [xChart,c.ne_zero]
    have hb := H c y (u*c.val) hy'
    simp only [hval] at hb
    rw [hX,norm_mul,norm_pow]
    have hm : 1 ≤ (modulus F (.inl w) c.val)^(-growthExponent n) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by simp [modulus,c.ne_zero,pow_pos])
        hc.le (neg_nonpos.mpr (growthExponent_nonneg n))
    refine (mul_le_mul_of_nonneg_left hb (by positivity)).trans ?_
    have he : ‖a‖^3*(C*‖u*c.val‖^3*(‖y‖^3)⁻¹) = ‖a‖^3*C*‖u‖^3*1*(‖c.val‖/‖y‖)^3 := by
      rw [norm_mul,div_pow]; ring
    rw [he]
    gcongr
  by_cases hw : w.IsReal
  · exact go (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw)
      (by simpa only [testSet,hw,↓reduceDIte] using! hΦ.2)
  · exact go (InfinitePlace.Completion.ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp hw))
      (InfinitePlace.Completion.isometry_extensionEmbedding w)
      (by simpa only [testSet,hw,↓reduceDIte] using! hΦ.2)

end MetaplecticPoisson.Datum

namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "K" => LocalField F v
local notation "dx" => selfDual F d.character v

/-- The Y-chart line integral after the substitution y = βw of the line variable. -/
theorem radon_Y_substituted (f : Charts K) (a : K) (β : Kˣ) (t : K) :
    (radon n (d.symbol v) (modulus F v) dx f t).2 a β =
      ∫ w, lineIntegrandY (d.symbol v) f n t a β (β.val*w) ∂dx := by
  unfold radon
  dsimp only
  rw [← d.integral_local_mul v β]
  rfl

theorem lineIntegrandY_mul (f : Charts K) (a t w : K) (β : Kˣ) (hw : w ≠ 0) :
    lineIntegrandY (d.symbol v) f n t a β (β.val*w) =
      d.symbol v (β * Units.mk0 w hw) β * d.symbol v (-1) β * yChart f (a*w + t^n*β.val⁻¹, β.val*w) := by
  have hβw : β.val*w ≠ 0 := mul_ne_zero β.ne_zero hw
  have hu : Units.mk0 (β.val*w) hβw = β * Units.mk0 w hw := Units.ext rfl
  have hc : (a*(β.val*w) + t^n)/β.val = a*w + t^n*β.val⁻¹ := by field_simp [β.ne_zero]
  simp only [lineIntegrandY,ne_eq,hβw,not_false_eq_true,dite_true,yChart,hc,hu]
  ring

theorem integrable_lineIntegrandY_mul (Φ : d.schwartz v) (a t : K) (β : Kˣ) :
    Integrable (fun w => lineIntegrandY (d.symbol v) Φ.val n t a β (β.val*w)) dx := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  obtain ⟨hx,hy⟩ := d.continuous_schwartz_charts v Φ
  have hi := (d.radon_convergence_of_growth v Φ.val hx hy (d.schwartz_chart_growth v Φ 2 (by decide))).2.1 t a β
  let e := MeasurableEquiv.smul (α := K) β
  apply (e.measurableEmbedding.integrable_map_iff (g := lineIntegrandY (d.symbol v) Φ.val n t a β)).mp
  change Integrable _ (Measure.map (fun w => β.val*w) dx)
  rw [d.map_local_mul]
  exact hi.smul_measure_nnreal

end MetaplecticPoisson.Datum

namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (w : InfinitePlace F)
local notation "vw" => (Sum.inl w : Place F)
local notation "K" => LocalField F vw
local notation "dx" => selfDual F d.character vw

private theorem one_add_le_pow (t : ℝ) (ht : 0 ≤ t) : 1 + t ≤ 2*(1 + t^n) := by
  rcases le_total t 1 with h|h
  · nlinarith [pow_nonneg ht n]
  · nlinarith [le_self_pow₀ h (NeZero.ne n)]

/-- Third differences in the second coordinate of the Y-chart Radon slices of an
Archimedean test section, integrable in the line parameter. -/
theorem radon_Y_third_difference {f : Charts K} (hf : f ∈ d.testSet vw) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (t a : K) (b : Kˣ) (h : K) (bs : ℕ → Kˣ), ‖a‖ ≤ 1 → ‖b.val‖ = 1 → 6*‖h‖ ≤ 1 →
      (∀ j ∈ Finset.range (3+1), (bs j).val = b.val + j • h) →
      ‖∑ j ∈ Finset.range (3+1), ((-1:ℤ)^(3-j) * (3:ℕ).choose j) •
        (radon n (d.symbol vw) (modulus F vw) dx f t).2 a (bs j)‖ ≤ B*‖h‖^3*((1+‖t‖)^3)⁻¹ := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character vw).exists.choose_spec.1
  let Φ : d.schwartz vw := ⟨f,Submodule.subset_span (Or.inl hf)⟩
  have go {L : Type} [NontriviallyNormedField L] [NormedAlgebra ℝ L] [FiniteDimensional ℝ L]
      (e : K ≃+* L) (he : Isometry e) (htest : archTest e f) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (t a : K) (b : Kˣ) (h : K) (bs : ℕ → Kˣ), ‖a‖ ≤ 1 → ‖b.val‖ = 1 → 6*‖h‖ ≤ 1 →
        (∀ j ∈ Finset.range (3+1), (bs j).val = b.val + j • h) →
        ‖∑ j ∈ Finset.range (3+1), ((-1:ℤ)^(3-j) * (3:ℕ).choose j) •
          (radon n (d.symbol vw) (modulus F vw) dx f t).2 a (bs j)‖ ≤ B*‖h‖^3*((1+‖t‖)^3)⁻¹ := by
    have norm_e := he.norm_map_of_map_zero e.map_zero
    let Y : L × L → ℂ := fun p => yChart f (e.symm p.1,e.symm p.2)
    obtain ⟨Kc,hKc,H⟩ := radon_integrand_third_difference (Y := Y) htest.2
    let J := ∫ z : K, ((1+‖z‖)^3)⁻¹ ∂dx
    have hJ : 0 ≤ J := integral_nonneg fun _ => by positivity
    refine ⟨8*Kc*J,by positivity,fun t a b h bs ha hb hh hbs => ?_⟩
    have hnear (j : ℕ) (hj : j ∈ Finset.range (3+1)) : ‖(bs j).val - b.val‖ < ‖b.val‖ := by
      rw [hbs j hj,add_sub_cancel_left,hb]
      have : (j:ℝ) ≤ 3 := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      calc ‖j • h‖ ≤ j*‖h‖ := norm_nsmul_le
        _ ≤ 3*‖h‖ := by gcongr
        _ < 1 := by linarith
    let c (j : ℕ) : ℂ := (((-1:ℤ)^(3-j) * (3:ℕ).choose j : ℤ) : ℂ)
    let G (j : ℕ) (z : K) := lineIntegrandY (d.symbol vw) f n t a (bs j) ((bs j).val*z)
    have hsum : ∑ j ∈ Finset.range (3+1), ((-1:ℤ)^(3-j) * (3:ℕ).choose j) •
        (radon n (d.symbol vw) (modulus F vw) dx f t).2 a (bs j) = ∫ z, ∑ j ∈ Finset.range (3+1), c j * G j z ∂dx := by
      rw [integral_finsetSum _ (fun j _ => (d.integrable_lineIntegrandY_mul vw Φ a t (bs j)).const_mul _)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [zsmul_eq_mul,d.radon_Y_substituted,integral_const_mul]
    rw [hsum]
    let P (z : K) := ((1+‖e (t^n)‖)*(1+‖z‖))^3
    have hpt (z : K) : ‖∑ j ∈ Finset.range (3+1), c j * G j z‖ ≤ Kc*‖h‖^3*(P z)⁻¹ := by
      by_cases hz : z = 0
      · simp only [G,hz,mul_zero,lineIntegrandY,ne_eq,not_true_eq_false,dite_false,Finset.sum_const_zero,norm_zero]
        positivity
      have hconst (j : ℕ) (hj : j ∈ Finset.range (3+1)) : G j z = d.symbol vw (b * Units.mk0 z hz) b *
          d.symbol vw (-1) b * yChart f (a*z + t^n*(bs j).val⁻¹, (bs j).val*z) := by
        simp only [G]
        rw [d.lineIntegrandY_mul vw f a t z (bs j) hz]
        congr 2
        · rw [d.arch_symbol_near w _ b (bs j) (hnear j hj),d.arch_symbol_near_left w _ _ b]
          rw [Units.val_mul,Units.val_mul,← sub_mul,norm_mul,norm_mul]
          exact mul_lt_mul_of_pos_right (hnear j hj) (norm_pos_iff.mpr hz)
        · exact d.arch_symbol_near w _ b (bs j) (hnear j hj)
      set S := d.symbol vw (b * Units.mk0 z hz) b * d.symbol vw (-1) b
      have hS : ‖S‖ = 1 := by simp [S]
      let φl : L → ℂ := fun β => Y (e (a*z) + e (t^n)*β⁻¹, β*e z)
      have hval (j : ℕ) (hj : j ∈ Finset.range (3+1)) :
          φl (e b.val + j • e h) = yChart f (a*z + t^n*(bs j).val⁻¹, (bs j).val*z) := by
        have hb' : e b.val + j • e h = e (bs j).val := by rw [hbs j hj,map_add,map_nsmul]
        simp only [φl,Y,hb',← map_inv₀,← map_mul,← map_add,RingEquiv.symm_apply_apply]
      have hdiff : ∑ j ∈ Finset.range (3+1), c j * G j z = S * (fwdDiff (e h))^[3] φl (e b.val) := by
        rw [fwdDiff_iter_eq_sum_shift,Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [hconst j hj,hval j hj,zsmul_eq_mul]
        simp only [c]
        ring
      rw [hdiff,norm_mul,hS,one_mul]
      have hb1 : ‖e b.val‖ = 1 := by rw [norm_e,hb]
      have hh1 : 6*‖e h‖ ≤ 1 := by rw [norm_e]; exact hh
      have hA : ‖e (a*z)‖ ≤ ‖e z‖ := by
        rw [norm_e,norm_e,norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) ha
      have hz' : e z ≠ 0 := (map_ne_zero e).mpr hz
      refine (H (e (a*z)) (e (t^n)) (e z) (e b.val) (e h) hz' hA hb1 hh1).trans_eq ?_
      simp only [P,norm_e]
    have hmaj : Integrable (fun z : K => (Kc*‖h‖^3*((1+‖e (t^n)‖)^3)⁻¹)*((1+‖z‖)^3)⁻¹) dx :=
      (d.integrable_local_inv_cube vw).const_mul _
    have hle := norm_integral_le_of_norm_le hmaj (.of_forall fun z => (hpt z).trans_eq (by
      simp only [P,mul_pow,mul_inv]; ring))
    rw [integral_const_mul] at hle
    refine hle.trans ?_
    have ht : ‖e (t^n)‖ = ‖t‖^n := by rw [norm_e,norm_pow]
    have h8 : ((1+‖e (t^n)‖)^3)⁻¹ ≤ 8*((1+‖t‖)^3)⁻¹ := by
      rw [ht,← div_eq_mul_inv,← one_div,div_le_div_iff₀ (by positivity) (by positivity),one_mul]
      calc (1+‖t‖)^3 ≤ (2*(1+‖t‖^n))^3 := pow_le_pow_left₀ (by positivity) (one_add_le_pow ‖t‖ (norm_nonneg t)) 3
        _ = 8*(1+‖t‖^n)^3 := by ring
    calc Kc*‖h‖^3*((1+‖e (t^n)‖)^3)⁻¹*J ≤ Kc*‖h‖^3*(8*((1+‖t‖)^3)⁻¹)*J := by gcongr
      _ = 8*Kc*J*‖h‖^3*((1+‖t‖)^3)⁻¹ := by ring
  by_cases hw : w.IsReal
  · exact go (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw)
      (by simpa only [testSet,hw,↓reduceDIte] using! hf.2)
  · exact go (InfinitePlace.Completion.ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp hw))
      (InfinitePlace.Completion.isometry_extensionEmbedding w)
      (by simpa only [testSet,hw,↓reduceDIte] using! hf.2)

/-- Every positive real number is a norm at an infinite place. -/
theorem arch_exists_norm_eq {r : ℝ} (hr : 0 < r) : ∃ μ : Kˣ, ‖μ.val‖ = r := by
  have go {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) (he : Isometry e) :
      ∃ μ : Kˣ, ‖μ.val‖ = r := by
    have hx : e.symm (algebraMap ℝ L r) ≠ 0 := by
      simp [hr.ne']
    refine ⟨Units.mk0 _ hx,?_⟩
    rw [Units.val_mk0,← he.norm_map_of_map_zero e.map_zero,RingEquiv.apply_symm_apply,norm_algebraMap',
      Real.norm_eq_abs,abs_of_pos hr]
  by_cases hw : w.IsReal
  · exact go (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw)
  · exact go (InfinitePlace.Completion.ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp hw))
      (InfinitePlace.Completion.isometry_extensionEmbedding w)

/-- Transforms of Archimedean test sections satisfy the bound on the far part of
the vertical cone: the power-ray formula turns the third difference into the
Fourier integral of a third difference of Radon slices. -/
theorem shearVerticalBound_transform (u : K) {g : d.Operators vw} (hg : d.IsUpper vw u g)
    {f : Charts K} (hf : f ∈ d.testSet vw) :
    d.ShearVerticalBound vw u g ⟨d.integralTransform vw f,Submodule.subset_span (Or.inr ⟨f,hf,rfl⟩)⟩ := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character vw).exists.choose_spec.1
  let Ψ : d.schwartz vw := ⟨d.integralTransform vw f,Submodule.subset_span (Or.inr ⟨f,hf,rfl⟩)⟩
  let Φ : d.schwartz vw := ⟨f,Submodule.subset_span (Or.inl hf)⟩
  obtain ⟨B,hB,HB⟩ := d.radon_Y_third_difference w hf
  let Jt := ∫ t : K, ((1+‖t‖)^3)⁻¹ ∂dx
  have hJt : 0 ≤ Jt := integral_nonneg fun _ => by positivity
  let ac := (d.character.localValue F vw u - 1)⁻¹
  let cn : ℂ := (Real.sqrt (modulus F vw (n : K)))⁻¹
  refine ⟨6*‖u‖+1,‖ac‖^3*(‖cn‖*(B*Jt))*‖u‖^3,by positivity,fun c y hc hy => ?_⟩
  have hcpos : 0 < ‖c.val‖ := norm_pos_iff.mpr c.ne_zero
  have hcy : ‖c.val‖ ≤ ‖y‖ := by nlinarith [norm_nonneg u]
  have hyp : 0 < ‖y‖ := hcpos.trans_le hcy
  have hy0 : y ≠ 0 := norm_pos_iff.mp hyp
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  obtain ⟨μ,hμ⟩ := arch_exists_norm_eq w (r := ‖y‖^((n:ℝ)⁻¹)) (by positivity)
  let N : Kˣ := μ^n
  have hN : ‖N.val‖ = ‖y‖ := by
    rw [Units.val_pow_eq_pow_val,norm_pow,hμ,← Real.rpow_natCast,← Real.rpow_mul hyp.le,
      inv_mul_cancel₀ hn0,Real.rpow_one]
  let a' : Kˣ := c / N
  let h' : K := u * a'.val
  let b0 : Kˣ := Units.mk0 (y / N.val) (div_ne_zero hy0 N.ne_zero)
  have hb0 : ‖b0.val‖ = 1 := by simp [b0,norm_div,hN,hyp.ne']
  have ha' : ‖a'.val‖ = ‖c.val‖/‖y‖ := by simp [a',norm_div,hN]
  have ha'1 : ‖a'.val‖ ≤ 1 := by rw [ha']; exact div_le_one_of_le₀ hcy hyp.le
  have hh' : ‖h'‖ = ‖u‖*(‖c.val‖/‖y‖) := by rw [norm_mul,ha']
  have hh'6 : 6*‖h'‖ ≤ 1 := by
    rw [hh',← mul_assoc,mul_div_assoc',div_le_one hyp]; nlinarith [norm_nonneg u]
  have hbs_ne (j : ℕ) (hj : j ∈ Finset.range (3+1)) : b0.val + j • h' ≠ 0 := by
    have hj3 : (j:ℝ) ≤ 3 := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    intro h0
    have : ‖j • h'‖ = 1 := by rw [eq_neg_of_add_eq_zero_right h0,norm_neg,hb0]
    have : ‖j • h'‖ ≤ 1/2 := norm_nsmul_le.trans (by nlinarith [norm_nonneg h'])
    linarith
  let bs : ℕ → Kˣ := fun j => if hj : b0.val + j • h' ≠ 0 then Units.mk0 _ hj else 1
  have hbs (j : ℕ) (hj : j ∈ Finset.range (3+1)) : (bs j).val = b0.val + j • h' := by
    simp only [bs,ne_eq,hbs_ne j hj,not_false_eq_true,dite_true,Units.val_mk0]
  have hpoint (j : ℕ) (hj : j ∈ Finset.range (3+1)) :
      Ψ.val.1 c (y + j • (u*c.val)) = Ψ.val.1 (μ^n * a') (μ.val^n * (bs j).val) := by
    have h1 : μ^n * a' = c := by simp [a',N]
    have h2 : μ.val^n * (bs j).val = y + j • (u*c.val) := by
      rw [hbs j hj]
      simp only [b0,h',a',N,Units.val_mk0,Units.val_div_eq_div_val,Units.val_pow_eq_pow_val,nsmul_eq_mul]
      field_simp [pow_ne_zero n μ.ne_zero]
    rw [h1,h2]
  let R := radon n (d.symbol vw) (modulus F vw) dx f
  let ψ := d.character.localValue F vw
  have hmμ : 0 < modulus F vw μ.val := by simp [modulus,μ.ne_zero,pow_pos]
  let M : ℂ := (modulus F vw μ.val : ℂ)^(n-1)
  have hM : M ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hmμ.ne')
  have hray (j : ℕ) (hj : j ∈ Finset.range (3+1)) :
      Ψ.val.1 c (y + j • (u*c.val)) = M⁻¹ * (cn * ∫ t, (R t).1 a' (bs j).val * ψ (μ.val*t) ∂dx) := by
    rw [hpoint j hj,eq_inv_mul_iff_mul_eq₀ hM]
    exact (d.transform_pow_ray vw f μ).1 a' (bs j).val
  have hint (b : K) : Integrable (fun t => (R t).1 a' b * ψ (μ.val*t)) dx := by
    have hi := (d.schwartz_radon_rapid vw Φ).1.integrable dx (d.integrable_local_inv_cube vw) (a',b)
    exact hi.norm.mono' (hi.aestronglyMeasurable.mul ((d.character.continuous_localValue vw).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable)
      (.of_forall fun t => by rw [norm_mul,d.character.norm_localValue,mul_one])
  have hX := d.jacquetDifference_iterate_X vw u hg Ψ 3 c y
  let co (j : ℕ) : ℂ := (((-1:ℤ)^(3-j) * (3:ℕ).choose j : ℤ) : ℂ)
  have hsum : ∑ j ∈ Finset.range (3+1), ((-1:ℤ)^(3-j) * (3).choose j) • Ψ.val.1 c (y + j • (u*c.val)) =
      M⁻¹ * (cn * ∫ t, (∑ j ∈ Finset.range (3+1), co j * (R t).1 a' (bs j).val) * ψ (μ.val*t) ∂dx) := by
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ (fun j _ => by simpa only [mul_assoc] using (hint _).const_mul (co j)),
      Finset.mul_sum,Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [zsmul_eq_mul,hray j hj]
    simp only [mul_assoc,integral_const_mul]
    ring
  rw [hX,hsum]
  -- Gluing and symbol constancy replace the X-chart slices by Y-chart slices.
  have hglue (t : K) : ∑ j ∈ Finset.range (3+1), co j * (R t).1 a' (bs j).val =
      d.symbol vw a' b0 * ∑ j ∈ Finset.range (3+1), ((-1:ℤ)^(3-j) * (3:ℕ).choose j) • (R t).2 a' (bs j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hgl := d.radon_glues vw hf.1 t a' (bs j)
    have hnear : ‖(bs j).val - b0.val‖ < ‖b0.val‖ := by
      have hj3 : (j:ℝ) ≤ 3 := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [hbs j hj,add_sub_cancel_left,hb0]
      exact norm_nsmul_le.trans_lt (by nlinarith [norm_nonneg h'])
    rw [hgl,d.arch_symbol_near w a' b0 (bs j) hnear,zsmul_eq_mul]
    simp only [co]
    ring
  have hbound (t : K) : ‖(∑ j ∈ Finset.range (3+1), co j * (R t).1 a' (bs j).val) * ψ (μ.val*t)‖ ≤
      B*‖h'‖^3*((1+‖t‖)^3)⁻¹ := by
    rw [norm_mul,d.character.norm_localValue,mul_one,hglue,norm_mul,norm_symbol,one_mul]
    exact HB t a'.val b0 h' bs ha'1 hb0 hh'6 hbs
  have hI := norm_integral_le_of_norm_le ((d.integrable_local_inv_cube vw).const_mul (B*‖h'‖^3))
    (.of_forall hbound)
  rw [integral_const_mul] at hI
  -- The modulus of the ray parameter is controlled by that of c.
  have hγ : ‖M⁻¹‖ ≤ (modulus F vw c.val)^(-growthExponent n) := by
    let k := w.mult
    have hmc : modulus F vw c.val = ‖c.val‖^k := rfl
    have hmμ' : modulus F vw μ.val = ‖μ.val‖^k := rfl
    have hγpos : 0 ≤ growthExponent n := growthExponent_nonneg n
    have hMn : ‖M⁻¹‖ = ((modulus F vw μ.val)^(n-1))⁻¹ := by
      rw [norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg hmμ.le]
    have heq : (modulus F vw μ.val)^(n-1) = (‖y‖^k)^(growthExponent n) := by
      rw [hmμ',hμ,← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_mul hyp.le,← Real.rpow_mul hyp.le,
        ← Real.rpow_natCast,← Real.rpow_mul hyp.le]
      congr 1
      simp only [growthExponent]
      rw [Nat.cast_sub (NeZero.one_le : 1 ≤ n),Nat.cast_one]
      field_simp
    have hle : (‖c.val‖^k)^(growthExponent n) ≤ (‖y‖^k)^(growthExponent n) :=
      Real.rpow_le_rpow (by positivity) (pow_le_pow_left₀ (norm_nonneg _) hcy k) hγpos
    rw [hMn,heq,hmc,Real.rpow_neg (by positivity)]
    exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _) hle
  rw [norm_mul,norm_pow,norm_mul,norm_mul]
  calc ‖(d.character.localValue F vw u - 1)⁻¹‖^3 * (‖M⁻¹‖ * (‖cn‖ *
        ‖∫ t, (∑ j ∈ Finset.range (3+1), co j * (R t).1 a' (bs j).val) * ψ (μ.val*t) ∂dx‖))
      ≤ ‖ac‖^3 * ((modulus F vw c.val)^(-growthExponent n) * (‖cn‖ * (B*‖h'‖^3*Jt))) := by
        have : 0 ≤ (modulus F vw c.val)^(-growthExponent n) := Real.rpow_nonneg (by simp [modulus]) _
        gcongr
    _ = ‖ac‖^3*(‖cn‖*(B*Jt))*‖u‖^3 * (modulus F vw c.val)^(-growthExponent n) * (‖c.val‖/‖y‖)^3 := by
        rw [hh']; ring

/-- The bound on the far part of the vertical cone for every Archimedean Schwartz
section, by linearity from tests and transformed tests. -/
theorem shearVerticalBound_arch (u : K) {g : d.Operators vw} (hg : d.IsUpper vw u g) (Φ : d.schwartz vw) :
    d.ShearVerticalBound vw u g Φ := by
  obtain ⟨f,hf⟩ := Φ
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with hf|⟨f,hf,rfl⟩
    · exact d.shearVerticalBound_test w u hg ⟨f,_⟩ hf
    · exact d.shearVerticalBound_transform w u hg hf
  | zero => exact d.shearVerticalBound_zero vw u g
  | add f₁ f₂ h₁ h₂ ih₁ ih₂ =>
    have he : (⟨f₁+f₂,add_mem h₁ h₂⟩ : d.schwartz vw) = ⟨f₁,h₁⟩ + ⟨f₂,h₂⟩ := rfl
    rw [he]
    exact d.shearVerticalBound_add vw u g ih₁ ih₂
  | smul r f hf ih =>
    have he : (⟨r • f,Submodule.smul_mem _ r hf⟩ : d.schwartz vw) = r • ⟨f,hf⟩ := rfl
    rw [he]
    exact d.shearVerticalBound_smul vw u g r ih

end MetaplecticPoisson.Datum
