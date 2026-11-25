import MetaplecticSummation.ArchimedeanSlice

/-! Joint smoothness of the archimedean line integrals of §4 (Lemma 4.2(iii), Proposition 4.5).

Substituting x = x′z in the X-chart line integral makes the dependence on the parameters
linear: the integrand at z is the chart composed with P = (U, V, Σ) ↦ (zU, zV − Σ). An integrable
majorant for every derivative on sets where U is bounded away from zero then lets all
derivatives pass under the integral (`smooth_fiber_integral_on`). The Fourier integral in
the determinant variable is handled the same way, with the parameter W = 1/x′ scaling the
last coordinate linearly. -/

noncomputable section
namespace MetaplecticPoisson
open MeasureTheory Set Filter
open scoped Topology ContDiff

section FiberOn
variable {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} {g : X → E → ℂ}

/-- The local form of `smooth_fiber_integral`: majorants on an open set of parameters. -/
theorem smooth_fiber_integral_on {Ω : Set E} (hΩ : IsOpen Ω)
    (hs : ∀ x, ContDiffOn ℝ ∞ (g x) Ω)
    (hm : ∀ k, ∀ t ∈ Ω, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ k (g x) t) μ)
    (hb : ∀ k, ∃ b : X → ℝ, Integrable b μ ∧ ∀ x, ∀ t ∈ Ω, ‖iteratedFDeriv ℝ k (g x) t‖ ≤ b x) :
    ContDiffOn ℝ ∞ (fun t => ∫ x, g x t ∂μ) Ω ∧
    ∀ k, ∀ t ∈ Ω, iteratedFDeriv ℝ k (fun t => ∫ x, g x t ∂μ) t =
      ∫ x, iteratedFDeriv ℝ k (g x) t ∂μ := by
  have hi (k : ℕ) (t : E) (ht : t ∈ Ω) : Integrable (fun x => iteratedFDeriv ℝ k (g x) t) μ := by
    obtain ⟨b, hbi, h⟩ := hb k
    exact hbi.mono' (hm k t ht) (.of_forall (fun x => h x t ht))
  have hd (k : ℕ) (t : E) (ht : t ∈ Ω) :
      HasFDerivAt (fun u => ∫ x, iteratedFDeriv ℝ k (g x) u ∂μ)
        (∫ x, fderiv ℝ (iteratedFDeriv ℝ k (g x)) t ∂μ) t := by
    obtain ⟨b, hbi, h⟩ := hb (k+1)
    let c := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) ℂ
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Ω) (hΩ.mem_nhds ht)
      (eventually_of_mem (hΩ.mem_nhds ht) (hm k)) (hi k t ht) (bound := b)
    · have H := c.continuous.comp_aestronglyMeasurable (hm (k+1) t ht)
      simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def, c,
        LinearIsometryEquiv.apply_symm_apply] using H
    · exact .of_forall (fun x u hu => by simpa only [iteratedFDeriv_succ_eq_comp_left,
        Function.comp_apply, LinearIsometryEquiv.norm_map] using h x u hu)
    · exact hbi
    · refine .of_forall (fun x u hu => ?_)
      have hc : ContDiffAt ℝ ∞ (g x) u := (hs x).contDiffAt (hΩ.mem_nhds hu)
      exact (hc.differentiableAt_iteratedFDeriv
        (show ((k : ℕ∞) : WithTop ℕ∞) < ∞ by exact_mod_cast ENat.natCast_lt_top k)).hasFDerivAt
  have eqn (k : ℕ) : EqOn (iteratedFDeriv ℝ k (fun t => ∫ x, g x t ∂μ))
      (fun t => ∫ x, iteratedFDeriv ℝ k (g x) t ∂μ) Ω := by
    induction k with
    | zero =>
      intro t _
      simp_rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℝ E ℂ).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
    | succ k ih =>
      intro t ht
      have hev : iteratedFDeriv ℝ k (fun t => ∫ x, g x t ∂μ) =ᶠ[𝓝 t]
          fun t => ∫ x, iteratedFDeriv ℝ k (g x) t ∂μ :=
        eventually_of_mem (hΩ.mem_nhds ht) ih
      simp_rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hev.fderiv_eq, (hd k t ht).fderiv]
      exact (ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (E := E →L[ℝ] (E [×k]→L[ℝ] ℂ))
        (F := E [×(k+1)]→L[ℝ] ℂ) ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) ℂ).symm.toContinuousLinearEquiv)
        (fun x => fderiv ℝ (iteratedFDeriv ℝ k (g x)) t) (μ := μ)).symm
  refine ⟨contDiffOn_of_differentiableOn (fun k _ => ?_), eqn⟩
  intro t ht
  refine ((hd k t ht).differentiableAt.congr_of_eventuallyEq ?_).differentiableWithinAt
  exact eventually_of_mem (hΩ.mem_nhds ht) fun u hu =>
    (iteratedFDerivWithin_of_isOpen k hΩ hu).trans (eqn k hu)

end FiberOn

section Helpers
variable {E F' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F'] [NormedSpace ℝ F']

theorem iteratedFDeriv_comp_clm_of_isOpen {W : Set F'} (hW : IsOpen W) {f : F' → ℂ}
    (hf : ContDiffOn ℝ ∞ f W) (A : E →L[ℝ] F') {P : E} (hP : A P ∈ W) (k : ℕ) :
    iteratedFDeriv ℝ k (f ∘ A) P = (iteratedFDeriv ℝ k f (A P)).compContinuousLinearMap (fun _ => A) := by
  have hV : IsOpen (A ⁻¹' W) := hW.preimage A.continuous
  have h := A.iteratedFDerivWithin_comp_right hf hW.uniqueDiffOn hV.uniqueDiffOn hP (i := k)
    (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen k hV hP,iteratedFDerivWithin_of_isOpen k hW hP] at h
  exact h

end Helpers

variable {L : Type} [NormedField L] [NormedAlgebra ℝ L]

/-- The linear map P = (U, V, Σ) ↦ (aU, aV − Σ) parametrizing the substituted lines. -/
def lineAffine (a : L) : (L × L × L) →L[ℝ] (L × L) :=
  ((ContinuousLinearMap.lsmul ℝ L a).comp (ContinuousLinearMap.fst ℝ L (L × L))).prod
    ((ContinuousLinearMap.lsmul ℝ L a).comp ((ContinuousLinearMap.fst ℝ L L).comp
      (ContinuousLinearMap.snd ℝ L (L × L))) -
      (ContinuousLinearMap.snd ℝ L L).comp (ContinuousLinearMap.snd ℝ L (L × L)))

@[simp] theorem lineAffine_apply (a : L) (P : L × L × L) :
    lineAffine a P = (a * P.1, a * P.2.1 - P.2.2) := by
  simp [lineAffine,smul_eq_mul]

theorem norm_lineAffine_le (a : L) : ‖lineAffine a‖ ≤ ‖a‖ + 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun P => ?_
  have h1 : ‖P.1‖ ≤ ‖P‖ := norm_fst_le P
  have h2 : ‖P.2.1‖ ≤ ‖P‖ := (norm_fst_le P.2).trans (norm_snd_le P)
  have h3 : ‖P.2.2‖ ≤ ‖P‖ := (norm_snd_le P.2).trans (norm_snd_le P)
  rw [lineAffine_apply,Prod.norm_def]
  refine max_le ?_ ?_
  · rw [norm_mul]; nlinarith [norm_nonneg a,norm_nonneg P]
  · calc ‖a * P.2.1 - P.2.2‖ ≤ ‖a‖ * ‖P.2.1‖ + ‖P.2.2‖ := (norm_sub_le _ _).trans (by rw [norm_mul])
      _ ≤ _ := by nlinarith [norm_nonneg a,norm_nonneg P]

theorem continuous_lineAffine : Continuous (lineAffine (L := L)) := by
  refine (LipschitzWith.of_dist_le_mul fun a b => ?_).continuous (K := 1)
  rw [dist_eq_norm,dist_eq_norm,NNReal.coe_one,one_mul]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun P => ?_
  have h1 : ‖P.1‖ ≤ ‖P‖ := norm_fst_le P
  have h2 : ‖P.2.1‖ ≤ ‖P‖ := (norm_fst_le P.2).trans (norm_snd_le P)
  rw [sub_apply,lineAffine_apply,lineAffine_apply,Prod.norm_def]
  refine max_le ?_ ?_
  · rw [Prod.fst_sub,← sub_mul,norm_mul]; exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  · rw [Prod.snd_sub,show a * P.2.1 - P.2.2 - (b * P.2.1 - P.2.2) = (a - b) * P.2.1 by ring,norm_mul]
    exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

theorem continuous_compContinuousLinearMap_const {E F' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {X : Type} [TopologicalSpace X] {S : Set X} (k : ℕ)
    {φ : X → ContinuousMultilinearMap ℝ (fun _ : Fin k => F') ℂ} {A : X → E →L[ℝ] F'}
    (hφ : ContinuousOn φ S) (hA : ContinuousOn A S) :
    ContinuousOn (fun x => (φ x).compContinuousLinearMap (fun _ => A x)) S := by
  let T := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin k => E) (fun _ : Fin k => F') ℂ
  have hT : ContinuousOn (fun x => T (fun _ => A x)) S :=
    T.coe_continuous.comp_continuousOn (continuousOn_pi.mpr fun _ => hA)
  exact (hT.clm_apply hφ).congr fun x _ => rfl

section Core
variable {K : Type} [NormedField K] [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

open Classical in
/-- The Radon chart after the substitution x = x′z: the parameters enter linearly. -/
def lineRadon (μ : Measure K) (e : K ≃+* L) (c : K → L → ℂ) (f : L × L → ℂ) (P : L × L × L) : ℂ :=
  ∫ z, (if z = 0 then 0 else c z P.1 * f (lineAffine (e z) P)) ∂μ

/-- Lemma 4.2(iii) at a real or complex place, in the linearized coordinates: the line integral
of a rapid chart is smooth, and every derivative decays rapidly in the determinant variable,
uniformly for U bounded away from zero and V bounded. -/
theorem lineRadon_smooth (μ : Measure K) (e : K ≃+* L) (he : Isometry e)
    (hint : Integrable (fun x : K => ((1+‖x‖)^3)⁻¹) μ)
    {f : L × L → ℂ} (hf : rapidChart {p | p.1 ≠ 0} f) (c : K → L → ℂ)
    (hloc : ∀ z, z ≠ 0 → ∀ U : L, U ≠ 0 → ∀ᶠ U' in 𝓝 U, c z U' = c z U)
    (hcont : ∀ U : L, U ≠ 0 → ContinuousOn (fun z => c z U) {z | z ≠ 0})
    (hnorm : ∀ z U, ‖c z U‖ ≤ 1) :
    ContDiffOn ℝ ∞ (lineRadon μ e c f) {P | P.1 ≠ 0} ∧
    ∀ k M : ℕ, ∀ δ B : ℝ, 0 < δ → ∃ C : ℝ, ∀ P : L × L × L, δ ≤ ‖P.1‖ → ‖P.2.1‖ ≤ B →
      ‖iteratedFDeriv ℝ k (lineRadon μ e c f) P‖ * (1+‖P.2.2‖)^M ≤ C := by
  classical
  let g (z : K) (P : L × L × L) : ℂ := if z = 0 then 0 else c z P.1 * f (lineAffine (e z) P)
  let W : Set (L × L) := {p | p.1 ≠ 0}
  have hW : IsOpen W := isOpen_ne_fun continuous_fst continuous_const
  have norm_e := he.norm_map_of_map_zero e.map_zero
  have hmem (z : K) (hz : z ≠ 0) (P : L × L × L) (hP : P.1 ≠ 0) : lineAffine (e z) P ∈ W := by
    simp only [W,mem_ofPred_eq,lineAffine_apply]
    exact mul_ne_zero ((map_ne_zero e).mpr hz) hP
  have hfA (z : K) (hz : z ≠ 0) (P : L × L × L) (hP : P.1 ≠ 0) :
      ContDiffAt ℝ ∞ (f ∘ lineAffine (e z)) P :=
    (hf.1.contDiffAt (hW.mem_nhds (hmem z hz P hP))).comp P (lineAffine (e z)).contDiff.contDiffAt
  have hev (z : K) (hz : z ≠ 0) (P : L × L × L) (hP : P.1 ≠ 0) :
      g z =ᶠ[𝓝 P] (c z P.1 • (f ∘ lineAffine (e z)) : L × L × L → ℂ) := by
    filter_upwards [continuous_fst.continuousAt.eventually (hloc z hz P.1 hP)] with Q hQ
    simp [g,hz,hQ,smul_eq_mul]
  have deriv (z : K) (hz : z ≠ 0) (P : L × L × L) (hP : P.1 ≠ 0) (k : ℕ) :
      iteratedFDeriv ℝ k (g z) P = c z P.1 •
        (iteratedFDeriv ℝ k f (lineAffine (e z) P)).compContinuousLinearMap (fun _ => lineAffine (e z)) := by
    rw [((hev z hz P hP).iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds,
      iteratedFDeriv_const_smul_apply ((hfA z hz P hP).of_le (by exact_mod_cast le_top)),
      iteratedFDeriv_comp_clm_of_isOpen hW hf.1 _ (hmem z hz P hP)]
  let Ω (δ B : ℝ) : Set (L × L × L) := {P | δ < ‖P.1‖ ∧ ‖P.2.1‖ < B}
  have hΩ (δ B : ℝ) : IsOpen (Ω δ B) :=
    (isOpen_lt continuous_const continuous_fst.norm).inter
      (isOpen_lt (continuous_fst.comp continuous_snd).norm continuous_const)
  have hΩne (δ B : ℝ) (hδ : 0 ≤ δ) (P) (hP : P ∈ Ω δ B) : P.1 ≠ 0 :=
    norm_pos_iff.mp (hδ.trans_lt hP.1)
  have hs (δ B : ℝ) (hδ : 0 ≤ δ) (z : K) : ContDiffOn ℝ ∞ (g z) (Ω δ B) := by
    intro P hP
    by_cases hz : z = 0
    · have : g z = fun _ => 0 := by funext Q; simp [g,hz]
      rw [this]; exact contDiffWithinAt_const
    exact ((hfA z hz P (hΩne δ B hδ P hP)).const_smul (c z P.1)).congr_of_eventuallyEq
      (hev z hz P (hΩne δ B hδ P hP)) |>.contDiffWithinAt
  have hm (δ B : ℝ) (hδ : 0 ≤ δ) (k : ℕ) (P) (hP : P ∈ Ω δ B) :
      AEStronglyMeasurable (fun z => iteratedFDeriv ℝ k (g z) P) μ := by
    have hP0 := hΩne δ B hδ P hP
    let V : Set K := {z | z ≠ 0}
    have hV : MeasurableSet V := (measurableSet_singleton 0).compl
    have hA : Continuous fun z : K => lineAffine (e z) := continuous_lineAffine.comp he.continuous
    have hDf : ContinuousOn (iteratedFDeriv ℝ k f) W := by
      have h := hf.1.continuousOn_iteratedFDerivWithin (m := k) (by exact_mod_cast le_top) hW.uniqueDiffOn
      exact h.congr fun u hu => (iteratedFDerivWithin_of_isOpen k hW hu).symm
    have hφ : ContinuousOn (fun z : K => iteratedFDeriv ℝ k f (lineAffine (e z) P)) V :=
      hDf.comp (hA.clm_apply continuous_const).continuousOn (fun z hz => hmem z hz P hP0)
    have hc := ((hcont P.1 hP0).smul (continuous_compContinuousLinearMap_const k hφ hA.continuousOn)).congr
      (fun z hz => deriv z hz P hP0 k)
    rw [← Measure.restrict_add_restrict_compl (μ := μ) (measurableSet_singleton (0 : K))]
    exact aestronglyMeasurable_add_measure_iff.mpr
      ⟨(continuousOn_singleton _ _).aestronglyMeasurable (measurableSet_singleton _),
        hc.aestronglyMeasurable hV⟩
  have bound (δ B : ℝ) (hδ : 0 < δ) (k M : ℕ) : ∃ b : K → ℝ, Integrable b μ ∧
      ∀ z, ∀ P ∈ Ω δ B, ‖iteratedFDeriv ℝ k (g z) P‖ * (1+‖P.2.2‖)^M ≤ b z := by
    obtain ⟨C,hC0,hC⟩ := rapidChart_derivative_polynomial hf k (k+3+M)
    let κ := (1 + 1/δ)^(k+3) * (1 + B/δ)^M * C
    refine ⟨fun z => κ * ((1+‖z‖)^3)⁻¹,hint.const_mul κ,fun z P hP => ?_⟩
    have hB : 0 < B := (norm_nonneg _).trans_lt hP.2
    have hκ : 0 ≤ κ := by positivity
    by_cases hz : z = 0
    · have : g z = fun _ => 0 := by funext Q; simp [g,hz]
      rw [this,iteratedFDeriv_fun_zero]
      simp only [Pi.zero_apply,norm_zero,zero_mul]
      positivity
    have hP0 := hΩne δ B hδ.le P hP
    set u := lineAffine (e z) P
    have hu1 : ‖z‖ * δ ≤ ‖u‖ := by
      calc ‖z‖ * δ ≤ ‖z‖ * ‖P.1‖ := mul_le_mul_of_nonneg_left hP.1.le (norm_nonneg _)
        _ = ‖u.1‖ := by simp [u,norm_e]
        _ ≤ ‖u‖ := norm_fst_le u
    have hz1 : 1 + ‖z‖ ≤ (1 + 1/δ) * (1 + ‖u‖) := by
      have : ‖z‖ ≤ ‖u‖ / δ := by rw [le_div_iff₀ hδ]; exact hu1
      have h2 : ‖u‖ / δ = 1/δ * ‖u‖ := by ring
      nlinarith [norm_nonneg u, one_div_nonneg.mpr hδ.le]
    have hs1 : 1 + ‖P.2.2‖ ≤ (1 + B/δ) * (1 + ‖u‖) := by
      have e1 : P.2.2 = e z * P.2.1 - u.2 := by simp [u]
      have h1 : ‖P.2.2‖ ≤ ‖z‖ * B + ‖u‖ := by
        rw [e1]
        calc ‖e z * P.2.1 - u.2‖ ≤ ‖e z * P.2.1‖ + ‖u.2‖ := norm_sub_le _ _
          _ ≤ ‖z‖ * B + ‖u‖ := by
            rw [norm_mul,norm_e]
            exact add_le_add (mul_le_mul_of_nonneg_left hP.2.le (norm_nonneg _)) (norm_snd_le u)
      have h2 : ‖z‖ * B ≤ ‖u‖ * (B/δ) := by
        rw [mul_div_assoc', le_div_iff₀ hδ]; nlinarith [hu1, hB]
      nlinarith [norm_nonneg u, div_nonneg hB.le hδ.le]
    have hder : ‖iteratedFDeriv ℝ k (g z) P‖ ≤ ‖iteratedFDeriv ℝ k f u‖ * (1+‖z‖)^k := by
      rw [deriv z hz P hP0 k,norm_smul]
      have h := (iteratedFDeriv ℝ k f u).norm_compContinuousLinearMap_le (fun _ : Fin k => lineAffine (e z))
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
      have hA : ‖lineAffine (e z)‖ ≤ 1 + ‖z‖ := by
        have := norm_lineAffine_le (e z); rw [norm_e] at this; linarith
      calc ‖c z P.1‖ * ‖(iteratedFDeriv ℝ k f u).compContinuousLinearMap fun _ => lineAffine (e z)‖
          ≤ 1 * (‖iteratedFDeriv ℝ k f u‖ * ‖lineAffine (e z)‖^k) :=
            mul_le_mul (hnorm z P.1) h (norm_nonneg _) zero_le_one
        _ ≤ _ := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hA k) (norm_nonneg _)
    have hu := hC u (hmem z hz P hP0)
    change _ ≤ κ * ((1 + ‖z‖)^3)⁻¹
    rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
    calc ‖iteratedFDeriv ℝ k (g z) P‖ * (1 + ‖P.2.2‖)^M * (1+‖z‖)^3
        ≤ ‖iteratedFDeriv ℝ k f u‖ * (1+‖z‖)^k * ((1 + B/δ) * (1 + ‖u‖))^M * (1+‖z‖)^3 := by
          gcongr
      _ = ‖iteratedFDeriv ℝ k f u‖ * (1+‖z‖)^(k+3) * ((1 + B/δ) * (1 + ‖u‖))^M := by ring
      _ ≤ ‖iteratedFDeriv ℝ k f u‖ * ((1 + 1/δ) * (1 + ‖u‖))^(k+3) * ((1 + B/δ) * (1 + ‖u‖))^M := by
          gcongr
      _ = (1 + 1/δ)^(k+3) * (1 + B/δ)^M * (‖iteratedFDeriv ℝ k f u‖ * (1+‖u‖)^(k+3+M)) := by
          rw [mul_pow,mul_pow]; ring
      _ ≤ κ := mul_le_mul_of_nonneg_left hu (by positivity)
  have fiber (δ B : ℝ) (hδ : 0 < δ) := smooth_fiber_integral_on (μ := μ) (hΩ δ B) (hs δ B hδ.le)
    (hm δ B hδ.le) (fun k => by
      obtain ⟨b,hb,h⟩ := bound δ B hδ k 0
      exact ⟨b,hb,fun z P hP => by simpa using h z P hP⟩)
  have hR : lineRadon μ e c f = fun P => ∫ z, g z P ∂μ := rfl
  refine ⟨fun P hP => ?_,fun k M δ B hδ => ?_⟩
  · have hP' : P.1 ≠ 0 := hP
    have hmemΩ : P ∈ Ω (‖P.1‖/2) (‖P.2.1‖+1) :=
      ⟨by linarith [norm_pos_iff.mpr hP'],by linarith⟩
    rw [hR]
    exact ((fiber _ _ (by positivity)).1.contDiffAt ((hΩ _ _).mem_nhds hmemΩ)).contDiffWithinAt
  · obtain ⟨b,hb,h⟩ := bound (δ/2) (B+1) (by positivity) k M
    refine ⟨∫ z, b z ∂μ,fun P hP1 hP2 => ?_⟩
    have hmemΩ : P ∈ Ω (δ/2) (B+1) := ⟨by linarith,by linarith⟩
    rw [hR,(fiber _ _ (by positivity)).2 k P hmemΩ]
    calc ‖∫ z, iteratedFDeriv ℝ k (g z) P ∂μ‖ * (1+‖P.2.2‖)^M
        ≤ (∫ z, ‖iteratedFDeriv ℝ k (g z) P‖ ∂μ) * (1+‖P.2.2‖)^M :=
          mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm _) (by positivity)
      _ = ∫ z, ‖iteratedFDeriv ℝ k (g z) P‖ * (1+‖P.2.2‖)^M ∂μ := (integral_mul_const _ _).symm
      _ ≤ ∫ z, b z ∂μ := integral_mono_of_nonneg (.of_forall fun _ => by positivity) hb
          (.of_forall fun z => h z P hmemΩ)

end Core

/-- The linear map (U, V, W) ↦ (U, V, aW). -/
def thirdScale (a : L) : (L × L × L) →L[ℝ] (L × L × L) :=
  (ContinuousLinearMap.fst ℝ L (L × L)).prod ((ContinuousLinearMap.fst ℝ L L).comp
    (ContinuousLinearMap.snd ℝ L (L × L)) |>.prod
    ((ContinuousLinearMap.lsmul ℝ L a).comp ((ContinuousLinearMap.snd ℝ L L).comp
      (ContinuousLinearMap.snd ℝ L (L × L)))))

@[simp] theorem thirdScale_apply (a : L) (P : L × L × L) : thirdScale a P = (P.1, P.2.1, a * P.2.2) := by
  simp [thirdScale,smul_eq_mul]

theorem norm_thirdScale_le (a : L) : ‖thirdScale a‖ ≤ 1 + ‖a‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun P => ?_
  have h1 : ‖P.1‖ ≤ ‖P‖ := norm_fst_le P
  have h2 : ‖P.2.1‖ ≤ ‖P‖ := (norm_fst_le P.2).trans (norm_snd_le P)
  have h3 : ‖P.2.2‖ ≤ ‖P‖ := (norm_snd_le P.2).trans (norm_snd_le P)
  rw [thirdScale_apply,Prod.norm_def,Prod.norm_def,norm_mul]
  refine max_le (by nlinarith [norm_nonneg a,norm_nonneg P]) (max_le (by nlinarith [norm_nonneg a,norm_nonneg P]) ?_)
  nlinarith [norm_nonneg a,norm_nonneg P]

theorem continuous_thirdScale : Continuous (thirdScale (L := L)) := by
  refine (LipschitzWith.of_dist_le_mul fun a b => ?_).continuous (K := 1)
  rw [dist_eq_norm,dist_eq_norm,NNReal.coe_one,one_mul]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun P => ?_
  have h3 : ‖P.2.2‖ ≤ ‖P‖ := (norm_snd_le P.2).trans (norm_snd_le P)
  rw [sub_apply,thirdScale_apply,thirdScale_apply]
  simp only [Prod.mk_sub_mk,sub_self,Prod.norm_def,norm_zero,← sub_mul,norm_mul]
  refine max_le (by positivity) (max_le (by positivity) ?_)
  exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)

section Fourier
variable {K : Type} [NormedField K] [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

/-- Proposition 4.5 at a real or complex place, in linearized coordinates: if R is smooth for
U ≠ 0 and its derivatives decay in the last variable, then the Fourier integral
Q(U, V, W) = ∫ ψ(t) R(U, V, tⁿ W) dt is smooth where U W ≠ 0. -/
theorem lineFourier_smooth (μ : Measure K) (e : K ≃+* L) (he : Isometry e)
    (hint : Integrable (fun x : K => ((1+‖x‖)^3)⁻¹) μ) (n : ℕ) (hn : 0 < n)
    {ψ : K → ℂ} (hψ : Continuous ψ) (hψ1 : ∀ t, ‖ψ t‖ = 1)
    {R : L × L × L → ℂ} (hR : ContDiffOn ℝ ∞ R {P | P.1 ≠ 0})
    (hdec : ∀ k M : ℕ, ∀ δ B : ℝ, 0 < δ → ∃ C : ℝ, ∀ P : L × L × L, δ ≤ ‖P.1‖ → ‖P.2.1‖ ≤ B →
      ‖iteratedFDeriv ℝ k R P‖ * (1+‖P.2.2‖)^M ≤ C) :
    ContDiffOn ℝ ∞ (fun P : L × L × L => ∫ t, ψ t * R (P.1, P.2.1, e t ^ n * P.2.2) ∂μ)
      {P | P.1 ≠ 0 ∧ P.2.2 ≠ 0} := by
  let W : Set (L × L × L) := {P | P.1 ≠ 0}
  have hW : IsOpen W := isOpen_ne_fun continuous_fst continuous_const
  have norm_e := he.norm_map_of_map_zero e.map_zero
  let h (t : K) (P : L × L × L) : ℂ := ψ t * R (thirdScale (e t ^ n) P)
  have hh (t : K) : h t = (ψ t • (R ∘ thirdScale (e t ^ n)) : L × L × L → ℂ) := by
    funext P; simp [h,smul_eq_mul]
  have hmem (t : K) (P : L × L × L) (hP : P.1 ≠ 0) : thirdScale (e t ^ n) P ∈ W := by simpa [W] using hP
  have hRA (t : K) (P : L × L × L) (hP : P.1 ≠ 0) : ContDiffAt ℝ ∞ (R ∘ thirdScale (e t ^ n)) P :=
    (hR.contDiffAt (hW.mem_nhds (hmem t P hP))).comp P (thirdScale (e t ^ n)).contDiff.contDiffAt
  have deriv (t : K) (P : L × L × L) (hP : P.1 ≠ 0) (k : ℕ) :
      iteratedFDeriv ℝ k (h t) P = ψ t • (iteratedFDeriv ℝ k R (thirdScale (e t ^ n) P)).compContinuousLinearMap
        (fun _ => thirdScale (e t ^ n)) := by
    rw [hh,iteratedFDeriv_const_smul_apply ((hRA t P hP).of_le (by exact_mod_cast le_top)),
      iteratedFDeriv_comp_clm_of_isOpen hW hR _ (hmem t P hP)]
  let Ω (δ B : ℝ) : Set (L × L × L) := {P | δ < ‖P.1‖ ∧ ‖P.2.1‖ < B ∧ δ < ‖P.2.2‖}
  have hΩ (δ B : ℝ) : IsOpen (Ω δ B) :=
    (isOpen_lt continuous_const continuous_fst.norm).inter
      ((isOpen_lt (continuous_fst.comp continuous_snd).norm continuous_const).inter
        (isOpen_lt continuous_const (continuous_snd.comp continuous_snd).norm))
  have hΩne (δ B : ℝ) (hδ : 0 ≤ δ) (P) (hP : P ∈ Ω δ B) : P.1 ≠ 0 :=
    norm_pos_iff.mp (hδ.trans_lt hP.1)
  have hs (δ B : ℝ) (hδ : 0 ≤ δ) (t : K) : ContDiffOn ℝ ∞ (h t) (Ω δ B) := by
    intro P hP
    rw [hh]
    exact ((hRA t P (hΩne δ B hδ P hP)).const_smul (ψ t)).contDiffWithinAt
  have hm (δ B : ℝ) (hδ : 0 ≤ δ) (k : ℕ) (P) (hP : P ∈ Ω δ B) :
      AEStronglyMeasurable (fun t => iteratedFDeriv ℝ k (h t) P) μ := by
    have hP0 := hΩne δ B hδ P hP
    have hA : Continuous fun t : K => thirdScale (e t ^ n) :=
      continuous_thirdScale.comp (he.continuous.pow n)
    have hDk : ContinuousOn (iteratedFDeriv ℝ k R) W := by
      have h := hR.continuousOn_iteratedFDerivWithin (m := k) (by exact_mod_cast le_top) hW.uniqueDiffOn
      exact h.congr fun u hu => (iteratedFDerivWithin_of_isOpen k hW hu).symm
    have hφ : Continuous (fun t : K => iteratedFDeriv ℝ k R (thirdScale (e t ^ n) P)) :=
      hDk.comp_continuous (hA.clm_apply continuous_const) (fun t => hmem t P hP0)
    have hc := (hψ.continuousOn.smul (continuous_compContinuousLinearMap_const k hφ.continuousOn
      hA.continuousOn (S := univ))).congr (fun t _ => deriv t P hP0 k)
    exact (continuousOn_univ.mp hc).aestronglyMeasurable
  have bound (δ B : ℝ) (hδ : 0 < δ) (k : ℕ) : ∃ b : K → ℝ, Integrable b μ ∧
      ∀ t, ∀ P ∈ Ω δ B, ‖iteratedFDeriv ℝ k (h t) P‖ ≤ b t := by
    obtain ⟨C,hC⟩ := hdec k (k+3) δ B hδ
    let κ := 8 * (1 + 1/δ)^(k+3) * max C 0
    refine ⟨fun t => κ * ((1+‖t‖)^3)⁻¹,hint.const_mul κ,fun t P hP => ?_⟩
    have hP0 := hΩne δ B hδ.le P hP
    set σ := e t ^ n * P.2.2
    have hσ : δ * ‖t‖^n ≤ ‖σ‖ := by
      rw [norm_mul,norm_pow,norm_e,mul_comm]; exact mul_le_mul_of_nonneg_left hP.2.2.le (by positivity)
    have ht1 : 1 + ‖t‖ ≤ 2 * (1 + ‖t‖^n) := by
      rcases le_total ‖t‖ 1 with h1|h1
      · nlinarith [pow_nonneg (norm_nonneg t) n]
      · nlinarith [le_self_pow₀ h1 hn.ne']
    have ht2 : 1 + ‖t‖^n ≤ (1 + 1/δ) * (1 + ‖σ‖) := by
      have : ‖t‖^n ≤ ‖σ‖ / δ := by rw [le_div_iff₀ hδ]; linarith
      have h2 : ‖σ‖ / δ = 1/δ * ‖σ‖ := by ring
      nlinarith [norm_nonneg σ,one_div_nonneg.mpr hδ.le]
    have hder : ‖iteratedFDeriv ℝ k (h t) P‖ ≤ ‖iteratedFDeriv ℝ k R (thirdScale (e t ^ n) P)‖ * (1+‖t‖^n)^k := by
      rw [deriv t P hP0 k,norm_smul,hψ1,one_mul]
      have h := (iteratedFDeriv ℝ k R (thirdScale (e t ^ n) P)).norm_compContinuousLinearMap_le
        (fun _ : Fin k => thirdScale (e t ^ n))
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
      have hA : ‖thirdScale (e t ^ n)‖ ≤ 1 + ‖t‖^n := by
        have := norm_thirdScale_le (e t ^ n); rwa [norm_pow,norm_e] at this
      exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hA k) (norm_nonneg _))
    have hb := hC (thirdScale (e t ^ n) P) (by simpa using hP.1.le) (by simpa using hP.2.1.le)
    simp only [thirdScale_apply] at hb
    change _ ≤ κ * ((1 + ‖t‖)^3)⁻¹
    rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
    calc ‖iteratedFDeriv ℝ k (h t) P‖ * (1+‖t‖)^3
        ≤ ‖iteratedFDeriv ℝ k R (thirdScale (e t ^ n) P)‖ * (1+‖t‖^n)^k * (2 * (1 + ‖t‖^n))^3 := by
          gcongr
      _ = 8 * (‖iteratedFDeriv ℝ k R (thirdScale (e t ^ n) P)‖ * (1+‖t‖^n)^(k+3)) := by ring
      _ ≤ 8 * (‖iteratedFDeriv ℝ k R (thirdScale (e t ^ n) P)‖ * ((1 + 1/δ) * (1 + ‖σ‖))^(k+3)) := by
          gcongr
      _ = 8 * (1 + 1/δ)^(k+3) * (‖iteratedFDeriv ℝ k R (P.1, P.2.1, σ)‖ * (1 + ‖σ‖)^(k+3)) := by
          rw [mul_pow]; simp only [thirdScale_apply,σ]; ring
      _ ≤ κ := mul_le_mul_of_nonneg_left (hb.trans (le_max_left _ _)) (by positivity)
  intro P hP
  obtain ⟨hP1,hP2⟩ := hP
  let δ := min ‖P.1‖ ‖P.2.2‖ / 2
  have hδ : 0 < δ := by positivity
  have hmemΩ : P ∈ Ω δ (‖P.2.1‖+1) :=
    ⟨by have := min_le_left ‖P.1‖ ‖P.2.2‖; have := norm_pos_iff.mpr hP1; simp only [δ]; linarith,
     by linarith,
     by have := min_le_right ‖P.1‖ ‖P.2.2‖; have := norm_pos_iff.mpr hP2; simp only [δ]; linarith⟩
  have fib := smooth_fiber_integral_on (μ := μ) (hΩ δ (‖P.2.1‖+1)) (hs _ _ hδ.le) (hm _ _ hδ.le)
    (fun k => bound δ (‖P.2.1‖+1) hδ k)
  have : (fun P : L × L × L => ∫ t, ψ t * R (P.1, P.2.1, e t ^ n * P.2.2) ∂μ) = fun P => ∫ t, h t P ∂μ := by
    funext P; simp [h]
  rw [this]
  exact (fib.1.contDiffAt ((hΩ _ _).mem_nhds hmemΩ)).contDiffWithinAt

end Fourier

end MetaplecticPoisson
