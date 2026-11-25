import MetaplecticSummation.ArchimedeanSmoothness

/-! Proposition 8.1 at real and complex places: uniform bounds for the normalized rays.

For Ψ in the local Schwartz space, the normalized rays μ ↦ |μ|^{n-1} Ψ(μⁿ v) are smooth in v,
and every derivative in v decays rapidly in μ, uniformly for v in compact subsets of either
chart and μ ∈ F^×. For a test section this is the rapid decay of the chart at the origin
and at infinity. For a transformed test section the ray formula identifies the ray with the
Fourier transform of the Radon slice. Its derivatives in v are the Fourier transforms of the
v-derivatives of the slice, and these form a bounded Schwartz family by Lemma 4.2(iii). -/

noncomputable section
namespace MetaplecticPoisson
open NumberField MeasureTheory Set Filter
open scoped Topology ContDiff
open Classical

set_option backward.isDefEq.respectTransparency false in
theorem norm_iteratedFDeriv_iteratedFDeriv' {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : E → G) (x : E) (k : ℕ) :
    ∀ j, ‖iteratedFDeriv ℝ j (iteratedFDeriv ℝ k f) x‖ = ‖iteratedFDeriv ℝ (j + k) f x‖ := by
  induction k with
  | zero =>
    intro j
    rw [iteratedFDeriv_zero_eq_comp,LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,add_zero]
  | succ k ih =>
    intro j
    have h := LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := ℝ)
      (F := E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) G)
      (G := ContinuousMultilinearMap ℝ (fun _ : Fin (k+1) => E) G)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) G).symm
      (fderiv ℝ (iteratedFDeriv ℝ k f)) x j
    rw [iteratedFDeriv_succ_eq_comp_left,h,norm_iteratedFDeriv_fderiv,ih (j+1),add_assoc,add_comm 1 k]

section Slices
variable {L : Type} [NormedField L] [NormedAlgebra ℝ L]

/-- The inclusion (a, b) ↦ (a, b, 0). -/
def planeIncl : (L × L) →L[ℝ] (L × L × L) :=
  (ContinuousLinearMap.fst ℝ L L).prod ((ContinuousLinearMap.snd ℝ L L).prod 0)

@[simp] theorem planeIncl_apply (Q : L × L) : (planeIncl : (L × L) →L[ℝ] (L × L × L)) Q = (Q.1, Q.2, 0) := rfl

theorem norm_planeIncl_apply (Q : L × L) : ‖(planeIncl : (L × L) →L[ℝ] (L × L × L)) Q‖ ≤ ‖Q‖ := by
  rw [planeIncl_apply,Prod.norm_def,Prod.norm_def,norm_zero,Prod.norm_def]
  exact max_le (le_max_left _ _) (max_le (le_max_right _ _) (le_max_of_le_left (norm_nonneg _)))

/-- The inclusion y ↦ (0, 0, y). -/
def lineIncl : L →L[ℝ] (L × L × L) :=
  (0 : L →L[ℝ] L).prod ((0 : L →L[ℝ] L).prod (ContinuousLinearMap.id ℝ L))

theorem norm_lineIncl_le : ‖(lineIncl : L →L[ℝ] (L × L × L))‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  simp [lineIncl,Prod.norm_def]

/-- Iterated derivatives of a smooth function along the third coordinate, evaluated on fixed
directions in the first two, are bounded by the joint derivatives. -/
theorem slice_deriv_le {Rr : L × L × L → ℂ} {U' : Set (L × L × L)} (hU' : IsOpen U')
    (hR : ContDiffOn ℝ ∞ Rr U') (k : ℕ) (a b : L) (hmem : ∀ y : L, (a, b, y) ∈ U')
    (h : Fin k → L × L) (hh : ∀ i, ‖h i‖ ≤ 1) (j : ℕ) (y : L) :
    ContDiff ℝ ∞ (fun y : L => (iteratedFDeriv ℝ k Rr (a, b, y)) (fun i => planeIncl (h i))) ∧
    ‖iteratedFDeriv ℝ j (fun y : L => (iteratedFDeriv ℝ k Rr (a, b, y)) (fun i => planeIncl (h i))) y‖ ≤
      ‖iteratedFDeriv ℝ (j + k) Rr (a, b, y)‖ := by
  let c : L × L × L := (a, b, 0)
  have hc (y : L) : (a, b, y) = lineIncl y + c := by ext <;> simp [lineIncl,c]
  let D := iteratedFDeriv ℝ k Rr
  have hD : ∀ P ∈ U', ContDiffAt ℝ ∞ D P := fun P hP =>
    ((hR.contDiffAt (hU'.mem_nhds hP)).iteratedFDeriv_right (m := ∞) (i := k) (by simp))
  let Dc : L × L × L → ContinuousMultilinearMap ℝ (fun _ : Fin k => L × L × L) ℂ := fun P => D (P + c)
  let W : Set (L × L × L) := (fun P => P + c) ⁻¹' U'
  have hW : IsOpen W := hU'.preimage (continuous_id.add continuous_const)
  have hDc : ContDiffOn ℝ ∞ Dc W := fun P hP =>
    ((hD _ hP).comp P (contDiffAt_id.add contDiffAt_const)).contDiffWithinAt
  have hmemW (y : L) : lineIncl y ∈ W := by
    change lineIncl y + c ∈ U'; rw [← hc]; exact hmem y
  let Ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => L × L × L) ℂ (fun i => planeIncl (h i))
  have hEv : ‖Ev‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun φ => ?_
    refine (φ.le_opNorm _).trans ?_
    rw [one_mul]
    have hp (i : Fin k) : ‖(planeIncl : (L × L) →L[ℝ] (L × L × L)) (h i)‖ ≤ 1 :=
      (norm_planeIncl_apply (h i)).trans (hh i)
    exact mul_le_of_le_one_right (norm_nonneg _)
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hp i)
  have hfun : (fun y : L => (iteratedFDeriv ℝ k Rr (a, b, y)) (fun i => planeIncl (h i))) = Ev ∘ (Dc ∘ lineIncl) := by
    funext y; simp only [Function.comp_apply,Dc,D,Ev,ContinuousMultilinearMap.apply_apply,← hc]
  have hsm : ContDiff ℝ ∞ (Dc ∘ lineIncl) := contDiff_iff_contDiffAt.mpr fun y =>
    (hDc.contDiffAt (hW.mem_nhds (hmemW y))).comp y (lineIncl : L →L[ℝ] (L × L × L)).contDiff.contDiffAt
  refine ⟨hfun ▸ Ev.contDiff.comp hsm,?_⟩
  rw [hfun,Ev.iteratedFDeriv_comp_left (x := y) hsm.contDiffAt (by exact_mod_cast le_top),
    iteratedFDeriv_comp_clm_of_isOpen' hW hDc lineIncl (hmemW y) j]
  have hsh : iteratedFDeriv ℝ j Dc (lineIncl y) = iteratedFDeriv ℝ j D (a, b, y) := by
    rw [hc y]; exact iteratedFDeriv_comp_add_right j c (lineIncl y)
  calc _ ≤ ‖Ev‖ * ‖(iteratedFDeriv ℝ j Dc (lineIncl y)).compContinuousLinearMap fun _ => lineIncl‖ :=
        Ev.norm_compContinuousMultilinearMap_le _
    _ ≤ 1 * (‖iteratedFDeriv ℝ j Dc (lineIncl y)‖ * 1) := by
        refine mul_le_mul hEv ?_ (norm_nonneg _) zero_le_one
        refine ((iteratedFDeriv ℝ j Dc (lineIncl y)).norm_compContinuousLinearMap_le _).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => norm_lineIncl_le
    _ = ‖iteratedFDeriv ℝ (j + k) Rr (a, b, y)‖ := by
        rw [one_mul,mul_one,hsh]; exact norm_iteratedFDeriv_iteratedFDeriv' Rr _ k j

end Slices

namespace Datum
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (w : InfinitePlace F)
local notation "v" => (Sum.inl w : Place F)
local notation "K" => LocalField F v
local notation "dx" => selfDual F d.character v

omit [NeZero n] in
/-- Proposition 8.1 at a real or complex place, for the Fourier integral of a slice function:
if R is smooth with all derivatives rapidly decreasing in the last variable, then the
derivatives in the first two variables of ∫ R(a, b, t) ψ(ut) dt are bounded and decay rapidly
in u, uniformly for (a, b) in a compact set and u ∈ F. -/
theorem slice_fourier_bounds {L : Type} [NormedField L] [NormedAlgebra ℝ L] [ProperSpace L]
    (e : K ≃+* L) (he : Isometry e)
    {Rr : L × L × L → ℂ} {Ω : Set (L × L)} (hΩ : IsOpen Ω) (hR : ContDiffOn ℝ ∞ Rr {P | (P.1, P.2.1) ∈ Ω})
    {T O : Set (L × L)} (hTc : IsCompact T) (hTO : T ⊆ O) (hO : IsOpen O) (hOΩ : O ⊆ Ω)
    (hdec : ∀ k N : ℕ, ∃ C : ℝ, ∀ P : L × L × L, (P.1, P.2.1) ∈ O →
      ‖iteratedFDeriv ℝ k Rr P‖ * (1+‖P.2.2‖)^N ≤ C) (k N : ℕ) :
    let G := fun (u : K) (Q : L × L) => ∫ t, Rr (Q.1, Q.2, e t) * d.character.localValue F v (u * t) ∂dx
    (∀ u, ContDiffOn ℝ ∞ (G u) O) ∧
    ∃ C : ℝ, ∀ u : K, ∀ Q ∈ T, ∀ h : Fin k → L × L, (∀ i, ‖h i‖ ≤ 1) →
      ‖(iteratedFDeriv ℝ k (G u) Q) h‖ * (1+‖u‖)^N ≤ C := by
  intro G
  let : SecondCountableTopology K :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  have norm_e := he.norm_map_of_map_zero e.map_zero
  let ψ := d.character.localValue F v
  have hψ : Continuous ψ := d.character.continuous_localValue v
  have hψ1 (t : K) : ‖ψ t‖ = 1 := d.character.norm_localValue v t
  have hint := d.arch_integrable_inv_cube w
  let U' : Set (L × L × L) := {P | (P.1, P.2.1) ∈ Ω}
  have hU' : IsOpen U' := hΩ.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  let J : (L × L) →L[ℝ] (L × L × L) := planeIncl
  let c (t : K) : L × L × L := (0, 0, e t)
  have hJc (Q : L × L) (t : K) : (Q.1, Q.2, e t) = J Q + c t := by ext <;> simp [J,c]
  -- the shifted functions
  let f (t : K) : L × L × L → ℂ := fun P => Rr (P + c t)
  have hf (t : K) : ContDiffOn ℝ ∞ (f t) U' := fun P hP =>
    ((hR.contDiffAt (hU'.mem_nhds (show P + c t ∈ U' by simpa [U',c] using hP))).comp P
      (contDiffAt_id.add contDiffAt_const)).contDiffWithinAt
  have hJmem (Q : L × L) (hQ : Q ∈ Ω) : J Q ∈ U' := by simpa [U',J] using hQ
  let g (u t : K) : L × L → ℂ := fun Q => ψ (u * t) • (f t ∘ J) Q
  have hg (u : K) (t : K) : (fun Q => Rr (Q.1, Q.2, e t) * ψ (u * t)) = g u t := by
    funext Q; simp only [g,f,Function.comp_apply,← hJc,smul_eq_mul]; ring
  have hG (u : K) : G u = fun Q => ∫ t, g u t Q ∂dx := by
    funext Q; simp only [G]; congr 1; funext t; exact congrFun (hg u t) Q
  have hfJ (t : K) (Q : L × L) (hQ : Q ∈ Ω) : ContDiffAt ℝ ∞ (f t ∘ J) Q :=
    ((hf t).contDiffAt (hU'.mem_nhds (hJmem Q hQ))).comp Q J.contDiff.contDiffAt
  have deriv (u t : K) (Q : L × L) (hQ : Q ∈ Ω) (i : ℕ) :
      iteratedFDeriv ℝ i (g u t) Q = ψ (u * t) •
        (iteratedFDeriv ℝ i Rr (Q.1, Q.2, e t)).compContinuousLinearMap (fun _ => J) := by
    have h1 : g u t = ψ (u * t) • (f t ∘ J) := rfl
    rw [h1,iteratedFDeriv_const_smul_apply ((hfJ t Q hQ).of_le (by exact_mod_cast le_top)),
      iteratedFDeriv_comp_clm_of_isOpen' hU' (hf t) J (hJmem Q hQ) i]
    congr 2
    rw [hJc Q t]
    exact iteratedFDeriv_comp_add_right i (c t) (J Q)
  have hJn : ‖J‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun Q => ?_
    rw [one_mul]; exact norm_planeIncl_apply Q
  have hDcont (i : ℕ) : ContinuousOn (iteratedFDeriv ℝ i Rr) U' := by
    have h := hR.continuousOn_iteratedFDerivWithin (m := i) (by exact_mod_cast le_top) hU'.uniqueDiffOn
    exact h.congr fun P hP => (iteratedFDerivWithin_of_isOpen i hU' hP).symm
  -- majorants and smoothness
  have bound (i : ℕ) : ∃ b : K → ℝ, Integrable b dx ∧ ∀ u t, ∀ Q ∈ O,
      ‖iteratedFDeriv ℝ i (g u t) Q‖ ≤ b t := by
    obtain ⟨C,hC⟩ := hdec i 3
    refine ⟨fun t => max C 0 * ((1+‖t‖)^3)⁻¹,hint.const_mul _,fun u t Q hQ => ?_⟩
    rw [deriv u t Q (hOΩ hQ) i,norm_smul,hψ1,one_mul]
    have h1 := (iteratedFDeriv ℝ i Rr (Q.1, Q.2, e t)).norm_compContinuousLinearMap_le (fun _ : Fin i => J)
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h1
    have h2 := hC (Q.1, Q.2, e t) hQ
    simp only [norm_e] at h2
    refine h1.trans ?_
    show _ ≤ max C 0 * ((1+‖t‖)^3)⁻¹
    rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
    calc ‖iteratedFDeriv ℝ i Rr (Q.1, Q.2, e t)‖ * ‖J‖ ^ i * (1 + ‖t‖) ^ 3
        ≤ ‖iteratedFDeriv ℝ i Rr (Q.1, Q.2, e t)‖ * 1 * (1 + ‖t‖) ^ 3 := by
          gcongr; exact pow_le_one₀ (norm_nonneg _) hJn
      _ ≤ max C 0 := by rw [mul_one]; exact h2.trans (le_max_left _ _)
  have hm (u : K) (i : ℕ) (Q : L × L) (hQ : Q ∈ O) :
      AEStronglyMeasurable (fun t => iteratedFDeriv ℝ i (g u t) Q) dx := by
    have hc : Continuous fun t : K => iteratedFDeriv ℝ i Rr (Q.1, Q.2, e t) :=
      (hDcont i).comp_continuous (continuous_const.prodMk (continuous_const.prodMk he.continuous))
        (fun t => show (Q.1, Q.2) ∈ Ω from hOΩ hQ)
    have hcc := continuous_compContinuousLinearMap_const i hc.continuousOn
      (continuous_const (y := J)).continuousOn (S := univ)
    have := ((hψ.comp (continuous_const.mul continuous_id)).continuousOn.smul hcc).congr
      (fun t _ => deriv u t Q (hOΩ hQ) i)
    exact (continuousOn_univ.mp this).aestronglyMeasurable
  have hs (u t : K) : ContDiffOn ℝ ∞ (g u t) O := fun Q hQ =>
    ((hfJ t Q (hOΩ hQ)).const_smul (ψ (u * t))).contDiffWithinAt
  have fiber (u : K) := smooth_fiber_integral_on (μ := dx) hO (hs u) (hm u) (fun i => by
    obtain ⟨b,hb,h⟩ := bound i
    exact ⟨b,hb,fun t Q hQ => h u t Q hQ⟩)
  refine ⟨fun u => (hG u) ▸ (fiber u).1,?_⟩
  -- the family of directional slices
  let A : Set ((L × L) × (Fin k → L × L)) := T ×ˢ Set.univ.pi (fun _ => Metric.closedBall (0 : L × L) 1)
  have hA : IsCompact A := hTc.prod (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hAmem (q : A) : q.1.1 ∈ Ω ∧ ∀ i, ‖q.1.2 i‖ ≤ 1 :=
    ⟨hOΩ (hTO q.2.1),fun i => by simpa using q.2.2 i (Set.mem_univ i)⟩
  have hAO (q : A) : q.1.1 ∈ O := hTO q.2.1
  let S : A → K → ℂ := fun q t => (iteratedFDeriv ℝ k Rr (q.1.1.1, q.1.1.2, e t)) (fun i => J (q.1.2 i))
  have hline (q : A) (y : L) : (q.1.1.1, q.1.1.2, y) ∈ U' := (hAmem q).1
  have slice (q : A) := slice_deriv_le hU' hR k q.1.1.1 q.1.1.2 (hline q) q.1.2 (hAmem q).2
  have sbound (j N' : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ q : A, ∀ y : L,
      ‖iteratedFDeriv ℝ j (fun y : L => (iteratedFDeriv ℝ k Rr (q.1.1.1, q.1.1.2, y))
        (fun i => planeIncl (q.1.2 i))) y‖ * (1+‖y‖)^N' ≤ C := by
    obtain ⟨C,hC⟩ := hdec (j+k) N'
    refine ⟨max C 0,le_max_right _ _,fun q y => ?_⟩
    have h1 := (slice q j y).2
    have h2 := hC (q.1.1.1, q.1.1.2, y) (hAO q)
    exact (mul_le_mul_of_nonneg_right h1 (by positivity)).trans (h2.trans (le_max_left _ _))
  let G' (q : A) : SchwartzMap L ℂ :=
    { toFun := fun y => (iteratedFDeriv ℝ k Rr (q.1.1.1, q.1.1.2, y)) (fun i => planeIncl (q.1.2 i))
      smooth' := (slice q 0 0).1
      decay' := fun a' b' => by
        obtain ⟨C,_,hC⟩ := sbound b' a'
        refine ⟨C,fun y => (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)).trans ((mul_comm _ _).trans_le (hC q y))⟩
        exact pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_nonneg y]) _ }
  have hSS : SchwartzSliceFamily e S := ⟨G',fun q t => rfl,fun T' _ j N' => by
    obtain ⟨C,hC0,hC⟩ := sbound j N'
    exact ⟨C,hC0,fun q _ y => hC q y⟩⟩
  have hSb (q : A) (t : K) : ‖S q t‖ ≤ (sbound 0 3).choose * ((1+‖t‖)^3)⁻¹ := by
    have h := (sbound 0 3).choose_spec.2 q (e t)
    rw [norm_iteratedFDeriv_zero,norm_e] at h
    rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
    exact h
  have hSc (q : A) : Continuous (S q) := (G' q).continuous.comp he.continuous
  have hSi (q : A) : Integrable (S q) dx :=
    (hint.const_mul _).mono' (hSc q).aestronglyMeasurable (.of_forall (hSb q))
  obtain ⟨C1,hC1,H1⟩ := d.hat_decay_of_schwartz_slices w e he hSS hSi univ isCompact_univ N
  let V := ∫ t : K, ((1+‖t‖)^3)⁻¹ ∂dx
  let C0 := (sbound 0 3).choose
  refine ⟨max C1 (C0 * V * 2^N),fun u Q hQ h hh => ?_⟩
  let q : A := ⟨(Q,h),hQ,fun i _ => by simpa using hh i⟩
  have hform : (iteratedFDeriv ℝ k (G u) Q) h = d.hat v (S q) u := by
    rw [hG u,(fiber u).2 k Q (hTO hQ)]
    have hint' : Integrable (fun t => iteratedFDeriv ℝ k (g u t) Q) dx := by
      obtain ⟨b,hb,hbb⟩ := bound k
      exact hb.mono' (hm u k Q (hTO hQ)) (.of_forall fun t => hbb u t Q (hTO hQ))
    rw [ContinuousMultilinearMap.integral_apply hint']
    unfold hat
    congr 1; funext t
    rw [deriv u t Q (hOΩ (hTO hQ)) k,smul_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,smul_eq_mul,mul_comm]
  rw [hform]
  rcases le_total 1 ‖u‖ with hu|hu
  · exact (H1 q (mem_univ _) u hu).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    have hn : ‖d.hat v (S q) u‖ ≤ C0 * V := by
      unfold hat
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg (.of_forall fun _ => norm_nonneg _) (hint.const_mul _) (.of_forall fun t => ?_)
      show ‖S q t * ψ (u * t)‖ ≤ C0 * ((1+‖t‖)^3)⁻¹
      rw [norm_mul,hψ1,mul_one]; exact hSb q t
    have h2 : (1+‖u‖)^N ≤ 2^N := pow_le_pow_left₀ (by positivity) (by linarith) N
    have hC0V : 0 ≤ C0 * V := (norm_nonneg _).trans hn
    calc ‖d.hat v (S q) u‖ * (1 + ‖u‖)^N ≤ C0 * V * 2^N := mul_le_mul hn h2 (by positivity) hC0V

/-- The normalized ray μ ↦ |μ|^{n-1} Ψ_X(μⁿ v) of §8 in real coordinates. -/
def rayX {L : Type} [NormedField L] (e : K ≃+* L) (g : Charts K) (u : Kˣ) (Q : L × L) : ℂ :=
  (modulus F v u.val : ℂ)^(n-1) * xChart g (e.symm (e u ^ n * Q.1), e.symm (e u ^ n * Q.2))

/-- The normalized ray in the Y-chart. -/
def rayY {L : Type} [NormedField L] (e : K ≃+* L) (g : Charts K) (u : Kˣ) (Q : L × L) : ℂ :=
  (modulus F v u.val : ℂ)^(n-1) * yChart g (e.symm (e u ^ n * Q.1), e.symm (e u ^ n * Q.2))

/-- The open neighbourhood of the X-region used for differentiation. -/
def regionOX {L : Type} [NormedField L] (δ B : ℝ) : Set (L × L) :=
  {Q | δ/2 < ‖Q.1‖ ∧ ‖Q.1‖ < B+1 ∧ ‖Q.2‖ < B+1}

def regionOY {L : Type} [NormedField L] (δ B : ℝ) : Set (L × L) :=
  {Q | δ/2 < ‖Q.2‖ ∧ ‖Q.2‖ < B+1 ∧ ‖Q.1‖ < B+1}

theorem isOpen_regionOX {L : Type} [NormedField L] (δ B : ℝ) : IsOpen (regionOX (L := L) δ B) :=
  (isOpen_lt continuous_const continuous_fst.norm).inter ((isOpen_lt continuous_fst.norm continuous_const).inter
    (isOpen_lt continuous_snd.norm continuous_const))

theorem isOpen_regionOY {L : Type} [NormedField L] (δ B : ℝ) : IsOpen (regionOY (L := L) δ B) :=
  (isOpen_lt continuous_const continuous_snd.norm).inter ((isOpen_lt continuous_snd.norm continuous_const).inter
    (isOpen_lt continuous_fst.norm continuous_const))

/-- Proposition 8.1 at a real or complex place, in the X-chart, as uniform bounds: the normalized rays
are smooth on a neighbourhood of each region, and their derivatives of every order, evaluated on
unit directions, decay rapidly in μ uniformly for v in the region δ ≤ |x| ≤ B, |y| ≤ B. -/
def RayBoundX {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) (g : Charts K) : Prop :=
  ∀ δ B : ℝ, 0 < δ → (∀ u, ContDiffOn ℝ ∞ (rayX (n := n) w e g u) (regionOX δ B)) ∧
    ∀ k N : ℕ, ∃ C : ℝ, ∀ u : Kˣ, ∀ Q : L × L, δ ≤ ‖Q.1‖ → ‖Q.1‖ ≤ B → ‖Q.2‖ ≤ B →
      ∀ h : Fin k → L × L, (∀ i, ‖h i‖ ≤ 1) →
        ‖(iteratedFDeriv ℝ k (rayX (n := n) w e g u) Q) h‖ * (1+‖u.val‖)^N ≤ C

def RayBoundY {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) (g : Charts K) : Prop :=
  ∀ δ B : ℝ, 0 < δ → (∀ u, ContDiffOn ℝ ∞ (rayY (n := n) w e g u) (regionOY δ B)) ∧
    ∀ k N : ℕ, ∃ C : ℝ, ∀ u : Kˣ, ∀ Q : L × L, δ ≤ ‖Q.2‖ → ‖Q.2‖ ≤ B → ‖Q.1‖ ≤ B →
      ∀ h : Fin k → L × L, (∀ i, ‖h i‖ ≤ 1) →
        ‖(iteratedFDeriv ℝ k (rayY (n := n) w e g u) Q) h‖ * (1+‖u.val‖)^N ≤ C

theorem isCompact_regionX {L : Type} [NormedField L] [ProperSpace L] (δ B : ℝ) :
    IsCompact {Q : L × L | δ ≤ ‖Q.1‖ ∧ ‖Q.1‖ ≤ B ∧ ‖Q.2‖ ≤ B} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_fst.norm).inter ((isClosed_le continuous_fst.norm
      continuous_const).inter (isClosed_le continuous_snd.norm continuous_const))
  · refine (Metric.isBounded_closedBall (x := (0 : L × L)) (r := B)).subset fun Q hQ => ?_
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def]; exact max_le hQ.2.1 hQ.2.2

theorem isCompact_regionY {L : Type} [NormedField L] [ProperSpace L] (δ B : ℝ) :
    IsCompact {Q : L × L | δ ≤ ‖Q.2‖ ∧ ‖Q.2‖ ≤ B ∧ ‖Q.1‖ ≤ B} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_snd.norm).inter ((isClosed_le continuous_snd.norm
      continuous_const).inter (isClosed_le continuous_fst.norm continuous_const))
  · refine (Metric.isBounded_closedBall (x := (0 : L × L)) (r := B)).subset fun Q hQ => ?_
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def]; exact max_le hQ.2.2 hQ.2.1

set_option backward.isDefEq.respectTransparency false in
/-- The normalized rays of a transformed test section satisfy the bounds of Proposition 8.1. -/
theorem rayBoundX_transform {L : Type} [NormedField L] [NormedAlgebra ℝ L] [ProperSpace L]
    (e : K ≃+* L) (he : Isometry e) {f : Charts K} (htest : archTest e f) :
    RayBoundX (n := n) w e (d.integralTransform v f) := by
  intro δ B hδ
  let R := radon n (d.symbol v) (modulus F v) dx f
  let RX := fun P : L × L × L => (R (e.symm P.2.2)).1 (unitOf (e.symm P.1)) (e.symm P.2.1)
  have hsm : ContDiffOn ℝ ∞ RX {P | (P.1, P.2.1) ∈ {Q : L × L | Q.1 ≠ 0}} :=
    (d.arch_radon_smooth w e he htest).1
  have hdec0 := (d.arch_radon_deriv_decay w e he htest).1
  let T := {Q : L × L | δ ≤ ‖Q.1‖ ∧ ‖Q.1‖ ≤ B ∧ ‖Q.2‖ ≤ B}
  have hTO : T ⊆ regionOX δ B := fun Q hQ => ⟨by linarith [hQ.1],by linarith [hQ.2.1],by linarith [hQ.2.2]⟩
  have hOΩ : regionOX δ B ⊆ {Q : L × L | Q.1 ≠ 0} := fun Q hQ => norm_pos_iff.mp (by linarith [hQ.1])
  have hdec : ∀ k N : ℕ, ∃ C : ℝ, ∀ P : L × L × L, (P.1, P.2.1) ∈ regionOX δ B →
      ‖iteratedFDeriv ℝ k RX P‖ * (1+‖P.2.2‖)^N ≤ C := fun k N => by
    obtain ⟨C,hC⟩ := hdec0 k N (δ/2) (B+1) (by positivity)
    exact ⟨C,fun P hP => hC P hP.1.le hP.2.1.le hP.2.2.le⟩
  let c₀ : ℂ := (Real.sqrt (modulus F v (n : K)))⁻¹
  let G := fun (u : K) (Q : L × L) => ∫ t, RX (Q.1, Q.2, e t) * d.character.localValue F v (u * t) ∂dx
  have key (u : Kˣ) (Q : L × L) (hQ : Q.1 ≠ 0) : rayX (n := n) w e (d.integralTransform v f) u Q = c₀ * G u Q := by
    have hQ' : e.symm Q.1 ≠ 0 := (map_ne_zero e.symm).mpr hQ
    let a : Kˣ := unitOf (e.symm Q.1)
    have ha : a.val = e.symm Q.1 := unitOf_val hQ'
    have h1 : e.symm (e u ^ n * Q.1) = (u : K)^n * e.symm Q.1 := by rw [map_mul,map_pow,e.symm_apply_apply]
    have h2 : e.symm (e u ^ n * Q.2) = (u : K)^n * e.symm Q.2 := by rw [map_mul,map_pow,e.symm_apply_apply]
    have hne : (u : K)^n * e.symm Q.1 ≠ 0 := mul_ne_zero (pow_ne_zero _ u.ne_zero) hQ'
    have hray := (d.transform_pow_ray v f u).1 a (e.symm Q.2)
    simp only [rayX,h1,h2,xChart,ne_eq,hne,not_false_eq_true,dite_true]
    have hu : Units.mk0 ((u : K)^n * e.symm Q.1) hne = u^n * a := Units.ext (by simp [ha])
    rw [hu]
    refine hray.trans ?_
    simp only [G,RX,e.symm_apply_apply]
    rfl
  have SF (k N : ℕ) := d.slice_fourier_bounds w e he (isOpen_ne_fun continuous_fst continuous_const) hsm
    (isCompact_regionX δ B) hTO (isOpen_regionOX δ B) hOΩ hdec k N
  have hev (u : Kˣ) (Q : L × L) (hQ : Q.1 ≠ 0) :
      rayX (n := n) w e (d.integralTransform v f) u =ᶠ[𝓝 Q] (c₀ • G u : L × L → ℂ) := by
    filter_upwards [(isOpen_ne_fun continuous_fst continuous_const).mem_nhds hQ] with Q' hQ'
    exact key u Q' hQ'
  refine ⟨fun u => (contDiffOn_const.mul ((SF 0 0).1 u)).congr fun Q hQ => key u Q (hOΩ hQ),fun k N => ?_⟩
  obtain ⟨C,hC⟩ := (SF k N).2
  refine ⟨‖c₀‖ * C,fun u Q h1 h2 h3 h hh => ?_⟩
  have hQT : Q ∈ T := ⟨h1,h2,h3⟩
  have hQ0 : Q.1 ≠ 0 := hOΩ (hTO hQT)
  rw [((hev u Q hQ0).iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds,
    iteratedFDeriv_const_smul_apply ((((SF 0 0).1 u).contDiffAt ((isOpen_regionOX δ B).mem_nhds (hTO hQT))).of_le
      (by exact_mod_cast le_top)),smul_apply,norm_smul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC u Q hQT h hh) (norm_nonneg _)

set_option backward.isDefEq.respectTransparency false in
/-- The Y-chart rays of a transformed test section satisfy the bounds of Proposition 8.1. -/
theorem rayBoundY_transform {L : Type} [NormedField L] [NormedAlgebra ℝ L] [ProperSpace L]
    (e : K ≃+* L) (he : Isometry e) {f : Charts K} (htest : archTest e f) :
    RayBoundY (n := n) w e (d.integralTransform v f) := by
  intro δ B hδ
  let R := radon n (d.symbol v) (modulus F v) dx f
  let RX := fun P : L × L × L => (R (e.symm P.2.2)).2 (e.symm P.1) (unitOf (e.symm P.2.1))
  have hsm : ContDiffOn ℝ ∞ RX {P | (P.1, P.2.1) ∈ {Q : L × L | Q.2 ≠ 0}} :=
    (d.arch_radon_smooth w e he htest).2
  have hdec0 := (d.arch_radon_deriv_decay w e he htest).2
  let T := {Q : L × L | δ ≤ ‖Q.2‖ ∧ ‖Q.2‖ ≤ B ∧ ‖Q.1‖ ≤ B}
  have hTO : T ⊆ regionOY δ B := fun Q hQ => ⟨by linarith [hQ.1],by linarith [hQ.2.1],by linarith [hQ.2.2]⟩
  have hOΩ : regionOY δ B ⊆ {Q : L × L | Q.2 ≠ 0} := fun Q hQ => norm_pos_iff.mp (by linarith [hQ.1])
  have hdec : ∀ k N : ℕ, ∃ C : ℝ, ∀ P : L × L × L, (P.1, P.2.1) ∈ regionOY δ B →
      ‖iteratedFDeriv ℝ k RX P‖ * (1+‖P.2.2‖)^N ≤ C := fun k N => by
    obtain ⟨C,hC⟩ := hdec0 k N (δ/2) (B+1) (by positivity)
    exact ⟨C,fun P hP => hC P hP.1.le hP.2.1.le hP.2.2.le⟩
  let c₀ : ℂ := (Real.sqrt (modulus F v (n : K)))⁻¹
  let G := fun (u : K) (Q : L × L) => ∫ t, RX (Q.1, Q.2, e t) * d.character.localValue F v (u * t) ∂dx
  have key (u : Kˣ) (Q : L × L) (hQ : Q.2 ≠ 0) : rayY (n := n) w e (d.integralTransform v f) u Q = c₀ * G u Q := by
    have hQ' : e.symm Q.2 ≠ 0 := (map_ne_zero e.symm).mpr hQ
    let a : Kˣ := unitOf (e.symm Q.2)
    have ha : a.val = e.symm Q.2 := unitOf_val hQ'
    have h1 : e.symm (e u ^ n * Q.1) = (u : K)^n * e.symm Q.1 := by rw [map_mul,map_pow,e.symm_apply_apply]
    have h2 : e.symm (e u ^ n * Q.2) = (u : K)^n * e.symm Q.2 := by rw [map_mul,map_pow,e.symm_apply_apply]
    have hne : (u : K)^n * e.symm Q.2 ≠ 0 := mul_ne_zero (pow_ne_zero _ u.ne_zero) hQ'
    have hray := (d.transform_pow_ray v f u).2 (e.symm Q.1) a
    simp only [rayY,h1,h2,yChart,ne_eq,hne,not_false_eq_true,dite_true]
    have hu : Units.mk0 ((u : K)^n * e.symm Q.2) hne = u^n * a := Units.ext (by simp [ha])
    rw [hu]
    refine hray.trans ?_
    simp only [G,RX,e.symm_apply_apply]
    rfl
  have SF (k N : ℕ) := d.slice_fourier_bounds w e he (isOpen_ne_fun continuous_snd continuous_const) hsm
    (isCompact_regionY δ B) hTO (isOpen_regionOY δ B) hOΩ hdec k N
  have hev (u : Kˣ) (Q : L × L) (hQ : Q.2 ≠ 0) :
      rayY (n := n) w e (d.integralTransform v f) u =ᶠ[𝓝 Q] (c₀ • G u : L × L → ℂ) := by
    filter_upwards [(isOpen_ne_fun continuous_snd continuous_const).mem_nhds hQ] with Q' hQ'
    exact key u Q' hQ'
  refine ⟨fun u => (contDiffOn_const.mul ((SF 0 0).1 u)).congr fun Q hQ => key u Q (hOΩ hQ),fun k N => ?_⟩
  obtain ⟨C,hC⟩ := (SF k N).2
  refine ⟨‖c₀‖ * C,fun u Q h1 h2 h3 h hh => ?_⟩
  have hQT : Q ∈ T := ⟨h1,h2,h3⟩
  have hQ0 : Q.2 ≠ 0 := hOΩ (hTO hQT)
  rw [((hev u Q hQ0).iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds,
    iteratedFDeriv_const_smul_apply ((((SF 0 0).1 u).contDiffAt ((isOpen_regionOY δ B).mem_nhds (hTO hQT))).of_le
      (by exact_mod_cast le_top)),smul_apply,norm_smul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC u Q hQT h hh) (norm_nonneg _)

/-- Ray bounds for a rapid chart: r^a ‖D^k X(x)‖ decays rapidly in r, uniformly for points x
with ‖x‖ ≥ rⁿ δ. -/
theorem rapid_ray_bound {L : Type} [NormedField L] [NormedAlgebra ℝ L] {X : L × L → ℂ} {S : Set (L × L)}
    (hX : rapidChart S X) (k a N : ℕ) (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → ∀ x ∈ S, r^n * δ ≤ ‖x‖ →
      r^a * ‖iteratedFDeriv ℝ k X x‖ * (1+r)^N ≤ C := by
  obtain ⟨C0,hC0⟩ := hX.2 k 0
  obtain ⟨C1,hC1⟩ := hX.2 k (a+N)
  refine ⟨max (max C0 0 * 2^N) (max C1 0 * (δ^(a+N))⁻¹ * 2^N),fun r hr x hx hxr => ?_⟩
  rcases le_total r 1 with h1|h1
  · refine le_trans ?_ (le_max_left _ _)
    have hb : ‖iteratedFDeriv ℝ k X x‖ ≤ max C0 0 := by
      have := hC0 x hx; simp only [pow_zero,inv_one,min_self,mul_one] at this; exact this.trans (le_max_left _ _)
    have hra : r^a ≤ 1 := pow_le_one₀ hr h1
    have h2 : (1+r)^N ≤ 2^N := pow_le_pow_left₀ (by positivity) (by linarith) N
    calc r^a * ‖iteratedFDeriv ℝ k X x‖ * (1+r)^N ≤ 1 * max C0 0 * 2^N := by gcongr
      _ = _ := by ring
  · refine le_trans ?_ (le_max_right _ _)
    have hxpos : 0 < ‖x‖ := (mul_pos (pow_pos (by linarith) n) hδ).trans_le hxr
    have hrx : r * δ ≤ ‖x‖ := (mul_le_mul_of_nonneg_right (le_self_pow₀ h1 hn.ne') hδ.le).trans hxr
    have hb : ‖iteratedFDeriv ℝ k X x‖ ≤ max C1 0 * ((‖x‖^(a+N))⁻¹) := by
      have hm0 : 0 ≤ min (‖x‖^(a+N)) ((‖x‖^(a+N))⁻¹) := le_min (by positivity) (by positivity)
      exact (hC1 x hx).trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) hm0).trans
        (mul_le_mul_of_nonneg_left (min_le_right _ _) (le_max_right _ _)))
    have hrδ : 0 < r * δ := mul_pos (by linarith) hδ
    have hinv : (‖x‖^(a+N))⁻¹ ≤ ((r*δ)^(a+N))⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hrδ.le hrx _)
    have h2 : (1+r)^N ≤ (2*r)^N := pow_le_pow_left₀ (by positivity) (by linarith) N
    have hr0 : 0 < r := by linarith
    calc r^a * ‖iteratedFDeriv ℝ k X x‖ * (1+r)^N
        ≤ r^a * (max C1 0 * ((r*δ)^(a+N))⁻¹) * (2*r)^N := by
          gcongr; exact hb.trans (mul_le_mul_of_nonneg_left hinv (le_max_right _ _))
      _ = max C1 0 * (δ^(a+N))⁻¹ * 2^N := by
          rw [mul_pow,mul_pow,pow_add]; field_simp

/-- Scalar multiplication on the plane as a real-linear map. -/
def planeScale {L : Type} [NormedField L] [NormedAlgebra ℝ L] (c : L) : (L × L) →L[ℝ] (L × L) :=
  (ContinuousLinearMap.lsmul ℝ L c).prodMap (ContinuousLinearMap.lsmul ℝ L c)

@[simp] theorem planeScale_apply {L : Type} [NormedField L] [NormedAlgebra ℝ L] (c : L) (Q : L × L) :
    planeScale c Q = (c * Q.1, c * Q.2) := by simp [planeScale,Prod.map,smul_eq_mul]

theorem norm_planeScale_le {L : Type} [NormedField L] [NormedAlgebra ℝ L] (c : L) : ‖planeScale c‖ ≤ ‖c‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun Q => ?_
  rw [planeScale_apply,Prod.norm_def,Prod.norm_def,norm_mul,norm_mul,mul_max_of_nonneg _ _ (norm_nonneg _)]

/-- The normalized rays of a test section satisfy the bounds of Proposition 8.1, in both charts. -/
theorem rayBound_test {L : Type} [NormedField L] [NormedAlgebra ℝ L]
    (e : K ≃+* L) (he : Isometry e) {f : Charts K} (htest : archTest e f) :
    RayBoundX (n := n) w e f ∧ RayBoundY (n := n) w e f := by
  have norm_e := he.norm_map_of_map_zero e.map_zero
  have hm (u : Kˣ) : ‖((modulus F v u.val : ℝ) : ℂ)^(n-1)‖ = ‖u.val‖^(w.mult*(n-1)) := by
    rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg (by simp only [modulus]; positivity),pow_mul]; rfl
  have go (X : L × L → ℂ) (S : Set (L × L)) (hS : IsOpen S) (hX : rapidChart S X)
      (ray : Kˣ → L × L → ℂ) (hray : ∀ u, ray u = fun Q => ((modulus F v u.val : ℝ) : ℂ)^(n-1) * X (planeScale (e u ^ n) Q))
      (Ω : ℝ → ℝ → Set (L × L)) (hΩS : ∀ δ B (u : Kˣ), 0 < δ → ∀ Q ∈ Ω δ B, planeScale (e u ^ n) Q ∈ S)
      (T : ℝ → ℝ → Set (L × L)) (hTΩ : ∀ δ B, 0 < δ → T δ B ⊆ Ω δ B) (hΩo : ∀ δ B, IsOpen (Ω δ B))
      (hTn : ∀ δ B (u : Kˣ), ∀ Q ∈ T δ B, ‖u.val‖^n * δ ≤ ‖planeScale (e u ^ n) Q‖) :
      ∀ δ B : ℝ, 0 < δ → (∀ u, ContDiffOn ℝ ∞ (ray u) (Ω δ B)) ∧
        ∀ k N : ℕ, ∃ C : ℝ, ∀ u : Kˣ, ∀ Q ∈ T δ B, ∀ h : Fin k → L × L, (∀ i, ‖h i‖ ≤ 1) →
          ‖(iteratedFDeriv ℝ k (ray u) Q) h‖ * (1+‖u.val‖)^N ≤ C := by
    intro δ B hδ
    have hsm (u : Kˣ) (Q : L × L) (hQ : Q ∈ Ω δ B) : ContDiffAt ℝ ∞ (X ∘ planeScale (e u ^ n)) Q :=
      (hX.1.contDiffAt (hS.mem_nhds (hΩS δ B u hδ Q hQ))).comp Q (planeScale (L := L) (e u ^ n)).contDiff.contDiffAt
    refine ⟨fun u Q hQ => ?_,fun k N => ?_⟩
    · rw [hray u]; exact (contDiffAt_const.mul (hsm u Q hQ)).contDiffWithinAt
    obtain ⟨C,hC⟩ := rapid_ray_bound hX k (w.mult*(n-1) + n*k) N n (NeZero.pos n) hδ
    refine ⟨C,fun u Q hQ h hh => ?_⟩
    have hQΩ := hTΩ δ B hδ hQ
    have hfun : ray u = (((modulus F v u.val : ℝ) : ℂ)^(n-1) • (X ∘ planeScale (e u ^ n)) : L × L → ℂ) := by
      rw [hray u]; rfl
    rw [hfun,iteratedFDeriv_const_smul_apply ((hsm u Q hQΩ).of_le (by exact_mod_cast le_top)),
      iteratedFDeriv_comp_clm_of_isOpen' hS hX.1 _ (hΩS δ B u hδ Q hQΩ) k,
      smul_apply,norm_smul,hm u]
    set φ := (iteratedFDeriv ℝ k X (planeScale (e u ^ n) Q)).compContinuousLinearMap fun _ => planeScale (e u ^ n)
    have hφh : ‖φ h‖ ≤ ‖iteratedFDeriv ℝ k X (planeScale (e u ^ n) Q)‖ * ‖u.val‖^(n*k) := by
      refine (φ.le_opNorm h).trans ?_
      have hprod : ∏ i, ‖h i‖ ≤ 1 := Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hh i
      have hc := (iteratedFDeriv ℝ k X (planeScale (e u ^ n) Q)).norm_compContinuousLinearMap_le
        (fun _ : Fin k => planeScale (e u ^ n))
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hc
      have hs : ‖planeScale (e u ^ n)‖ ≤ ‖u.val‖^n := by
        have := norm_planeScale_le (e u ^ n); rwa [norm_pow,norm_e] at this
      calc ‖φ‖ * ∏ i, ‖h i‖ ≤ ‖φ‖ * 1 := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
        _ ≤ ‖iteratedFDeriv ℝ k X (planeScale (e u ^ n) Q)‖ * ‖planeScale (e u ^ n)‖^k := by
          rw [mul_one]; exact hc
        _ ≤ _ := by rw [pow_mul]; gcongr
    have hb := hC ‖u.val‖ (norm_nonneg _) _ (hΩS δ B u hδ Q hQΩ) (hTn δ B u Q hQ)
    calc ‖u.val‖^(w.mult*(n-1)) * ‖φ h‖ * (1 + ‖u.val‖)^N
        ≤ ‖u.val‖^(w.mult*(n-1)) * (‖iteratedFDeriv ℝ k X (planeScale (e u ^ n) Q)‖ * ‖u.val‖^(n*k)) *
            (1 + ‖u.val‖)^N := by gcongr
      _ = ‖u.val‖^(w.mult*(n-1) + n*k) * ‖iteratedFDeriv ℝ k X (planeScale (e u ^ n) Q)‖ * (1 + ‖u.val‖)^N := by
          rw [pow_add]; ring
      _ ≤ C := hb
  have hrayX (u : Kˣ) : rayX (n := n) w e f u = fun Q => ((modulus F v u.val : ℝ) : ℂ)^(n-1) *
      (fun p : L × L => xChart f (e.symm p.1, e.symm p.2)) (planeScale (e u ^ n) Q) := by
    funext Q; simp [rayX]
  have hrayY (u : Kˣ) : rayY (n := n) w e f u = fun Q => ((modulus F v u.val : ℝ) : ℂ)^(n-1) *
      (fun p : L × L => yChart f (e.symm p.1, e.symm p.2)) (planeScale (e u ^ n) Q) := by
    funext Q; simp [rayY]
  have hu0 (u : Kˣ) : e u ^ n ≠ 0 := pow_ne_zero _ ((map_ne_zero e).mpr u.ne_zero)
  constructor
  · intro δ B hδ
    have := go _ _ (isOpen_ne_fun continuous_fst continuous_const) htest.1 (rayX (n := n) w e f) hrayX
      (fun δ B => regionOX δ B) (fun δ B u hδ Q hQ => by
        have h1 : δ/2 < ‖Q.1‖ := hQ.1
        simp only [planeScale_apply,mem_ofPred_eq]
        exact mul_ne_zero (hu0 u) (norm_pos_iff.mp (by linarith)))
      (fun δ B => {Q : L × L | δ ≤ ‖Q.1‖ ∧ ‖Q.1‖ ≤ B ∧ ‖Q.2‖ ≤ B})
      (fun δ B hδ Q hQ => ⟨by linarith [hQ.1],by linarith [hQ.2.1],by linarith [hQ.2.2]⟩) isOpen_regionOX
      (fun δ B u Q hQ => by
        rw [planeScale_apply,Prod.norm_def]
        refine le_max_of_le_left ?_
        rw [norm_mul,norm_pow,norm_e]; exact mul_le_mul_of_nonneg_left hQ.1 (by positivity)) δ B hδ
    exact ⟨this.1,fun k N => by
      obtain ⟨C,hC⟩ := this.2 k N
      exact ⟨C,fun u Q h1 h2 h3 => hC u Q ⟨h1,h2,h3⟩⟩⟩
  · intro δ B hδ
    have := go _ _ (isOpen_ne_fun continuous_snd continuous_const) htest.2 (rayY (n := n) w e f) hrayY
      (fun δ B => regionOY δ B) (fun δ B u hδ Q hQ => by
        have h1 : δ/2 < ‖Q.2‖ := hQ.1
        simp only [planeScale_apply,mem_ofPred_eq]
        exact mul_ne_zero (hu0 u) (norm_pos_iff.mp (by linarith)))
      (fun δ B => {Q : L × L | δ ≤ ‖Q.2‖ ∧ ‖Q.2‖ ≤ B ∧ ‖Q.1‖ ≤ B})
      (fun δ B hδ Q hQ => ⟨by linarith [hQ.1],by linarith [hQ.2.1],by linarith [hQ.2.2]⟩) isOpen_regionOY
      (fun δ B u Q hQ => by
        rw [planeScale_apply,Prod.norm_def]
        refine le_max_of_le_right ?_
        rw [norm_mul,norm_pow,norm_e]; exact mul_le_mul_of_nonneg_left hQ.1 (by positivity)) δ B hδ
    exact ⟨this.1,fun k N => by
      obtain ⟨C,hC⟩ := this.2 k N
      exact ⟨C,fun u Q h1 h2 h3 => hC u Q ⟨h1,h2,h3⟩⟩⟩

omit [NeZero n] in
theorem rayX_add {L : Type} [NormedField L] (e : K ≃+* L) (g h : Charts K) (u : Kˣ) :
    rayX (n := n) w e (g + h) u = rayX (n := n) w e g u + rayX (n := n) w e h u := by
  funext Q; simp only [rayX,Pi.add_apply,xChart,Prod.fst_add,Pi.add_apply]; split_ifs <;> ring

omit [NeZero n] in
theorem rayX_smul {L : Type} [NormedField L] (e : K ≃+* L) (c : ℂ) (g : Charts K) (u : Kˣ) :
    rayX (n := n) w e (c • g) u = c • rayX (n := n) w e g u := by
  funext Q; simp only [rayX,Pi.smul_apply,xChart,Prod.smul_fst,Pi.smul_apply,smul_eq_mul]; split_ifs <;> ring

omit [NeZero n] in
theorem rayX_zero {L : Type} [NormedField L] (e : K ≃+* L) (u : Kˣ) :
    rayX (n := n) w e (0 : Charts K) u = 0 := by
  funext Q; simp [rayX,xChart]

omit [NeZero n] in
theorem RayBoundX.add {L : Type} [NormedField L] [NormedAlgebra ℝ L] {e : K ≃+* L} {g h : Charts K}
    (hg : RayBoundX (n := n) w e g) (hh : RayBoundX (n := n) w e h) : RayBoundX (n := n) w e (g + h) := by
  intro δ B hδ
  obtain ⟨s1,b1⟩ := hg δ B hδ
  obtain ⟨s2,b2⟩ := hh δ B hδ
  refine ⟨fun u => by rw [rayX_add]; exact (s1 u).add (s2 u),fun k N => ?_⟩
  obtain ⟨C1,hC1⟩ := b1 k N
  obtain ⟨C2,hC2⟩ := b2 k N
  refine ⟨C1 + C2,fun u Q h1 h2 h3 dir hdir => ?_⟩
  have hQ : Q ∈ regionOX δ B := ⟨by linarith,by linarith,by linarith⟩
  have hO := (isOpen_regionOX δ B).mem_nhds hQ
  rw [rayX_add,iteratedFDeriv_add_apply (((s1 u).contDiffAt hO).of_le (by exact_mod_cast le_top))
    (((s2 u).contDiffAt hO).of_le (by exact_mod_cast le_top)),add_apply]
  calc _ ≤ (‖(iteratedFDeriv ℝ k (rayX (n := n) w e g u) Q) dir‖ +
        ‖(iteratedFDeriv ℝ k (rayX (n := n) w e h u) Q) dir‖) * (1 + ‖u.val‖)^N :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
    _ ≤ C1 + C2 := by rw [add_mul]; exact add_le_add (hC1 u Q h1 h2 h3 dir hdir) (hC2 u Q h1 h2 h3 dir hdir)

omit [NeZero n] in
theorem RayBoundX.smul {L : Type} [NormedField L] [NormedAlgebra ℝ L] {e : K ≃+* L} {g : Charts K}
    (c : ℂ) (hg : RayBoundX (n := n) w e g) : RayBoundX (n := n) w e (c • g) := by
  intro δ B hδ
  obtain ⟨s1,b1⟩ := hg δ B hδ
  refine ⟨fun u => by rw [rayX_smul]; exact (s1 u).const_smul c,fun k N => ?_⟩
  obtain ⟨C1,hC1⟩ := b1 k N
  refine ⟨‖c‖ * C1,fun u Q h1 h2 h3 dir hdir => ?_⟩
  have hQ : Q ∈ regionOX δ B := ⟨by linarith,by linarith,by linarith⟩
  have hO := (isOpen_regionOX δ B).mem_nhds hQ
  rw [rayX_smul,iteratedFDeriv_const_smul_apply (((s1 u).contDiffAt hO).of_le (by exact_mod_cast le_top)),
    smul_apply,norm_smul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC1 u Q h1 h2 h3 dir hdir) (norm_nonneg _)

omit [NeZero n] in
theorem RayBoundX.zero {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) :
    RayBoundX (n := n) w e (0 : Charts K) := by
  intro δ B hδ
  refine ⟨fun u => by rw [rayX_zero]; exact contDiffOn_const,fun k N => ⟨0,fun u Q _ _ _ dir _ => ?_⟩⟩
  rw [rayX_zero,iteratedFDeriv_zero]
  simp

omit [NeZero n] in
theorem rayY_add {L : Type} [NormedField L] (e : K ≃+* L) (g h : Charts K) (u : Kˣ) :
    rayY (n := n) w e (g + h) u = rayY (n := n) w e g u + rayY (n := n) w e h u := by
  funext Q; simp only [rayY,Pi.add_apply,yChart,Prod.snd_add,Pi.add_apply]; split_ifs <;> ring

omit [NeZero n] in
theorem rayY_smul {L : Type} [NormedField L] (e : K ≃+* L) (c : ℂ) (g : Charts K) (u : Kˣ) :
    rayY (n := n) w e (c • g) u = c • rayY (n := n) w e g u := by
  funext Q; simp only [rayY,Pi.smul_apply,yChart,Prod.smul_snd,Pi.smul_apply,smul_eq_mul]; split_ifs <;> ring

omit [NeZero n] in
theorem rayY_zero {L : Type} [NormedField L] (e : K ≃+* L) (u : Kˣ) :
    rayY (n := n) w e (0 : Charts K) u = 0 := by
  funext Q; simp [rayY,yChart]

omit [NeZero n] in
theorem RayBoundY.add {L : Type} [NormedField L] [NormedAlgebra ℝ L] {e : K ≃+* L} {g h : Charts K}
    (hg : RayBoundY (n := n) w e g) (hh : RayBoundY (n := n) w e h) : RayBoundY (n := n) w e (g + h) := by
  intro δ B hδ
  obtain ⟨s1,b1⟩ := hg δ B hδ
  obtain ⟨s2,b2⟩ := hh δ B hδ
  refine ⟨fun u => by rw [rayY_add]; exact (s1 u).add (s2 u),fun k N => ?_⟩
  obtain ⟨C1,hC1⟩ := b1 k N
  obtain ⟨C2,hC2⟩ := b2 k N
  refine ⟨C1 + C2,fun u Q h1 h2 h3 dir hdir => ?_⟩
  have hQ : Q ∈ regionOY δ B := ⟨by linarith,by linarith,by linarith⟩
  have hO := (isOpen_regionOY δ B).mem_nhds hQ
  rw [rayY_add,iteratedFDeriv_add_apply (((s1 u).contDiffAt hO).of_le (by exact_mod_cast le_top))
    (((s2 u).contDiffAt hO).of_le (by exact_mod_cast le_top)),add_apply]
  calc _ ≤ (‖(iteratedFDeriv ℝ k (rayY (n := n) w e g u) Q) dir‖ +
        ‖(iteratedFDeriv ℝ k (rayY (n := n) w e h u) Q) dir‖) * (1 + ‖u.val‖)^N :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
    _ ≤ C1 + C2 := by rw [add_mul]; exact add_le_add (hC1 u Q h1 h2 h3 dir hdir) (hC2 u Q h1 h2 h3 dir hdir)

omit [NeZero n] in
theorem RayBoundY.smul {L : Type} [NormedField L] [NormedAlgebra ℝ L] {e : K ≃+* L} {g : Charts K}
    (c : ℂ) (hg : RayBoundY (n := n) w e g) : RayBoundY (n := n) w e (c • g) := by
  intro δ B hδ
  obtain ⟨s1,b1⟩ := hg δ B hδ
  refine ⟨fun u => by rw [rayY_smul]; exact (s1 u).const_smul c,fun k N => ?_⟩
  obtain ⟨C1,hC1⟩ := b1 k N
  refine ⟨‖c‖ * C1,fun u Q h1 h2 h3 dir hdir => ?_⟩
  have hQ : Q ∈ regionOY δ B := ⟨by linarith,by linarith,by linarith⟩
  have hO := (isOpen_regionOY δ B).mem_nhds hQ
  rw [rayY_smul,iteratedFDeriv_const_smul_apply (((s1 u).contDiffAt hO).of_le (by exact_mod_cast le_top)),
    smul_apply,norm_smul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC1 u Q h1 h2 h3 dir hdir) (norm_nonneg _)

omit [NeZero n] in
theorem RayBoundY.zero {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : K ≃+* L) :
    RayBoundY (n := n) w e (0 : Charts K) := by
  intro δ B hδ
  refine ⟨fun u => by rw [rayY_zero]; exact contDiffOn_const,fun k N => ⟨0,fun u Q _ _ _ dir _ => ?_⟩⟩
  rw [rayY_zero,iteratedFDeriv_zero]
  simp

/-- Proposition 8.1 at a real or complex place: for every element of the local Schwartz space, the
normalized rays μ ↦ |μ|^{n-1} Ψ(μⁿ v) in either chart are smooth in v, and all their derivatives in v
decay rapidly in μ, uniformly for v in compact subsets of the chart and μ ∈ F^×. -/
theorem schwartz_rayBound {L : Type} [NormedField L] [NormedAlgebra ℝ L] [ProperSpace L]
    (e : K ≃+* L) (he : Isometry e) (htests : ∀ f ∈ d.testSet v, archTest e f) :
    ∀ Φ ∈ d.schwartz v, RayBoundX (n := n) w e Φ ∧ RayBoundY (n := n) w e Φ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem f hf =>
    rcases hf with hf | ⟨f₀,hf₀,rfl⟩
    · exact rayBound_test w e he (htests f hf)
    · exact ⟨d.rayBoundX_transform w e he (htests f₀ hf₀),d.rayBoundY_transform w e he (htests f₀ hf₀)⟩
  | zero => exact ⟨RayBoundX.zero w e,RayBoundY.zero w e⟩
  | add _ _ _ _ hg hh => exact ⟨hg.1.add w hh.1,hg.2.add w hh.2⟩
  | smul a _ _ hg => exact ⟨hg.1.smul w a,hg.2.smul w a⟩

/-- Proposition 8.1 at a real place. -/
theorem schwartz_rayBound_real (hw : w.IsReal) (Φ : Charts K) (hΦ : Φ ∈ d.schwartz v) :
    RayBoundX (n := n) w (InfinitePlace.Completion.ringEquivRealOfIsReal hw) Φ ∧
      RayBoundY (n := n) w (InfinitePlace.Completion.ringEquivRealOfIsReal hw) Φ :=
  d.schwartz_rayBound w _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw)
    (fun f hf => by simpa only [testSet,hw,↓reduceDIte] using! hf.2) Φ hΦ

/-- Proposition 8.1 at a complex place. -/
theorem schwartz_rayBound_complex (hw : ¬ w.IsReal) (Φ : Charts K) (hΦ : Φ ∈ d.schwartz v) :
    RayBoundX (n := n) w (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)) Φ ∧
      RayBoundY (n := n) w (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)) Φ :=
  d.schwartz_rayBound w _ (InfinitePlace.Completion.isometry_extensionEmbedding w)
    (fun f hf => by simpa only [testSet,hw,↓reduceDIte] using! hf.2) Φ hΦ

end Datum

end MetaplecticPoisson
