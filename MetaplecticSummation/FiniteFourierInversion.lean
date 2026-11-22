import MetaplecticSummation.Marginals
import MetaplecticSummation.FourierOrthogonality
import Mathlib.MeasureTheory.Integral.Prod

/-! One-dimensional Fourier inversion with the self-dual Haar measure at finite places. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open MeasureTheory Set Filter Metric NumberField IsDedekindDomain
open scoped Topology
open Classical

private def fourierIntegral {K : Type*} [NormedField K] [MeasurableSpace K]
    (μ : Measure K) (ψ : K → ℂ) (f : K → ℂ) (u : K) := ∫ t, f t * ψ (u*t) ∂μ

/-- The bilinear Fourier identity, by absolute convergence of the joint integral. -/
private theorem fourierIntegral_swap {K : Type*} [NormedField K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K] (μ : Measure K) [SFinite μ] {ψ f g : K → ℂ} (hψ : Continuous ψ) (hnorm : ∀ z, ‖ψ z‖ = 1)
    (hf : Continuous f) (hg : Continuous g) (hfi : Integrable f μ) (hgi : Integrable g μ) :
    (∫ x, fourierIntegral μ ψ f x * g x ∂μ) = ∫ t, f t * fourierIntegral μ ψ g t ∂μ := by
  let H (x t : K) := f t * ψ (x*t) * g x
  have hi : Integrable (Function.uncurry H) (μ.prod μ) := by
    apply (hgi.norm.mul_prod hfi.norm).mono
    · exact ((hf.comp continuous_snd).mul (hψ.comp (continuous_fst.mul continuous_snd)) |>.mul
        (hg.comp continuous_fst)).aestronglyMeasurable
    · filter_upwards with z
      simp [Function.uncurry,H,norm_mul,hnorm,mul_comm]
  calc
    _ = ∫ x, ∫ t, H x t ∂μ ∂μ := by simp only [H,fourierIntegral,integral_mul_const]
    _ = ∫ t, ∫ x, H x t ∂μ ∂μ := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      unfold fourierIntegral
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp [H]
      rw [mul_comm x t]
      ring

private theorem fourierIntegral_test {K : Type*} [NormedField K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] {ψ f : K → ℂ}
    (hc : IsLocallyConstant f) (hk : HasCompactSupport f) (hl : IsLocallyConstant ψ)
    (ha : ∀ x y, ψ (x+y) = ψ x * ψ y) (hn : ∃ z, ψ z ≠ 1) :
    IsLocallyConstant (fourierIntegral μ ψ f) ∧ HasCompactSupport (fourierIntegral μ ψ f) := by
  let g (_ : Unit) (t : K) := f t
  have fam : SmoothFiniteFamily g :=
    smoothFiniteFamily_of_support (hc.comp_continuous (continuous_snd : Continuous (Prod.snd : Unit × K → K)))
      (fun _ _ => ⟨tsupport f,hk,fun _ _ _ hz => image_eq_zero_of_notMem_tsupport hz⟩)
  have out := fam.fourier μ hl ha hn
  obtain ⟨C,hC,ho⟩ := (out.2 {()} isCompact_singleton).2.1
  exact ⟨out.1.comp_continuous ((continuous_const (y := ())).prodMk (continuous_id : Continuous (id : K → K))),
    HasCompactSupport.intro hC (ho () (mem_singleton ()))⟩

variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

omit [NeZero n] in
theorem hat_finite_bruhat (p : HeightOneSpectrum (𝓞 F)) {f : LocalField F (.inr p) → ℂ}
    (hf : Bruhat (.inr p) f) : Bruhat (.inr p) (d.hat (.inr p) f) := by
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace (p.adicCompletion F) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  letI : ProperSpace (LocalField F (.inr p)) := inferInstanceAs (ProperSpace (p.adicCompletion F))
  let dx := selfDual F d.character (.inr p)
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character (.inr p)).exists.choose_spec.1
  exact fourierIntegral_test dx hf.1 hf.2 (d.character.locallyConstant_finiteValue p)
    (d.character.localValue_add _) (d.character.nontrivial_finiteValue p)

private theorem integral_fourier_zero {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [ProperSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] [SFinite μ]
    {ψ f : K → ℂ} (hc : Continuous ψ) (ha : ∀ x y, ψ (x+y) = ψ x * ψ y)
    (hnorm : ∀ z, ‖ψ z‖ = 1) (hn : ∃ z, ψ z ≠ 1)
    (hP : ∀ g : K → ℂ, Continuous g → HasCompactSupport g →
      (∫⁻ y, ‖∫ x, g x * ψ (x*y) ∂μ‖ₑ^2 ∂μ) = ∫⁻ x, ‖g x‖ₑ^2 ∂μ)
    (hf : IsLocallyConstant f) (hk : HasCompactSupport f)
    (hhat : HasCompactSupport (fourierIntegral μ ψ f)) : (∫ u, fourierIntegral μ ψ f u ∂μ) = f 0 := by
  obtain ⟨z,hz⟩ := hn
  obtain ⟨r,hr,hrf⟩ := Metric.mem_nhds_iff.mp (hf.eventually_eq 0)
  obtain ⟨B,hB⟩ := hhat.exists_bound_of_continuousOn (f := id) continuous_id.continuousOn
  let R := max 1 (max B (‖z‖/r))
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  let U : AddSubgroup K :=
    { carrier := closedBall 0 R
      zero_mem' := by simp [hR.le]
      add_mem' := by
        intro a b ha hb
        rw [mem_closedBall,dist_zero_right] at ha hb ⊢
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
      neg_mem' := by intro a ha; simpa only [mem_closedBall,dist_zero_right,norm_neg] using ha }
  let D := {t : K | ∀ y ∈ U, ψ (t*y) = 1}
  have hD : IsClosed D := by
    have he : D = ⋂ y ∈ (U : Set K), {t | ψ (t*y) = 1} := by ext t; simp [D]
    rw [he]
    exact isClosed_biInter fun y _ => isClosed_eq (hc.comp (continuous_id.mul continuous_const)) continuous_const
  have hopen : IsClopen (U : Set K) := IsUltrametricDist.isClopen_closedBall 0 hR.ne'
  have hcomp : IsCompact (U : Set K) := isCompact_closedBall _ _
  have vol := volume_mul_annihilator U D hD.measurableSet hopen hcomp μ ψ ha (fun _ => Iff.rfl) hP
  let g := (U : Set K).indicator (fun _ => (1 : ℂ))
  have htrans (u : K) : fourierIntegral μ ψ g u = D.indicator (fun _ => (μ.real U : ℂ)) u := by
    unfold fourierIntegral
    simpa only [mul_comm u] using hat_addSubgroup_indicator U D hopen.isOpen.measurableSet μ ψ ha (fun _ => Iff.rfl) u
  have hfactor (t : K) (ht : t ∈ D) : f t = f 0 := by
    apply hrf
    rw [mem_ball_zero_iff]
    by_contra! hlarge
    have ht₀ : t ≠ 0 := norm_pos_iff.mp (hr.trans_le hlarge)
    have hzu : z/t ∈ U := by
      change z/t ∈ closedBall 0 R
      rw [mem_closedBall,dist_zero_right,norm_div]
      exact (div_le_div_of_nonneg_left (norm_nonneg _) hr hlarge).trans
        ((le_max_right _ _).trans (le_max_right _ _))
    exact hz (by simpa only [mul_div_cancel₀ _ ht₀] using ht _ hzu)
  have hcut (u : K) : fourierIntegral μ ψ f u * g u = fourierIntegral μ ψ f u := by
    by_cases hu : u ∈ U
    · simp [g,hu]
    · have ho : u ∉ tsupport (fourierIntegral μ ψ f) := fun h =>
        hu (show u ∈ closedBall 0 R by
          rw [mem_closedBall,dist_zero_right]
          exact (hB u h).trans ((le_max_left _ _).trans (le_max_right _ _)))
      simp [image_eq_zero_of_notMem_tsupport ho]
  have he := fourierIntegral_swap μ hc hnorm hf.continuous (hopen.continuous_indicator continuous_const)
    (hf.continuous.integrable_of_hasCompactSupport hk)
    ((hopen.continuous_indicator continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hcomp (fun _ hu => indicator_of_notMem hu _)) : Integrable g μ)
  change (∫ x, fourierIntegral μ ψ f x * g x ∂μ) = ∫ t, f t * fourierIntegral μ ψ g t ∂μ at he
  simp_rw [hcut,htrans] at he
  have hd (t : K) : f t * D.indicator (fun _ => (μ.real U : ℂ)) t =
      D.indicator (fun _ => (μ.real U : ℂ)*f 0) t := by
    by_cases ht : t ∈ D <;> simp [ht,hfactor t,mul_comm]
  simp_rw [hd] at he
  rw [he,integral_indicator hD.measurableSet,integral_const,measureReal_restrict_apply_univ,Complex.real_smul]
  change (μ.real D : ℂ) * ((μ.real U : ℂ) * f 0) = f 0
  rw [mul_left_comm,← mul_assoc,← Complex.ofReal_mul,vol,Complex.ofReal_one,one_mul]

omit [NeZero n] in
/-- Affine substitution in the ordinary Fourier integral at every place. -/
theorem hat_affine (v : Place F) (f : LocalField F v → ℂ) (a μ : LocalField F v) (b : (LocalField F v)ˣ) :
    d.hat v (fun t => f ((t-a)*b.val)) μ =
      (d.hat v f (μ/b.val) / (modulus F v b.val : ℂ)) * d.character.localValue F v (μ*a) := by
  let dx := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let g (t : LocalField F v) := f t * d.character.localValue F v ((μ/b.val)*t)
  let H (t : LocalField F v) := f ((t-a)*b.val) * d.character.localValue F v (μ*t)
  have he (t : LocalField F v) : H (t+a) = g (b.val*t) * d.character.localValue F v (μ*a) := by
    have hphase : (μ/b.val)*(b.val*t) = μ*t := by field_simp
    simp only [H,g,add_sub_cancel_right,hphase,mul_add,d.character.localValue_add,mul_assoc]
    rw [mul_comm b.val t]
  have h := integral_add_right_eq_self (μ := dx) H a
  simp_rw [he] at h
  rw [integral_mul_const,d.integral_local_mul] at h
  exact h.symm

omit [NeZero n] in
/-- The affine Fourier integral in the linear-factor calculation of Appendix A. -/
theorem finite_linearFactor_pairing (p : HeightOneSpectrum (𝓞 F)) {f ρ : LocalField F (.inr p) → ℂ}
    (hf : Bruhat (.inr p) f) (hρ : Bruhat (.inr p) ρ) (a : LocalField F (.inr p))
    (b : (LocalField F (.inr p))ˣ) :
    let v : Place F := .inr p
    let dx := selfDual F d.character v
    (∫ t, d.hat v ρ t * f ((t-a)*b.val) ∂dx) =
      ∫ μ, ρ μ * (d.hat v f (μ/b.val) / (modulus F v b.val : ℂ)) * d.character.localValue F v (μ*a) ∂dx := by
  let v : Place F := .inr p
  let K := LocalField F v
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace (p.adicCompletion F) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  letI : ProperSpace K := inferInstanceAs (ProperSpace (p.adicCompletion F))
  let dx := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let g (t : K) := f ((t-a)*b.val)
  have hg : Continuous g := hf.1.continuous.comp ((continuous_id.sub continuous_const).mul continuous_const)
  have hk : HasCompactSupport g := by
    have hc : HasCompactSupport f := hf.2
    have hs : HasCompactSupport (fun t : K => f (b.val*t)) := hc.comp_homeomorph (Homeomorph.mulLeft₀ b.val b.ne_zero)
    have h := hs.comp_homeomorph (Homeomorph.addRight (-a))
    change HasCompactSupport (fun t : K => f (b.val*(t + -a))) at h
    simpa only [g,sub_eq_add_neg,mul_comm b.val] using h
  have h := fourierIntegral_swap dx (d.character.continuous_localValue v) (d.character.norm_localValue v)
    hρ.1.continuous hg (hρ.integrable d) (hg.integrable_of_hasCompactSupport hk)
  change (∫ t, d.hat v ρ t * g t ∂dx) = ∫ μ, ρ μ * d.hat v g μ ∂dx at h
  refine h.trans (integral_congr_ae ?_)
  filter_upwards with μ
  rw [show d.hat v g μ = _ from d.hat_affine v f a μ b]
  exact (mul_assoc ..).symm

omit [NeZero n] in
/-- Additive Fourier inversion at zero at any finite completion, with any
conductor of the additive character. -/
theorem integral_hat_finite (p : HeightOneSpectrum (𝓞 F)) {f : LocalField F (.inr p) → ℂ}
    (hf : Bruhat (.inr p) f) : (∫ t, d.hat (.inr p) f t ∂(selfDual F d.character (.inr p))) = f 0 := by
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace (p.adicCompletion F) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  letI : MeasurableSpace (p.adicCompletion F) := borel _
  letI : BorelSpace (p.adicCompletion F) := ⟨rfl⟩
  let dx : Measure (p.adicCompletion F) := selfDual F d.character (.inr p)
  have hP := (existsUnique_selfDual F d.character (.inr p)).exists.choose_spec
  letI : dx.IsAddHaarMeasure := hP.1
  exact integral_fourier_zero (K := p.adicCompletion F) dx (d.character.continuous_localValue (.inr p)) (d.character.localValue_add (.inr p))
    (d.character.norm_localValue (.inr p)) (d.character.nontrivial_finiteValue p) hP.2 hf.1 hf.2
    (d.hat_finite_bruhat p hf).2

omit [NeZero n] in
/-- With the positive additive phase, the square of the ordinary Fourier
transform on finite-place Schwartz–Bruhat functions is reflection. -/
theorem hat_hat_finite (p : HeightOneSpectrum (𝓞 F)) {f : LocalField F (.inr p) → ℂ}
    (hf : Bruhat (.inr p) f) (x : LocalField F (.inr p)) :
    d.hat (.inr p) (d.hat (.inr p) f) x = f (-x) := by
  let v : Place F := .inr p
  let g (t : LocalField F v) := f (t + -x)
  have hg : Bruhat v g := ⟨hf.1.comp_continuous (continuous_id.add continuous_const),
    hf.2.comp_homeomorph (Homeomorph.addRight (-x))⟩
  have he (u : LocalField F v) : d.hat v g u = d.hat v f u * d.character.localValue F v (x*u) := by
    let h (t : LocalField F v) := g t * d.character.localValue F v (u*t)
    let dx := selfDual F d.character v
    letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
    have ht := integral_add_right_eq_self (μ := dx) h x
    have hs (t : LocalField F v) : h (t+x) =
        (f t * d.character.localValue F v (u*t)) * d.character.localValue F v (x*u) := by
      simp only [h,g,add_neg_cancel_right,mul_add,d.character.localValue_add,mul_assoc,mul_comm x u]
    simp_rw [hs] at ht
    rw [integral_mul_const] at ht
    exact ht.symm
  have h := d.integral_hat_finite p hg
  change (∫ u, d.hat v g u ∂(selfDual F d.character v)) = g 0 at h
  simp_rw [he] at h
  simp only [g,zero_add] at h
  exact h

end MetaplecticPoisson.Datum
