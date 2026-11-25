import MetaplecticSummation.FiniteRayFourier

/-! The normalized ray extensions of §8 at a finite place. -/

noncomputable section
namespace MetaplecticPoisson
open Filter Set MeasureTheory Metric
open scoped Topology
open Classical

variable {P K : Type*} [TopologicalSpace P] [NormedField K] {n : ℕ}

/-- A bounded Schwartz–Bruhat family extending the prescribed normalized values
along nonzero power rays. The parameter is a point of one of the two charts. -/
def HasFiniteRayExtension (n : ℕ) (dil : Kˣ → P → P) (f : P → ℂ) : Prop :=
  ∃ e : P → K → ℂ, SmoothFiniteFamily e ∧
    ∀ p (u : Kˣ), e p u.val = (‖u.val‖ : ℂ)^(n-1) * f (dil u p)

namespace HasFiniteRayExtension
variable {dil : Kˣ → P → P} {f g : P → ℂ}

protected theorem add (hf : HasFiniteRayExtension n dil f) (hg : HasFiniteRayExtension n dil g) :
    HasFiniteRayExtension n dil (f+g) := by
  obtain ⟨e,he,hf⟩ := hf
  obtain ⟨b,hb,hg⟩ := hg
  refine ⟨fun p t => e p t + b p t, smoothFiniteFamily_of_support (he.1.add hb.1) ?_,?_⟩
  · intro T hT
    obtain ⟨C,hC,h₁⟩ := (he.2 T hT).2.1
    obtain ⟨D,hD,h₂⟩ := (hb.2 T hT).2.1
    refine ⟨C ∪ D,hC.union hD,fun p hp t ht => ?_⟩
    rw [h₁ p hp t (fun h => ht (Or.inl h)),h₂ p hp t (fun h => ht (Or.inr h)),add_zero]
  · intro p u
    simp only [hf,hg,Pi.add_apply,mul_add]

protected theorem smul (hf : HasFiniteRayExtension n dil f) (c : ℂ) :
    HasFiniteRayExtension n dil (c • f) := by
  obtain ⟨e,he,hf⟩ := hf
  refine ⟨fun p t => c * e p t,smoothFiniteFamily_of_support (he.1.comp (c * ·)) ?_,?_⟩
  · intro T hT
    obtain ⟨C,hC,h₁⟩ := (he.2 T hT).2.1
    exact ⟨C,hC,fun p hp t ht => by rw [h₁ p hp t ht,mul_zero]⟩
  · intro p u
    simp only [hf,Pi.smul_apply,smul_eq_mul,mul_left_comm]

protected theorem zero : HasFiniteRayExtension n dil 0 := by
  refine ⟨0,smoothFiniteFamily_of_support (IsLocallyConstant.const 0) ?_,?_⟩
  · exact fun _ _ => ⟨∅,isCompact_empty,fun _ _ _ _ => rfl⟩
  · simp

/-- An open-chart test function with compact support off the origin extends
by zero at ray parameter zero. -/
theorem of_test {K : Type*} [NontriviallyNormedField K] {dil : Kˣ → P → P} [ProperSpace K] [IsUltrametricDist K] (hn : n ≠ 0)
    (a : P → Kˣ) (b : P → K) (ha : Continuous a) (hb : Continuous b)
    (hd : Continuous (fun w : P × Kˣ => dil w.2 w.1))
    (had : ∀ p u, a (dil u p) = u^n * a p) (hbd : ∀ p u, b (dil u p) = u.val^n * b p)
    (hf : IsLocallyConstant f) {C : Set (K × K)} (hC : IsCompact C) (h0 : (0 : K × K) ∉ C)
    (ho : ∀ p, ((a p).val,b p) ∉ C → f p = 0) : HasFiniteRayExtension n dil f := by
  let E (p : P) (t : K) : ℂ :=
    if ht : t = 0 then 0 else (‖t‖ : ℂ)^(n-1) * f (dil (Units.mk0 t ht) p)
  let pt (p : P) (t : K) := (t^n * (a p).val,t^n * b p)
  have vanish (p : P) (t : K) (h : pt p t ∉ C) : E p t = 0 := by
    by_cases ht : t = 0
    · simp [E,ht]
    · have hz := ho (dil (Units.mk0 t ht) p) (by simpa [had,hbd,pt] using h)
      simp [E,ht,hz]
  refine ⟨E,smoothFiniteFamily_of_support ?_ ?_,fun p u => by simp [E,u.ne_zero]⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨p,t⟩
    by_cases ht : t = 0
    · subst t
      have hc : Continuous (Function.uncurry pt) :=
        ((continuous_snd.pow n).mul ((Units.continuous_val.comp ha).comp continuous_fst)).prodMk
        ((continuous_snd.pow n).mul (hb.comp continuous_fst))
      have he := (hc.tendsto (p,0)).eventually
        (hC.isClosed.isOpen_compl.mem_nhds (by simpa [pt,zero_pow hn] using (show (0,0) ∉ C from h0)))
      filter_upwards [he] with q hq
      simpa [Function.uncurry,E] using vanish q.1 q.2 hq
    · let U (s : K) : Kˣ := if hs : s = 0 then 1 else Units.mk0 s hs
      have hu : ContinuousAt U t := by
        apply Units.isEmbedding_val₀.tendsto_nhds_iff.mpr
        simp only [U,ht]
        exact tendsto_id.congr' ((eventually_ne_nhds ht).mono fun _ hs => by simp [hs])
      have hq : ContinuousAt (fun q : P × K => (q.1,U q.2)) (p,t) :=
        continuous_fst.continuousAt.prodMk (hu.comp_of_eq continuous_snd.continuousAt rfl)
      have hl := ((locallyConstant_norm_units.comp_continuous (show Continuous (Prod.snd : P × Kˣ → Kˣ) from continuous_snd)).comp
        (fun r : ℝ => (r : ℂ)^(n-1))).mul (hf.comp_continuous hd)
      have he := hq.tendsto.eventually (hl.eventually_eq (p,U t))
      filter_upwards [he, (continuous_snd.tendsto (p,t)).eventually (eventually_ne_nhds ht)] with q heq hne
      simpa [Function.uncurry,E,U,hne,ht] using heq
  · intro T hT
    let ratio (w : P × (K × K)) := w.2.1 / (a w.1).val
    have hc : Continuous ratio := ((continuous_fst.comp continuous_snd)).div
      ((Units.continuous_val.comp ha).comp continuous_fst) (fun _ => (a _).ne_zero)
    obtain ⟨B,hB⟩ := (hT.prod hC).exists_bound_of_continuousOn hc.continuousOn
    refine ⟨closedBall 0 (max B 1),isCompact_closedBall _ _,fun p hp t ht => vanish p t ?_⟩
    intro hz
    have h := hB (p,pt p t) ⟨hp,hz⟩
    simp only [ratio,pt,mul_div_cancel_right₀ _ (a p).ne_zero,norm_pow] at h
    have hlt : max B 1 < ‖t‖ := by simpa [mem_closedBall,dist_zero_right] using ht
    exact (not_lt_of_ge h) ((le_max_left _ _).trans_lt (hlt.trans_le
      (le_self_pow₀ ((le_max_right _ _).trans hlt.le) hn)))

end HasFiniteRayExtension

/-- The two charts in the normalized ray assertion in §8. -/
def FiniteRayExtensions (n : ℕ) (f : Charts K) : Prop :=
  HasFiniteRayExtension n (fun (u : Kˣ) (q : Kˣ × K) => (u^n*q.1,u.val^n*q.2))
    (fun q => f.1 q.1 q.2) ∧
  HasFiniteRayExtension n (fun (u : Kˣ) (q : K × Kˣ) => (u.val^n*q.1,u^n*q.2))
    (fun q => f.2 q.1 q.2)

theorem finiteRayExtensions_of_test {K : Type} [NontriviallyNormedField K] [ProperSpace K]
    [IsUltrametricDist K] (hn : n ≠ 0) {f : Charts K} (hf : finiteTest f) : FiniteRayExtensions n f := by
  obtain ⟨C,hC,h0,ho⟩ := hf.2.2
  constructor
  · apply HasFiniteRayExtension.of_test hn Prod.fst Prod.snd continuous_fst continuous_snd
      (by fun_prop) (fun _ _ => rfl) (fun _ _ => rfl) hf.1 hC h0
    rintro ⟨a,b⟩ hq
    simpa [xChart,a.ne_zero] using (ho _ hq).1
  · apply HasFiniteRayExtension.of_test hn Prod.snd Prod.fst continuous_snd continuous_fst
      (by fun_prop) (fun _ _ => rfl) (fun _ _ => rfl) hf.2.1 (hC.image continuous_swap)
      (fun ⟨z,hz,he⟩ => h0 ((show z = 0 from congrArg Prod.swap he) ▸ hz))
    rintro ⟨a,b⟩ hq
    simpa [yChart,b.ne_zero] using (ho (a,b.val) (fun h => hq ⟨_,h,rfl⟩)).2

private theorem finiteRayExtension_of_fourier [WeaklyLocallyCompactSpace P] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (dx : Measure K) [dx.IsAddHaarMeasure]
    {R : P → K → ℂ} (hR : SmoothFiniteFamily R) {ψ : K → ℂ} (hc : IsLocallyConstant ψ)
    (ha : ∀ x y, ψ (x+y) = ψ x * ψ y) (hn : ∃ x, ψ x ≠ 1) (c : ℂ)
    {dil : Kˣ → P → P} {f : P → ℂ}
    (hray : ∀ p (u : Kˣ), (‖u.val‖ : ℂ)^(n-1) * f (dil u p) = c * ∫ t, R p t * ψ (u.val*t) ∂dx) :
    HasFiniteRayExtension n dil f := by
  have h := hR.fourier dx hc ha hn
  refine ⟨fun p u => c * ∫ t, R p t * ψ (u*t) ∂dx,
    smoothFiniteFamily_of_support (h.1.comp (c * ·)) ?_,fun p u => (hray p u).symm⟩
  intro T hT
  obtain ⟨C,hC,ho⟩ := (h.2 T hT).2.1
  exact ⟨C,hC,fun p hp t ht => by simp [ho p hp t ht]⟩

namespace Datum
open NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] [NeZero n] (d : Datum F n)

theorem finiteTest_transform_rayExtensions (p : HeightOneSpectrum (𝓞 F)) {f : Charts (LocalField F (.inr p))}
    (hf : f ∈ d.testSet (.inr p)) : FiniteRayExtensions n (d.integralTransform (.inr p) f) := by
  let v : Place F := .inr p
  let K := LocalField F v
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace (p.adicCompletion F) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  letI : MeasurableSpace (p.adicCompletion F) := borel _
  letI : BorelSpace (p.adicCompletion F) := ⟨rfl⟩
  letI : ProperSpace K := inferInstanceAs (ProperSpace (p.adicCompletion F))
  letI : LocallyCompactSpace K := inferInstanceAs (LocallyCompactSpace (p.adicCompletion F))
  letI : LocallyCompactSpace {x : K // x ≠ 0} :=
    (isOpen_ne_fun continuous_id (continuous_const (y := (0 : K)))).locallyCompactSpace
  letI : LocallyCompactSpace Kˣ := unitsHomeomorphNeZero.isOpenEmbedding.locallyCompactSpace
  let dx : Measure K := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  obtain ⟨hx,hy⟩ := d.smooth_finiteTest_lines p hf
  have hc := d.character.locallyConstant_finiteValue p
  have ha := d.character.localValue_add v
  have hn := d.character.nontrivial_finiteValue p
  constructor
  · exact finiteRayExtension_of_fourier (K := K) (P := Kˣ × K) dx hx hc ha hn _
      (fun q u => (d.transform_pow_ray v f u).1 q.1 q.2)
  · exact finiteRayExtension_of_fourier (K := K) (P := K × Kˣ) dx hy hc ha hn _
      (fun q u => (d.transform_pow_ray v f u).2 q.1 q.2)

/-- The normalized ray of every Schwartz section at a finite place extends
to a Schwartz–Bruhat function, uniformly in compact sets of chart vectors. -/
theorem finite_schwartz_rayExtensions (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p)) :
    FiniteRayExtensions n Φ.val := by
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace (p.adicCompletion F) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  refine Submodule.span_induction (p := fun f _ => FiniteRayExtensions n f) ?_ ?_ ?_ ?_ Φ.property
  · rintro f (hf | ⟨g,hg,rfl⟩)
    · exact finiteRayExtensions_of_test (K := p.adicCompletion F) (NeZero.ne n) hf.2
    · exact d.finiteTest_transform_rayExtensions p hg
  · exact ⟨.zero,.zero⟩
  · rintro f g _ _ ⟨fx,fy⟩ ⟨gx,gy⟩
    exact ⟨fx.add gx,fy.add gy⟩
  · rintro c f _ ⟨fx,fy⟩
    exact ⟨fx.smul c,fy.smul c⟩

end Datum

end MetaplecticPoisson
