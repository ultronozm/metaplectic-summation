import MetaplecticSummation.FiniteTransform
import MetaplecticSummation.RayFourier

/-! Construction of the leading term at a finite place from normalized
ray limits, including the Radon integral formula of §8. -/

noncomputable section
namespace MetaplecticPoisson
open MeasureTheory Filter Set
open scoped Topology
variable {K : Type*} [Field K] [TopologicalSpace K] {n : ℕ} {m : K → ℝ}

namespace IsLeadingTerm
variable {f g f' g' : Charts K}

protected theorem add (hf : IsLeadingTerm n m f g) (hf' : IsLeadingTerm n m f' g') :
    IsLeadingTerm n m (f+f') (g+g') := by
  constructor
  · intro x y
    simpa only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add] using (hf.1 x y).add (hf'.1 x y)
  · intro x y
    simpa only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add] using (hf.2 x y).add (hf'.2 x y)

protected theorem smul (hf : IsLeadingTerm n m f g) (c : ℂ) : IsLeadingTerm n m (c • f) (c • g) := by
  constructor
  · intro x y
    convert (hf.1 x y).const_mul c using 1 <;> try rfl
    funext u
    change _ * (c * _) = c * (_ * _); ring
  · intro x y
    convert (hf.2 x y).const_mul c using 1 <;> try rfl
    funext u
    change _ * (c * _) = c * (_ * _); ring

protected theorem zero : IsLeadingTerm n m (0 : Charts K) 0 := by
  constructor <;> intro x y <;> simpa using (tendsto_const_nhds (x := (0:ℂ)))

theorem unique [NeBot (comap (fun u : Kˣ => u.val) (𝓝 0))]
    (hf : IsLeadingTerm n m f g) (hf' : IsLeadingTerm n m f g') : g = g' := by
  ext x y
  · exact tendsto_nhds_unique (hf.1 x y) (hf'.1 x y)
  · exact tendsto_nhds_unique (hf.2 x y) (hf'.2 x y)

end IsLeadingTerm

theorem units_neBot_at_zero {L : Type*} [NontriviallyNormedField L] :
    NeBot (comap (fun u : Lˣ => u.val) (𝓝 0)) := by
  apply comap_neBot_iff.mpr
  intro U hU
  have h := inter_mem (mem_nhdsWithin_of_mem_nhds hU) (self_mem_nhdsWithin (a := (0:L)) (s := {0}ᶜ))
  obtain ⟨x, hx, hx₀⟩ := Filter.nonempty_of_mem (f := 𝓝[≠] (0:L)) h
  exact ⟨Units.mk0 x hx₀,hx⟩

theorem finiteTest_zero_leading {L : Type} [NormedField L] (n : ℕ) (hn : n ≠ 0)
    (m : L → ℝ) {f : Charts L} (hf : finiteTest f) : IsLeadingTerm n m f 0 := by
  obtain ⟨C,hC,h0,hs⟩ := hf.2.2
  let l := comap (fun u : Lˣ => u.val) (𝓝 0)
  have hpow : Tendsto (fun u : Lˣ => u.val^n) l (𝓝 0) := by
    simpa only [zero_pow hn] using
      (tendsto_comap (f := fun u : Lˣ => u.val) (x := 𝓝 0)).pow n
  have ho (a b : L) : ∀ᶠ u in l, (u.val^n*a,u.val^n*b) ∉ C := by
    have he : Tendsto (fun u : Lˣ => (u.val^n*a,u.val^n*b)) l (𝓝 (0,0)) := by
      simpa only [zero_mul] using (hpow.mul_const a).prodMk_nhds (hpow.mul_const b)
    exact he.eventually (hC.isClosed.isOpen_compl.mem_nhds h0)
  constructor
  · intro a b
    apply tendsto_const_nhds.congr'
    filter_upwards [ho a.val b] with u hu
    have he := (hs _ hu).1
    simp only [xChart, mul_ne_zero (pow_ne_zero _ u.ne_zero) a.ne_zero, ne_eq, not_false_eq_true,
      dif_pos] at he
    change 0 = _ * f.1 (u^n*a) (u.val^n*b)
    rw [show f.1 (u^n*a) (u.val^n*b) = 0 from by
      convert he using 2
      exact Units.ext rfl, mul_zero]
  · intro a b
    apply tendsto_const_nhds.congr'
    filter_upwards [ho a b.val] with u hu
    have he := (hs _ hu).2
    simp only [yChart, mul_ne_zero (pow_ne_zero _ u.ne_zero) b.ne_zero, ne_eq, not_false_eq_true,
      dif_pos] at he
    change 0 = _ * f.2 (u.val^n*a) (u^n*b)
    rw [show f.2 (u.val^n*a) (u^n*b) = 0 from by
      convert he using 2
      exact Units.ext rfl, mul_zero]

namespace Datum
open NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] [NeZero n] (d : Datum F n)

/-- The right-hand side of the leading-term formula for the Fourier transform
of a test section in §8. -/
def radonLeading (v : Place F) (f : Charts (LocalField F v)) : Charts (LocalField F v) :=
  let dx := selfDual F d.character v
  let R := radon n (d.symbol v) (modulus F v) dx f
  let c : ℂ := (Real.sqrt (modulus F v (n : LocalField F v)))⁻¹
  (fun a b => c * ∫ t, (R t).1 a b ∂dx, fun a b => c * ∫ t, (R t).2 a b ∂dx)

/-- Evaluation at zero of the one-dimensional Fourier integral on each ray. -/
theorem isLeadingTerm_integralTransform (v : Place F) (f : Charts (LocalField F v))
    (hi : let dx := selfDual F d.character v
          let R := radon n (d.symbol v) (modulus F v) dx f
          (∀ a b, Integrable (fun t => (R t).1 a b) dx) ∧
          (∀ a b, Integrable (fun t => (R t).2 a b) dx)) :
    IsLeadingTerm n (modulus F v) (d.integralTransform v f) (d.radonLeading v f) := by
  let dx := selfDual F d.character v
  let ψ := d.character.localValue F v
  let c : ℂ := (Real.sqrt (modulus F v (n : LocalField F v)))⁻¹
  have ht {g : LocalField F v → ℂ} (hg : Integrable g dx) :
      Tendsto (fun u : (LocalField F v)ˣ => c * ∫ t, g t * ψ (u.val*t) ∂dx)
        (comap Units.val (𝓝 0)) (𝓝 (c * ∫ t, g t ∂dx)) := by
    have hc : Continuous (fun z : LocalField F v => ∫ t, g t * ψ (z*t) ∂dx) := by
      apply continuous_of_dominated (bound := fun t => ‖g t‖)
      · intro z
        exact hg.aestronglyMeasurable.mul (((d.character.continuous_localValue v).comp
          (continuous_const.mul continuous_id)).aestronglyMeasurable)
      · intro z
        filter_upwards with t
        simp [ψ]
      · exact hg.norm
      · filter_upwards with t
        exact continuous_const.mul ((d.character.continuous_localValue v).comp
          (continuous_id.mul continuous_const))
    have he := (hc.tendsto 0).comp (tendsto_comap (f := fun u : (LocalField F v)ˣ => u.val))
    simpa only [Function.comp_apply, zero_mul, ψ, Character.localValue_zero, mul_one] using he.const_mul c
  constructor
  · intro a b
    exact (ht (hi.1 a b)).congr (fun u => ((d.transform_pow_ray v f u).1 a b).symm)
  · intro a b
    exact (ht (hi.2 a b)).congr (fun u => ((d.transform_pow_ray v f u).2 a b).symm)

theorem finiteTest_transform_leading (p : HeightOneSpectrum (𝓞 F)) {f : Charts (LocalField F (.inr p))}
    (hf : f ∈ d.testSet (.inr p)) : IsLeadingTerm n (modulus F (.inr p))
      (d.integralTransform (.inr p) f) (d.radonLeading (.inr p) f) := by
  let v : Place F := .inr p
  let dx := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  obtain ⟨hx,hy⟩ := d.smooth_finiteTest_lines p hf
  apply d.isLeadingTerm_integralTransform
  constructor
  · intro a b
    simpa using hx.integrable_weight dx (continuous_const (y := (1:ℂ))) (a,b)
  · intro a b
    simpa using hy.integrable_weight dx (continuous_const (y := (1:ℂ))) (a,b)

theorem exists_leading_finite (p : HeightOneSpectrum (𝓞 F)) :
    let v : Place F := .inr p
    ∃ b : d.schwartz v →ₗ[ℂ] Charts (LocalField F v), ∀ f : d.schwartz v,
      IsLeadingTerm n (modulus F v) f (b f) := by
  let v : Place F := .inr p
  letI : NontriviallyNormedField (LocalField F v) := FinitePlace.nontriviallyNormedCompletion p
  letI : NeBot (comap (fun u : (LocalField F v)ˣ => u.val) (𝓝 0)) := units_neBot_at_zero
  have hex (Φ : d.schwartz v) : ∃ g, IsLeadingTerm n (modulus F v) Φ.val g := by
    refine Submodule.span_induction (p := fun f _ => ∃ g, IsLeadingTerm n (modulus F v) f g)
      ?_ ?_ ?_ ?_ Φ.property
    · rintro f (hf | ⟨g,hg,rfl⟩)
      · exact ⟨0,finiteTest_zero_leading n (NeZero.ne n) _ (show finiteTest f from hf.2)⟩
      · exact ⟨_,d.finiteTest_transform_leading p hg⟩
    · exact ⟨0,IsLeadingTerm.zero⟩
    · rintro f g _ _ ⟨a,ha⟩ ⟨b,hb⟩
      exact ⟨a+b,ha.add hb⟩
    · rintro c f _ ⟨a,ha⟩
      exact ⟨c • a,ha.smul c⟩
  choose b hb using hex
  exact ⟨{ toFun := b
           map_add' := fun x y => (hb (x+y)).unique ((hb x).add (hb y))
           map_smul' := fun c x => (hb (c • x)).unique ((hb x).smul c) }, hb⟩

end Datum
end MetaplecticPoisson
