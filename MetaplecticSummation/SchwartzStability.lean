import MetaplecticSummation.Cover.Operators
import MetaplecticSummation.FiniteMarginal
import MetaplecticSummation.DiagonalTransform
import MetaplecticSummation.TransformLinearity

/-! Inversion and stability of the full Schwartz space at tame finite places. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open Set Filter MeasureTheory NumberField IsDedekindDomain
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

private theorem integrable_transformTest_axis (p : HeightOneSpectrum (𝓞 F))
    (hpow : ∀ a : (LocalField F (.inr p))ˣ, (∀ u, d.symbol (.inr p) u a = 1) → ∃ b, b^n = a)
    {f : Charts (LocalField F (.inr p))} (hf : f ∈ d.testSet (.inr p)) (b : (LocalField F (.inr p))ˣ) :
    let v : Place F := .inr p
    Integrable (fun t => d.character.localValue F v t *
      (d.radonAt v (d.integralTransform v f) t).2 0 b) (selfDual F d.character v) := by
  let v : Place F := .inr p
  let K := LocalField F v
  let dx := selfDual F d.character v
  letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  letI : NullSingletonClass dx := d.selfDual_nullSingleton v
  let Φ : d.schwartz v := ⟨f,Submodule.subset_span (Or.inl hf)⟩
  let Ψ := d.transformTest v Φ hf
  let ψ := d.character.localValue F v
  obtain ⟨σ,hσ,hu⟩ := d.exists_finite_axis_density p Φ b⁻¹
  obtain ⟨hl,hc⟩ := (show IsLocallyConstant (d.hat v σ) ∧ HasCompactSupport (d.hat v σ) from d.hat_finite_bruhat p hσ)
  have hi : Integrable (fun t => ψ t*d.hat v σ t) dx :=
    ((d.character.continuous_localValue v).mul hl.continuous).integrable_of_hasCompactSupport hc.mul_left
  let c := d.symbol v (-1) b / (modulus F v b.val : ℂ)
  let k := (Real.sqrt (modulus F v (n : K)) : ℂ)⁻¹
  apply (hi.const_mul (c*k)).congr
  filter_upwards [dx.ae_ne 0] with t ht
  let u := Units.mk0 t ht
  change c*k*(ψ u.val*d.hat v σ u.val) = ψ u.val * d.axisLine v Ψ b u.val
  have hm : d.marginal v Ψ (u^n*b⁻¹) = k * d.hat v σ u.val :=
    d.finite_reverse_marginal_with_density p Φ hf b⁻¹ u σ hu hpow
  rw [d.axisLine_unit,div_eq_mul_inv (u^n),hm]
  dsimp only [c,k]
  ring

/-- Absolute convergence of the outer integral on the transformed generators.
The reverse marginal controls the vertical axis and shear covariance moves
that estimate to both charts. -/
theorem transformIntegrable_transformTest (p : HeightOneSpectrum (𝓞 F))
    (hpow : ∀ a : (LocalField F (.inr p))ˣ, (∀ u, d.symbol (.inr p) u a = 1) → ∃ b, b^n = a)
    {f : Charts (LocalField F (.inr p))} (hf : f ∈ d.testSet (.inr p)) :
    d.TransformIntegrable (.inr p) (d.integralTransform (.inr p) f) := by
  let v : Place F := .inr p
  let K := LocalField F v
  let T := d.integralTransform v
  let R := d.radonAt v
  let H := d.symbol v
  let ψ := d.character.localValue F v
  let dx := selfDual F d.character v
  have Y (g : Charts K) (hg : g ∈ d.testSet v) (x : K) (y : Kˣ) :
      Integrable (fun t => ψ t * (R (T g) t).2 x y) dx := by
    let u := x/y.val
    let g' := lowerShear H u g
    have hh := d.integrable_transformTest_axis p hpow (d.finite_shear_test p hg u).2 y
    have he : (T g').2 = (lowerShear H u (T g)).2 :=
      funext fun a => funext (transform_lower H n (modulus F v) dx ψ u g a)
    apply hh.congr
    filter_upwards with t
    have h := (congrArg (fun S => (R ((T g).1,S) t).2 0 y) he).trans
      (radon_lower H n (modulus F v) dx u t (T g) 0 y)
    change ψ t * (R (T g') t).2 0 y = _
    rw [show (R (T g') t).2 0 y = (R (T g) t).2 (0+u*y.val) y from h,zero_add,
      show u*y.val = x from div_mul_cancel₀ x y.ne_zero]
  have X (g : Charts K) (hg : g ∈ d.testSet v) (x y : Kˣ) :
      Integrable (fun t => ψ t * (R (T g) t).1 x y.val) dx := by
    apply ((Y g hg x.val y).const_mul (H x y)).congr
    filter_upwards with t
    have h := d.radon_glues v (d.integralTransform_glues v hg.1) t x y
    change _ = ψ t * (R (T g) t).1 x y.val
    rw [show (R (T g) t).1 x y.val = H x y * (R (T g) t).2 x.val y from h]
    ring
  refine ⟨?_, Y f hf⟩
  intro x y
  by_cases hy : y ≠ 0
  · exact X f hf x (Units.mk0 y hy)
  · obtain rfl := not_ne_iff.mp hy
    let g := upperShear H (-1) f
    have he : (T g).1 = (upperShear H (-1) (T f)).1 :=
      funext fun a => funext (transform_upper H n (modulus F v) dx ψ (-1) f a)
    apply (X g (d.finite_shear_test p hf (-1)).1 x x).congr
    filter_upwards with t
    have h := (congrArg (fun S => (R (S,(T f).2) t).1 x x.val) he).trans
      (radon_upper H n (modulus F v) dx (-1) t (T f) x x.val)
    change ψ t * (R (T g) t).1 x x.val = ψ t * (R (T f) t).1 x 0
    rw [show (R (T g) t).1 x x.val = (R (T f) t).1 x (x.val + -1*x.val) from h,neg_one_mul,add_neg_cancel]

/-- For each Schwartz section the two outer chart integrals converge
absolutely. At wild places the only extra hypothesis is Hilbert nondegeneracy. -/
theorem finite_transformIntegrable (p : HeightOneSpectrum (𝓞 F))
    (hpow : ∀ a : (LocalField F (.inr p))ˣ, (∀ u, d.symbol (.inr p) u a = 1) → ∃ b, b^n = a)
    (Φ : d.schwartz (.inr p)) : d.TransformIntegrable (.inr p) Φ.val := by
  let v : Place F := .inr p
  refine Submodule.span_induction (p := fun f _ => d.TransformIntegrable v f) ?_ ?_ ?_ ?_ Φ.property
  · rintro f (hf | ⟨g,hg,rfl⟩)
    · obtain ⟨hx,hy⟩ := d.integrable_finiteTest_transform p hf
      exact ⟨fun a b => hx (a,b),fun a b => hy (a,b)⟩
    · exact d.transformIntegrable_transformTest p hpow hg
  · constructor <;> intro a b <;> simp [radonAt,radon]
  · intro f g hf hg fi gi
    exact (d.finite_transform_add p ⟨f,hf⟩ ⟨g,hg⟩ fi gi).1
  · intro c f _ fi
    exact fi.smul d _ c

/-- The defining integral, first as a linear map with unrestricted chart values. -/
private def transformToCharts (p : HeightOneSpectrum (𝓞 F))
    (hpow : ∀ a : (LocalField F (.inr p))ˣ, (∀ u, d.symbol (.inr p) u a = 1) → ∃ b, b^n = a) :
    d.schwartz (.inr p) →ₗ[ℂ] Charts (LocalField F (.inr p)) where
  toFun Φ := d.integralTransform (.inr p) Φ.val
  map_add' Φ Ψ := (d.finite_transform_add p Φ Ψ (d.finite_transformIntegrable p hpow Φ)
    (d.finite_transformIntegrable p hpow Ψ)).2
  map_smul' c Φ := d.integralTransform_smul _ c Φ.val

private theorem schwartz_generators_span (v : Place F) :
    Submodule.span ℂ ((Subtype.val : d.schwartz v → _) ⁻¹'
      (d.testSet v ∪ d.integralTransform v '' d.testSet v)) = ⊤ :=
  Submodule.span_span_coe_preimage

/-- The integral transform preserves the span of test sections and their
transforms, since the second transform of a test section is a diagonal translate. -/
def finiteSchwartzTransform (p : HeightOneSpectrum (𝓞 F))
    (hpow : ∀ a : (LocalField F (.inr p))ˣ, (∀ u, d.symbol (.inr p) u a = 1) → ∃ b, b^n = a) :
    d.schwartz (.inr p) →ₗ[ℂ] d.schwartz (.inr p) := by
  let v : Place F := .inr p
  let T := d.transformToCharts p hpow
  apply T.codRestrict (d.schwartz v)
  intro Φ
  suffices h : ⊤ ≤ (d.schwartz v).comap T from h Submodule.mem_top
  rw [← d.schwartz_generators_span v,Submodule.span_le]
  rintro ⟨f,hf⟩ (ht | ⟨g,hg,rfl⟩)
  · exact Submodule.subset_span (Or.inr ⟨f,ht,rfl⟩)
  · change d.integralTransform v (d.integralTransform v g) ∈ d.schwartz v
    rw [d.finite_integralTransform_square_on_test p hpow hg]
    exact Submodule.subset_span (Or.inl (d.torusCharts_finiteTest p _ hg))

theorem finiteSchwartzTransform_square (p : HeightOneSpectrum (𝓞 F))
    (hpow : ∀ a : (LocalField F (.inr p))ˣ, (∀ u, d.symbol (.inr p) u a = 1) → ∃ b, b^n = a)
    (Φ : d.schwartz (.inr p)) :
    let v : Place F := .inr p
    let L := d.finiteSchwartzTransform p hpow
    (L (L Φ)).val = d.torusCharts v ((-1)^(n+1)) Φ.val := by
  let v : Place F := .inr p
  let e : (LocalField F v)ˣ := (-1)^(n+1)
  let T := d.integralTransform v
  let L := d.finiteSchwartzTransform p hpow
  let A := (d.schwartz v).subtype.comp (L.comp L)
  let B := (d.torusLinear v e).comp (d.schwartz v).subtype
  suffices h : A = B from DFunLike.congr_fun h Φ
  apply LinearMap.ext_on (d.schwartz_generators_span v)
  rintro ⟨f,hf⟩ (ht | ⟨g,hg,rfl⟩)
  · exact d.finite_integralTransform_square_on_test p hpow ht
  · change T (T (T g)) = d.torusCharts v e (T g)
    have hs : T (T g) = d.torusCharts v e g := d.finite_integralTransform_square_on_test p hpow hg
    rw [hs]
    exact d.integralTransform_torusCharts v e g

/-- Theorem 7.1(i) at every tame finite place. The linear equivalence agrees
pointwise with the two explicit chart integrals of Definition 4.4. -/
theorem tame_schwartz_inversion (p : HeightOneSpectrum (𝓞 F)) (hp : p.asIdeal.absNorm.Coprime n) :
    let v : Place F := .inr p
    ∃ L : d.schwartz v ≃ₗ[ℂ] d.schwartz v,
      (∀ Φ, (L Φ).val = d.integralTransform v Φ.val) ∧
      ∀ Φ, (L (L Φ)).val = d.torusCharts v ((-1)^(n+1)) Φ.val := by
  let v : Place F := .inr p
  have hpow (a : (LocalField F v)ˣ) := (d.tame_symbol_radical p hp a).mp
  let L := d.finiteSchwartzTransform p hpow
  have hs := d.finiteSchwartzTransform_square p hpow
  exact ⟨LinearEquiv.ofBijective L (d.bijective_of_torus_square v L hs),fun _ => rfl,hs⟩

/-- The integral automorphism at a tame place commutes with the local cover
action of §5, as in Theorem 7.1(ii). -/
theorem tame_transform_equivariant (p : HeightOneSpectrum (𝓞 F)) (hp : p.asIdeal.absNorm.Coprime n)
    (g : d.cover (.inr p)) (Φ : d.schwartz (.inr p)) :
    let L := d.finiteSchwartzTransform p (fun a => (d.tame_symbol_radical p hp a).mp)
    L (g.val Φ) = g.val (L Φ) :=
  d.integralTransform_equivariant _ _ (fun _ => rfl) g Φ

end MetaplecticPoisson.Datum
