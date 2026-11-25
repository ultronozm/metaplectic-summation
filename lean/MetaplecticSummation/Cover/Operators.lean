import MetaplecticSummation.Schwartz.Local
import MetaplecticSummation.Marginals.Basic
import MetaplecticSummation.ArchimedeanShears
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain Filter MeasureTheory
open scoped Topology Matrix ENNReal
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (v : Place F)
abbrev Operators := d.schwartz v ≃ₗ[ℂ] d.schwartz v

def IsUpper (u : LocalField F v) (g : d.Operators v) : Prop :=
  ∀ Φ, (∀ x y, (g Φ).val.1 x y = Φ.val.1 x (y + u * x)) ∧
    ∀ y, (g Φ).val.2 0 y = Φ.val.2 0 y

def IsLower (u : LocalField F v) (g : d.Operators v) : Prop :=
  ∀ Φ, (∀ x y, (g Φ).val.2 x y = Φ.val.2 (x + u * y) y) ∧
    ∀ x, (g Φ).val.1 x 0 = Φ.val.1 x 0

def IsCentralScalar (g : d.Operators v) : Prop :=
  ∃ z : Mu F n, ∀ Φ, g Φ = ((d.embedding z : ℂˣ) : ℂ) • Φ

/-- The image of the local cover acting on Schwartz functions, generated as in §5. -/
def cover : Subgroup (d.Operators v) := Subgroup.closure
  {g | d.IsCentralScalar v g ∨ (∃ u, d.IsUpper v u g) ∨ ∃ u, d.IsLower v u g}

/-- Translation on the primary chart and the value on the missing axis
determine the full shear of a genuine section. -/
theorem eq_upperShear {f g : Charts (LocalField F v)} (hg : Glues (d.symbol v) g)
    (u : LocalField F v) (hx : ∀ x y, g.1 x y = f.1 x (y+u*x.val))
    (hy : ∀ y, g.2 0 y = f.2 0 y) : g = upperShear (d.symbol v) u f := by
  apply Prod.ext (funext fun x => funext (hx x))
  funext x y
  by_cases h : x ≠ 0
  · let X := Units.mk0 x h
    simp only [upperShear,dif_pos h]
    apply (eq_div_iff (d.unitPairing v X y).ne_zero).mpr
    exact (mul_comm ..).trans ((hg X y).symm.trans (hx X y.val))
  · obtain rfl := not_ne_iff.mp h
    simpa only [upperShear,dif_neg (not_ne_iff.mpr rfl)] using hy y

theorem eq_lowerShear {f g : Charts (LocalField F v)} (hg : Glues (d.symbol v) g)
    (u : LocalField F v) (hy : ∀ x y, g.2 x y = f.2 (x+u*y.val) y)
    (hx : ∀ x, g.1 x 0 = f.1 x 0) : g = lowerShear (d.symbol v) u f := by
  apply Prod.ext _ (funext fun x => funext (hy x))
  funext x y
  by_cases h : y ≠ 0
  · let Y := Units.mk0 y h
    simp only [lowerShear,dif_pos h]
    exact (hg x Y).trans (congrArg (d.symbol v x Y * ·) (hy x.val Y))
  · obtain rfl := not_ne_iff.mp h
    simpa only [lowerShear,dif_neg (not_ne_iff.mpr rfl)] using hx x

/-- Lower shears preserve the Fourier transform on the horizontal axis.
At nonzero line parameter the two symbol factors multiply to {z,tⁿ} = 1. -/
private theorem horizontalLine_unit (Φ : d.schwartz v) (x t : (LocalField F v)ˣ) :
    (radon n (d.symbol v) (modulus F v) (selfDual F d.character v) Φ.val t.val).1 x 0 =
      (∫ z, Φ.val.2 z (-(t^n)/x) ∂(selfDual F d.character v)) / (modulus F v x : ℂ) := by
  let dx := selfDual F d.character v
  letI : NullSingletonClass dx := d.selfDual_nullSingleton v
  simp only [radon, mul_zero, zero_sub]
  congr 1
  apply integral_congr_ae
  filter_upwards [dx.ae_ne 0] with z hz
  let Z := Units.mk0 z hz
  let Y := -(t^n)/x
  have hs : d.symbol v Z Y * d.symbol v Z (-x) = 1 := by
    change ((d.unitPairing v Z Y).val * (d.unitPairing v Z (-x)).val) = 1
    rw [← Units.val_mul,← map_mul,show Y * (-x) = t^n by simp [Y],map_pow,d.unitPairing_pow,Units.val_one]
  have hg := (d.schwartz_glues v Φ) Z Y
  change Φ.val.1 Z Y.val = d.symbol v Z Y * Φ.val.2 z Y at hg
  simp only [Y,Units.val_div_eq_div_val,Units.val_neg,Units.val_pow_eq_pow_val] at hg
  rw [dif_pos hz]
  change Φ.val.1 Z _ * d.symbol v Z (-x) = Φ.val.2 z Y
  rw [hg]
  change d.symbol v Z Y * Φ.val.2 z Y * d.symbol v Z (-x) = Φ.val.2 z Y
  rw [mul_right_comm,hs,one_mul]

theorem integralTransform_upper_of_charts (u : LocalField F v) (Φ Ψ : d.schwartz v)
    (hx : ∀ x y, Ψ.val.1 x y = Φ.val.1 x (y + u*x.val)) :
    d.integralTransform v Ψ.val = upperShear (d.symbol v) u (d.integralTransform v Φ.val) := by
  apply d.eq_upperShear v (d.integralTransform_glues v (d.schwartz_glues v Ψ)) u
  · intro a b
    have he : Ψ.val.1 = (upperShear (d.symbol v) u Φ.val).1 := funext fun x => funext (hx x)
    exact (congrArg (fun X => (d.integralTransform v (X,Φ.val.2)).1 a b) he).trans
      (transform_upper (d.symbol v) n (modulus F v) (selfDual F d.character v) (d.character.localValue F v) u Φ.val a b)
  · intro y
    let dx := selfDual F d.character v
    letI : NullSingletonClass dx := d.selfDual_nullSingleton v
    simp only [integralTransform,transform]
    congr 1
    apply integral_congr_ae
    filter_upwards [dx.ae_ne 0] with t ht
    let T := Units.mk0 t ht
    change _ * d.axisLine v Ψ y T.val = _ * d.axisLine v Φ y T.val
    rw [d.axisLine_unit,d.axisLine_unit]
    congr 2
    unfold marginal
    simp_rw [hx]
    letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
    exact integral_add_right_eq_self (μ := dx) _ _

private theorem transform_upper (L : d.schwartz v →ₗ[ℂ] d.schwartz v)
    (hL : ∀ f, (L f).val = d.integralTransform v f.val)
    (u : LocalField F v) {g : d.Operators v} (hg : d.IsUpper v u g) (Φ : d.schwartz v) :
    L (g Φ) = g (L Φ) := by
  apply Subtype.ext
  rw [hL,d.integralTransform_upper_of_charts v u Φ (g Φ) (hg Φ).1]
  have he := d.eq_upperShear v (d.schwartz_glues v (g (L Φ))) u
    (hg (L Φ)).1 (hg (L Φ)).2
  rw [hL] at he
  exact he.symm

theorem fourier_upper (u : LocalField F v) {g : d.Operators v} (hg : d.IsUpper v u g) (Φ : d.schwartz v) :
    d.fourier v (g Φ) = g (d.fourier v Φ) :=
  d.transform_upper v _ (d.fourier_apply v) u hg Φ

theorem integralTransform_lower_of_charts (u : LocalField F v) (Φ Ψ : d.schwartz v)
    (hy : ∀ x y, Ψ.val.2 x y = Φ.val.2 (x + u*y.val) y) :
    d.integralTransform v Ψ.val = lowerShear (d.symbol v) u (d.integralTransform v Φ.val) := by
  apply d.eq_lowerShear v (d.integralTransform_glues v (d.schwartz_glues v Ψ)) u
  · intro a b
    have he : Ψ.val.2 = (lowerShear (d.symbol v) u Φ.val).2 := funext fun x => funext (hy x)
    exact (congrArg (fun Y => (d.integralTransform v (Φ.val.1,Y)).2 a b) he).trans
      (transform_lower (d.symbol v) n (modulus F v) (selfDual F d.character v) (d.character.localValue F v) u Φ.val a b)
  · intro x
    let dx := selfDual F d.character v
    letI : NullSingletonClass dx := d.selfDual_nullSingleton v
    simp only [integralTransform,transform]
    congr 1
    apply integral_congr_ae
    filter_upwards [dx.ae_ne 0] with t ht
    let T := Units.mk0 t ht
    have e := d.horizontalLine_unit v Ψ x T
    have e' := d.horizontalLine_unit v Φ x T
    change _ * (radon n (d.symbol v) (modulus F v) dx Ψ.val T.val).1 x 0 =
      _ * (radon n (d.symbol v) (modulus F v) dx Φ.val T.val).1 x 0
    rw [e,e']
    simp_rw [hy]
    letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
    let Y := -(T^n)/x
    exact congrArg (fun z : ℂ => d.character.localValue F v t * (z / (modulus F v x : ℂ)))
      (integral_add_right_eq_self (μ := dx) (fun z => Φ.val.2 z Y) (u*Y.val))

private theorem transform_lower (L : d.schwartz v →ₗ[ℂ] d.schwartz v)
    (hL : ∀ f, (L f).val = d.integralTransform v f.val)
    (u : LocalField F v) {g : d.Operators v} (hg : d.IsLower v u g) (Φ : d.schwartz v) :
    L (g Φ) = g (L Φ) := by
  apply Subtype.ext
  rw [hL,d.integralTransform_lower_of_charts v u Φ (g Φ) (hg Φ).1]
  have he := d.eq_lowerShear v (d.schwartz_glues v (g (L Φ))) u
    (hg (L Φ)).1 (hg (L Φ)).2
  rw [hL] at he
  exact he.symm

theorem fourier_lower (u : LocalField F v) {g : d.Operators v} (hg : d.IsLower v u g) (Φ : d.schwartz v) :
    d.fourier v (g Φ) = g (d.fourier v Φ) :=
  d.transform_lower v _ (d.fourier_apply v) u hg Φ

/-- A shear preserving tests extends to the Schwartz space by covariance on
the transformed generators. Its inverse is the shear with opposite parameter. -/
private def shearEquiv
    (S : LocalField F v → Charts (LocalField F v) →ₗ[ℂ] Charts (LocalField F v))
    (hD : ∀ u f, f ∈ d.testSet v → S u f ∈ d.testSet v)
    (hT : ∀ u f, f ∈ d.testSet v → S u (d.integralTransform v f) = d.integralTransform v (S u f))
    (hinv : ∀ u (Φ : d.schwartz v), S (-u) (S u Φ.val) = Φ.val) (u : LocalField F v) :
    d.Operators v := by
  have stable (w : LocalField F v) : d.schwartz v ≤ (d.schwartz v).comap (S w) := by
    apply Submodule.span_le.mpr
    rintro f (hf | ⟨g,hg,rfl⟩)
    · exact Submodule.subset_span (Or.inl (hD w f hf))
    · change S w (d.integralTransform v g) ∈ d.schwartz v
      rw [hT w g hg]
      exact Submodule.subset_span (Or.inr ⟨S w g,hD w g hg,rfl⟩)
  let L (w : LocalField F v) : d.schwartz v →ₗ[ℂ] d.schwartz v :=
    (S w).restrict (fun _ hx => stable w hx)
  apply LinearEquiv.ofLinear (L u) (L (-u))
  · ext Φ : 1
    apply Subtype.ext
    change S u (S (-u) Φ.val) = Φ.val
    simpa only [neg_neg] using hinv (-u) Φ
  · ext Φ : 1
    apply Subtype.ext
    exact hinv u Φ

theorem exists_upper_of_test
    (ht : ∀ u f, f ∈ d.testSet v → upperShear (d.symbol v) u f ∈ d.testSet v) (u : LocalField F v) :
    ∃! g, d.IsUpper v u g := by
  let S := upperShearLinear (d.symbol v)
  have cov (w : LocalField F v) (f) (hf : f ∈ d.testSet v) :
      S w (d.integralTransform v f) = d.integralTransform v (S w f) := by
    let Φ : d.schwartz v := ⟨f,Submodule.subset_span (Or.inl hf)⟩
    let Ψ : d.schwartz v := ⟨S w f,Submodule.subset_span (Or.inl (ht w f hf))⟩
    exact (d.integralTransform_upper_of_charts v w Φ Ψ (fun _ _ => rfl)).symm
  have inv (w : LocalField F v) (Φ : d.schwartz v) : S (-w) (S w Φ.val) = Φ.val :=
    (upperShear_add _ _ _ _).trans (by
      rw [neg_add_cancel]
      exact upperShear_zero _ (fun x y => (d.unitPairing v x y).ne_zero) (d.schwartz_glues v Φ))
  let g := d.shearEquiv v S ht cov inv u
  refine ⟨g,fun Φ => ⟨fun _ _ => rfl,fun y => ?_⟩,?_⟩
  · change (upperShear (d.symbol v) u Φ.val).2 0 y = _
    simp [upperShear]
  · intro h hh
    ext Φ : 1
    exact Subtype.ext (d.eq_upperShear v (d.schwartz_glues v (h Φ)) u (hh Φ).1 (hh Φ).2)

theorem exists_lower_of_test
    (ht : ∀ u f, f ∈ d.testSet v → lowerShear (d.symbol v) u f ∈ d.testSet v) (u : LocalField F v) :
    ∃! g, d.IsLower v u g := by
  let S := lowerShearLinear (d.symbol v)
  have cov (w : LocalField F v) (f) (hf : f ∈ d.testSet v) :
      S w (d.integralTransform v f) = d.integralTransform v (S w f) := by
    let Φ : d.schwartz v := ⟨f,Submodule.subset_span (Or.inl hf)⟩
    let Ψ : d.schwartz v := ⟨S w f,Submodule.subset_span (Or.inl (ht w f hf))⟩
    exact (d.integralTransform_lower_of_charts v w Φ Ψ (fun _ _ => rfl)).symm
  have inv (w : LocalField F v) (Φ : d.schwartz v) : S (-w) (S w Φ.val) = Φ.val :=
    (lowerShear_add _ _ _ _).trans (by rw [neg_add_cancel]; exact lowerShear_zero _ (d.schwartz_glues v Φ))
  let g := d.shearEquiv v S ht cov inv u
  refine ⟨g,fun Φ => ⟨fun _ _ => rfl,fun x => ?_⟩,?_⟩
  · change (lowerShear (d.symbol v) u Φ.val).1 x 0 = _
    simp [lowerShear]
  · intro h hh
    ext Φ : 1
    exact Subtype.ext (d.eq_lowerShear v (d.schwartz_glues v (h Φ)) u (hh Φ).1 (hh Φ).2)

theorem exists_upper (u : LocalField F v) : ∃! g, d.IsUpper v u g := by
  apply d.exists_upper_of_test
  intro w f hf
  cases v with
  | inl q => exact (d.arch_shear_test q hf w).1
  | inr p => exact (d.finite_shear_test p hf w).1

theorem exists_lower (u : LocalField F v) : ∃! g, d.IsLower v u g := by
  apply d.exists_lower_of_test
  intro w f hf
  cases v with
  | inl q => exact (d.arch_shear_test q hf w).2
  | inr p => exact (d.finite_shear_test p hf w).2

/-- The two integral formulas force any Schwartz endomorphism realizing them
to commute with the subgroup generated by the shears and central scalars. -/
theorem integralTransform_equivariant (L : d.schwartz v →ₗ[ℂ] d.schwartz v)
    (hL : ∀ f, (L f).val = d.integralTransform v f.val)
    (g : d.cover v) (Φ : d.schwartz v) :
    L (g.val Φ) = g.val (L Φ) := by
  let P (s : d.Operators v) := ∀ f, L (s f) = s (L f)
  suffices P g.val from this Φ
  refine Subgroup.closure_induction (p := fun s _ => P s) ?_ (fun _ => rfl) ?_ ?_ g.property
  · rintro s (⟨z,hz⟩ | ⟨u,hu⟩ | ⟨u,hu⟩)
    · intro f
      rw [hz,hz,map_smul]
    · exact d.transform_upper v L hL u hu
    · exact d.transform_lower v L hL u hu
  · intro s t _ _ hs ht f
    exact (hs (t f)).trans (congrArg s (ht f))
  · intro s _ hs f
    apply s.injective
    change s (L (s.symm f)) = s (s.symm (L f))
    rw [LinearEquiv.apply_symm_apply]
    simpa only [LinearEquiv.apply_symm_apply] using (hs (s.symm f)).symm

theorem fourier_equivariant (g : d.cover v) (Φ : d.schwartz v) :
    d.fourier v (g.val Φ) = g.val (d.fourier v Φ) :=
  d.integralTransform_equivariant v _ (d.fourier_apply v) g Φ

end MetaplecticPoisson.Datum
