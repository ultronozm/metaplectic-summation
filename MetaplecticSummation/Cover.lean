import MetaplecticSummation.Marginals
import MetaplecticSummation.Shears
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

theorem exists_upper (u : LocalField F v) : ∃! g, d.IsUpper v u g := by sorry
theorem exists_lower (u : LocalField F v) : ∃! g, d.IsLower v u g := by sorry

def IsCentralScalar (g : d.Operators v) : Prop :=
  ∃ z : Mu F n, ∀ Φ, g Φ = ((d.embedding z : ℂˣ) : ℂ) • Φ

/-- The image of the local cover acting on Schwartz functions, generated as in §5. -/
def cover : Subgroup (d.Operators v) := Subgroup.closure
  {g | d.IsCentralScalar v g ∨ (∃ u, d.IsUpper v u g) ∨ ∃ u, d.IsLower v u g}

theorem kubota_projection :
    ∃ π : d.cover v →* Matrix.SpecialLinearGroup (Fin 2) (LocalField F v),
      Function.Surjective π ∧
      (∀ g, π g = 1 ↔ d.IsCentralScalar v g.val) ∧
      (∀ g u, d.IsUpper v u g.val → (π g).val = !![1,u;0,1]) ∧
      (∀ g u, d.IsLower v u g.val → (π g).val = !![1,0;u,1]) := by sorry

private theorem section_eq_of_X (Φ Ψ : d.schwartz v) (hx : Φ.val.1 = Ψ.val.1)
    (hy : ∀ y, Φ.val.2 0 y = Ψ.val.2 0 y) : Φ = Ψ := by
  apply Subtype.ext
  apply Prod.ext hx
  funext x y
  by_cases h : x = 0
  · exact h ▸ hy y
  let X := Units.mk0 x h
  apply mul_left_cancel₀ ((d.unitPairing v X y).ne_zero : d.symbol v X y ≠ 0)
  exact ((d.schwartz_glues v Φ) X y).symm.trans ((congrFun (congrFun hx X) y).trans ((d.schwartz_glues v Ψ) X y))

private theorem section_eq_of_Y (Φ Ψ : d.schwartz v) (hy : Φ.val.2 = Ψ.val.2)
    (hx : ∀ x, Φ.val.1 x 0 = Ψ.val.1 x 0) : Φ = Ψ := by
  apply Subtype.ext
  apply Prod.ext _ hy
  funext x y
  by_cases h : y = 0
  · exact h ▸ hx x
  let Y := Units.mk0 y h
  have he := congrFun (congrFun hy x.val) Y
  exact ((d.schwartz_glues v Φ) x Y).trans ((congrArg (d.symbol v x Y * ·) he).trans ((d.schwartz_glues v Ψ) x Y).symm)

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

theorem fourier_upper (u : LocalField F v) {g : d.Operators v} (hg : d.IsUpper v u g) (Φ : d.schwartz v) :
    d.fourier v (g Φ) = g (d.fourier v Φ) := by
  apply d.section_eq_of_X
  · funext a b
    rw [(hg (d.fourier v Φ)).1,d.fourier_apply,d.fourier_apply]
    have he : (g Φ).val.1 = (upperShear (d.symbol v) u Φ.val).1 := funext fun x => funext ((hg Φ).1 x)
    exact (congrArg (fun X => (d.integralTransform v (X,Φ.val.2)).1 a b) he).trans
      (transform_upper (d.symbol v) n (modulus F v) (selfDual F d.character v) (d.character.localValue F v) u Φ.val a b)
  · intro y
    rw [(hg (d.fourier v Φ)).2,d.fourier_apply,d.fourier_apply]
    let dx := selfDual F d.character v
    letI : NullSingletonClass dx := d.selfDual_nullSingleton v
    simp only [integralTransform,transform]
    congr 1
    apply integral_congr_ae
    filter_upwards [dx.ae_ne 0] with t ht
    let T := Units.mk0 t ht
    change _ * d.axisLine v (g Φ) y T.val = _ * d.axisLine v Φ y T.val
    rw [d.axisLine_unit,d.axisLine_unit]
    congr 2
    unfold marginal
    simp_rw [(hg Φ).1]
    letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
    exact integral_add_right_eq_self (μ := dx) _ _

theorem fourier_lower (u : LocalField F v) {g : d.Operators v} (hg : d.IsLower v u g) (Φ : d.schwartz v) :
    d.fourier v (g Φ) = g (d.fourier v Φ) := by
  apply d.section_eq_of_Y
  · funext a b
    rw [(hg (d.fourier v Φ)).1,d.fourier_apply,d.fourier_apply]
    have he : (g Φ).val.2 = (lowerShear (d.symbol v) u Φ.val).2 := funext fun x => funext ((hg Φ).1 x)
    exact (congrArg (fun Y => (d.integralTransform v (Φ.val.1,Y)).2 a b) he).trans
      (transform_lower (d.symbol v) n (modulus F v) (selfDual F d.character v) (d.character.localValue F v) u Φ.val a b)
  · intro x
    rw [(hg (d.fourier v Φ)).2,d.fourier_apply,d.fourier_apply]
    let dx := selfDual F d.character v
    letI : NullSingletonClass dx := d.selfDual_nullSingleton v
    simp only [integralTransform,transform]
    congr 1
    apply integral_congr_ae
    filter_upwards [dx.ae_ne 0] with t ht
    let T := Units.mk0 t ht
    have e := d.horizontalLine_unit v (g Φ) x T
    have e' := d.horizontalLine_unit v Φ x T
    change _ * (radon n (d.symbol v) (modulus F v) dx (g Φ).val T.val).1 x 0 =
      _ * (radon n (d.symbol v) (modulus F v) dx Φ.val T.val).1 x 0
    rw [e,e']
    simp_rw [(hg Φ).1]
    letI : dx.IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
    let Y := -(T^n)/x
    exact congrArg (fun z : ℂ => d.character.localValue F v t * (z / (modulus F v x : ℂ)))
      (integral_add_right_eq_self (μ := dx) (fun z => Φ.val.2 z Y) (u*Y.val))

/-- The equivariance assertion of Theorem 7.1 at every place. -/
theorem fourier_equivariant (g : d.cover v) (Φ : d.schwartz v) :
    d.fourier v (g.val Φ) = g.val (d.fourier v Φ) := by
  let P (s : d.Operators v) := ∀ f, d.fourier v (s f) = s (d.fourier v f)
  suffices P g.val from this Φ
  refine Subgroup.closure_induction (p := fun s _ => P s) ?_ (fun _ => rfl) ?_ ?_ g.property
  · rintro s (⟨z,hz⟩ | ⟨u,hu⟩ | ⟨u,hu⟩)
    · intro f
      rw [hz,hz,map_smul]
    · exact d.fourier_upper v u hu
    · exact d.fourier_lower v u hu
  · intro s t _ _ hs ht f
    exact (hs (t f)).trans (congrArg s (ht f))
  · intro s _ hs f
    apply s.injective
    change s (d.fourier v (s.symm f)) = s (s.symm (d.fourier v f))
    rw [LinearEquiv.apply_symm_apply]
    simpa only [LinearEquiv.apply_symm_apply] using (hs (s.symm f)).symm

end MetaplecticPoisson.Datum
