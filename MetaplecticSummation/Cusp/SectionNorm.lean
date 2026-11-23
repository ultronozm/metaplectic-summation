import MetaplecticSummation.RationalLifts

/-! Pointwise absolute values of genuine sections and their transformation under the cover. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField
open scoped Matrix MatrixGroups
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (v : Place F)
local notation "K" => LocalField F v

/-- The common chart norm away from zero, extended by zero at the origin. -/
def sectionNorm (Φ : d.schwartz v) (z : Fin 2 → K) : ℝ :=
  if z 0 ≠ 0 then ‖xChart Φ.val (z 0,z 1)‖ else ‖yChart Φ.val (z 0,z 1)‖

theorem sectionNorm_x (Φ : d.schwartz v) (z : Fin 2 → K) (hx : z 0 ≠ 0) :
    d.sectionNorm v Φ z = ‖Φ.val.1 (Units.mk0 _ hx) (z 1)‖ := by simp [sectionNorm,xChart,hx]

theorem sectionNorm_y (Φ : d.schwartz v) (z : Fin 2 → K) (hy : z 1 ≠ 0) :
    d.sectionNorm v Φ z = ‖Φ.val.2 (z 0) (Units.mk0 _ hy)‖ := by
  by_cases hx : z 0 ≠ 0
  · rw [d.sectionNorm_x v Φ z hx]
    have he := d.schwartz_glues v Φ (Units.mk0 _ hx) (Units.mk0 _ hy)
    simpa only [Units.val_mk0,norm_mul,norm_symbol,one_mul] using congrArg norm he
  · simp [sectionNorm,hx,yChart,hy]

theorem sectionNorm_diagonal (z : RationalPoint F) (Φ : d.schwartz v) :
    d.sectionNorm v Φ ![diagonal F v z.val.1,diagonal F v z.val.2] = ‖d.localValue z v Φ‖ := by
  by_cases hx : z.val.1 ≠ 0 <;> simp [sectionNorm,localValue,diagonalPoint,hx]

private theorem sectionNorm_upper {g : d.Operators v} {u : K} (hg : d.IsUpper v u g)
    (Φ : d.schwartz v) (z : Fin 2 → K) :
    d.sectionNorm v (g Φ) z = d.sectionNorm v Φ (z ᵥ* !![1,u;0,1]) := by
  let y := z ᵥ* !![1,u;0,1]
  have h₀ : y 0 = z 0 := by simp [y,Matrix.vecHead,Matrix.vecTail]
  have h₁ : y 1 = z 1+u*z 0 := by simp [y,Matrix.vecHead,Matrix.vecTail,mul_comm,add_comm]; abel
  change _ = d.sectionNorm v Φ y
  by_cases hx : z 0 ≠ 0
  · rw [d.sectionNorm_x v _ _ hx,d.sectionNorm_x v _ _ (h₀ ▸ hx),(hg Φ).1,h₁]
    simp only [h₀,Units.val_mk0]
  · have hx₀ := not_ne_iff.mp hx
    by_cases hy : z 1 ≠ 0
    · have h₁' : y 1 = z 1 := by simp [h₁,hx₀]
      rw [d.sectionNorm_y v _ _ hy,d.sectionNorm_y v _ _ (h₁' ▸ hy),h₀,hx₀,(hg Φ).2]
      simp only [h₁']
    · simp [sectionNorm,yChart,h₀,h₁,hx₀,not_ne_iff.mp hy]

private theorem sectionNorm_lower {g : d.Operators v} {u : K} (hg : d.IsLower v u g)
    (Φ : d.schwartz v) (z : Fin 2 → K) :
    d.sectionNorm v (g Φ) z = d.sectionNorm v Φ (z ᵥ* !![1,0;u,1]) := by
  let y := z ᵥ* !![1,0;u,1]
  have h₁ : y 1 = z 1 := by simp [y,Matrix.vecHead,Matrix.vecTail]
  have h₀ : y 0 = z 0+u*z 1 := by simp [y,Matrix.vecHead,Matrix.vecTail,mul_comm]
  change _ = d.sectionNorm v Φ y
  by_cases hy : z 1 ≠ 0
  · rw [d.sectionNorm_y v _ _ hy,d.sectionNorm_y v _ _ (h₁ ▸ hy),(hg Φ).1,h₀]
    simp only [h₁,Units.val_mk0]
  · have hy₀ := not_ne_iff.mp hy
    by_cases hx : z 0 ≠ 0
    · have h₀' : y 0 = z 0 := by simp [h₀,hy₀]
      rw [d.sectionNorm_x v _ _ hx,d.sectionNorm_x v _ _ (h₀' ▸ hx),h₁,hy₀,(hg Φ).2]
      simp only [h₀']
    · simp [sectionNorm,yChart,h₀,h₁,hy₀,not_ne_iff.mp hx]

/-- The transformation of absolute values uses just the projection on generators.
This form also applies before choosing the project's Kubota projection. -/
theorem sectionNorm_of_projection (π : d.cover v →* SL(2,K))
    (hs : ∀ g, d.IsCentralScalar v g.val → π g = 1)
    (hu : ∀ g u, d.IsUpper v u g.val → (π g).val = !![1,u;0,1])
    (hl : ∀ g u, d.IsLower v u g.val → (π g).val = !![1,0;u,1])
    (g : d.cover v) (Φ : d.schwartz v) (z : Fin 2 → K) :
    d.sectionNorm v (g.val Φ) z = d.sectionNorm v Φ (z ᵥ* (π g).val) := by
  obtain ⟨g,hg⟩ := g
  induction hg using Subgroup.closure_induction generalizing Φ z with
  | mem g hg =>
    rcases hg with h | ⟨u,h⟩ | ⟨u,h⟩
    · rw [hs _ h, show (1 : SL(2,K)).val = 1 from rfl,Matrix.vecMul_one]
      obtain ⟨c,hc⟩ := h
      have hc' : ‖((d.embedding c).val : ℂ)‖ = 1 := by
        apply Complex.norm_eq_one_of_pow_eq_one _ (NeZero.ne n)
        have hp := congrArg d.embedding (show c^n=1 from Subtype.ext c.property)
        simpa using congrArg Units.val hp
      rw [hc]
      by_cases hx : z 0 = 0 <;> by_cases hy : z 1 = 0 <;>
        simp [sectionNorm,xChart,yChart,hx,hy,smul_eq_mul,hc']
    · rw [hu _ _ h]
      exact d.sectionNorm_upper v h Φ z
    · rw [hl _ _ h]
      exact d.sectionNorm_lower v h Φ z
  | one =>
    change _ = d.sectionNorm v Φ (z ᵥ* (π 1).val)
    rw [map_one]; simp
  | mul a b ha hb ia ib =>
    let A : d.cover v := ⟨a,ha⟩
    let B : d.cover v := ⟨b,hb⟩
    change d.sectionNorm v (a (b Φ)) z = d.sectionNorm v Φ (z ᵥ* (π (A*B)).val)
    rw [map_mul,ia,ib,Matrix.vecMul_vecMul]
    rfl
  | inv a ha ih =>
    let A : d.cover v := ⟨a,ha⟩
    have he := ih (a⁻¹ Φ) (z ᵥ* (π (A⁻¹)).val)
    have hm : (π (A⁻¹)).val * (π A).val = 1 := congrArg Subtype.val (by rw [map_inv,inv_mul_cancel] : π (A⁻¹) * π A = 1)
    change d.sectionNorm v (a (a.symm Φ)) _ = d.sectionNorm v (a⁻¹ Φ) ((z ᵥ* (π (A⁻¹)).val) ᵥ* (π A).val) at he
    rw [LinearEquiv.apply_symm_apply,Matrix.vecMul_vecMul,hm,Matrix.vecMul_one] at he
    exact he.symm.trans (congrArg (fun b : d.cover v => d.sectionNorm v Φ (z ᵥ* (π b).val)) (Subtype.ext rfl))

theorem sectionNorm_cover (g : d.cover v) (Φ : d.schwartz v) (z : Fin 2 → K) :
    d.sectionNorm v (g.val Φ) z = d.sectionNorm v Φ (z ᵥ* (d.coverProjection v g).val) :=
  d.sectionNorm_of_projection v _ (fun g => ((d.kubota_projection v).choose_spec.2.1 g).mpr)
    (d.kubota_projection v).choose_spec.2.2.1 (d.kubota_projection v).choose_spec.2.2.2 g Φ z

end MetaplecticPoisson.Datum
