import MetaplecticSummation.Marginals.ArchimedeanTest
import MetaplecticSummation.ArchimedeanFourierSchwartz

/-! Schwartz regularity of the normalized axis density in Appendix A. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory CompactlySupported
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
variable (v : Place F)
local notation "K" => LocalField F v
local notation "N" => modulus F v (n : K)
local notation "dx" => selfDual F d.character v

/-- The defining Radon integral on the vertical axis is Schwartz–Bruhat for
a test section at every place (the last assertion of the marginal-axis lemma). -/
theorem axisLine_test_bruhat (Φ : d.schwartz v) (hΦ : Φ.val ∈ d.testSet v) (y : Kˣ) :
    Bruhat v (d.axisLine v Φ y) := by
  cases v with
  | inr p => exact d.axisLine_finiteTest_bruhat p Φ hΦ y
  | inl w =>
    have go {L : Type} [NormedField L] [NormedAlgebra ℝ L] (e : w.Completion ≃+* L) (he : Isometry e) :
        ∃ G : SchwartzMap L ℂ, ∀ t, d.axisLine (.inl w) Φ y t = G (e t) := by
      obtain ⟨G,hG,_⟩ := (d.arch_radon_schwartz_slices w hΦ e he).2
      exact ⟨G (y,0),hG (y,0)⟩
    dsimp only [Bruhat]
    split
    · exact go _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _)
    · exact go _ (InfinitePlace.Completion.isometry_extensionEmbedding w)

omit [NeZero n] in
theorem Bruhat.const_mul {f : K → ℂ} (hf : Bruhat v f) (c : ℂ) :
    Bruhat v (fun t => c * f t) := by
  cases v with
  | inr p => exact ⟨hf.1.comp (c * ·),hf.2.mul_left (f := fun _ => c)⟩
  | inl w =>
    dsimp only [Bruhat] at hf ⊢
    split at hf <;> rename_i h
    · rw [dif_pos h]; obtain ⟨G,hG⟩ := hf; exact ⟨c • G,fun t => congrArg (c * ·) (hG t)⟩
    · rw [dif_neg h]; obtain ⟨G,hG⟩ := hf; exact ⟨c • G,fun t => congrArg (c * ·) (hG t)⟩

/-- Formula for the density of a transformed section, including its value
at the origin. The normalization uses the self-dual additive measure. -/
theorem axisDensity_transform_eq_hat (Φ Ψ : d.schwartz v) (hΨ : Ψ.val = d.integralTransform v Φ.val)
    (x : Kˣ) (hi : Integrable (d.axisLine v Φ (-1/x)) dx) :
    d.axisDensity v Ψ x = fun t =>
      ((N : ℂ) / (modulus F v x.val : ℂ) * (Real.sqrt N : ℂ)⁻¹) * d.hat v (d.axisLine v Φ (-1/x)) t := by
  funext t
  by_cases ht : t = 0
  · subst t
    rw [d.axisDensity_zero,← d.axisLine_hat_zero_of_charts v Φ Ψ hΨ _ hi,mul_assoc]
  let u := Units.mk0 t ht
  have h := (d.transform_pow_ray v Φ.val u).2 0 (-1/x)
  rw [mul_zero,← hΨ] at h
  change (modulus F v u.val : ℂ)^(n-1) * d.axis v Ψ (u^n*(-1/x)) =
    (Real.sqrt N : ℂ)⁻¹ * d.hat v (d.axisLine v Φ (-1/x)) u.val at h
  change d.axisDensity v Ψ x u.val = _
  rw [d.axisDensity_unit,mul_assoc,← show u^n*(-1/x) = -(u^n)/x by rw [mul_div_assoc',mul_neg_one],h,mul_assoc]
  rfl

/-- The density of the transform of a test section is Schwartz–Bruhat at
every real, complex, and finite place. -/
theorem axisDensity_transformTest_bruhat (Φ : d.schwartz v) (hΦ : Φ.val ∈ d.testSet v) (x : Kˣ) :
    Bruhat v (d.axisDensity v (d.transformTest v Φ hΦ) x) := by
  have hb := d.axisLine_test_bruhat v Φ hΦ (-1/x)
  rw [d.axisDensity_transform_eq_hat v Φ _ rfl x (hb.integrable d)]
  apply Bruhat.const_mul
  cases v with
  | inl w => exact d.arch_hat_bruhat w hb
  | inr p => exact d.hat_finite_bruhat p hb

/-- The normalized axis density depends linearly on its section. -/
def axisDensityLinear (x : Kˣ) : d.schwartz v →ₗ[ℂ] (K → ℂ) where
  toFun Φ := d.axisDensity v Φ x
  map_add' Φ Ψ := by
    funext t
    by_cases ht : t = 0
    · subst t
      simp only [Pi.add_apply,axisDensity_zero,map_add]
      exact mul_add _ _ _
    · let u := Units.mk0 t ht
      change d.axisDensity v (Φ+Ψ) x u.val = d.axisDensity v Φ x u.val + d.axisDensity v Ψ x u.val
      simp only [d.axisDensity_unit]
      exact mul_add _ _ _
  map_smul' c Φ := by
    funext t
    by_cases ht : t = 0
    · subst t
      simp only [Pi.smul_apply,axisDensity_zero,map_smul,smul_eq_mul,RingHom.id_apply]
      exact mul_left_comm _ _ _
    · let u := Units.mk0 t ht
      change d.axisDensity v (c • Φ) x u.val = c * d.axisDensity v Φ x u.val
      simp only [d.axisDensity_unit]
      exact mul_left_comm _ _ _

private def archBruhatSubmodule (w : InfinitePlace F) : Submodule ℂ (LocalField F (.inl w) → ℂ) where
  carrier := {f | Bruhat (.inl w) f}
  zero_mem' := by
    dsimp only [Set.mem_setOf_eq,Bruhat]
    split <;> exact ⟨0,fun _ => rfl⟩
  add_mem' := by
    intro f g H J
    change Bruhat (.inl w) (f+g)
    change Bruhat (.inl w) f at H
    change Bruhat (.inl w) g at J
    dsimp only [Bruhat] at H J ⊢
    split <;> rename_i hw
    · rw [dif_pos hw] at H J
      obtain ⟨G,hG⟩ := H
      obtain ⟨T,hT⟩ := J
      exact ⟨G+T,fun t => congrArg₂ (· + ·) (hG t) (hT t)⟩
    · rw [dif_neg hw] at H J
      obtain ⟨G,hG⟩ := H
      obtain ⟨T,hT⟩ := J
      exact ⟨G+T,fun t => congrArg₂ (· + ·) (hG t) (hT t)⟩
  smul_mem' := fun a _ h => Bruhat.const_mul (.inl w) h a

/-- At any place, the axis density of a Schwartz section is Schwartz–Bruhat. -/
theorem axisDensity_bruhat (Φ : d.schwartz v) (x : Kˣ) : Bruhat v (d.axisDensity v Φ x) := by
  cases v with
  | inr p => exact d.axisDensity_finite_bruhat p Φ x
  | inl w =>
    let B := d.axisDensityLinear (.inl w) x
    suffices H : ⊤ ≤ (archBruhatSubmodule w).comap B from H (Submodule.mem_top (x := Φ))
    let S := d.testSet (.inl w) ∪ d.integralTransform (.inl w) '' d.testSet (.inl w)
    have span : Submodule.span ℂ ((Subtype.val : d.schwartz (.inl w) → _) ⁻¹' S) = ⊤ :=
      Submodule.span_span_coe_preimage
    apply span.ge.trans (Submodule.span_le.mpr ?_)
    rintro ⟨f,hf⟩ (ht | ⟨g,hg,rfl⟩)
    · exact d.arch_axisDensity_test_bruhat w ⟨f,hf⟩ ht x
    · let Γ : d.schwartz (.inl w) := ⟨g,Submodule.subset_span (Or.inl hg)⟩
      exact d.axisDensity_transformTest_bruhat (.inl w) Γ hg x

end MetaplecticPoisson.Datum
