import MetaplecticSummation.FiniteSchwartzLines
import MetaplecticSummation.Marginals

/-! Linearity of the two-chart transform where its integrals converge. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open Set Filter MeasureTheory NumberField IsDedekindDomain
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)

abbrev radonAt (f : Charts (LocalField F v)) := radon n (d.symbol v) (modulus F v) (selfDual F d.character v) f

/-- Absolute convergence of the two outer integrals in Definition 4.4. -/
def TransformIntegrable (f : Charts (LocalField F v)) : Prop :=
  let ψ := d.character.localValue F v
  let dx := selfDual F d.character v
  (∀ (a : (LocalField F v)ˣ) b, Integrable (fun t => ψ t * (d.radonAt v f t).1 a b) dx) ∧
    ∀ a (b : (LocalField F v)ˣ), Integrable (fun t => ψ t * (d.radonAt v f t).2 a b) dx

theorem radonAt_smul (c : ℂ) (f : Charts (LocalField F v)) (t : LocalField F v) :
    d.radonAt v (c • f) t = c • d.radonAt v f t := by
  have factor (P : Prop) [Decidable P] (g : P → ℂ) :
      (if h : P then c*g h else 0) = c*(if h : P then g h else 0) := by split <;> simp
  apply Prod.ext <;> funext a b <;>
    simp only [radonAt,radon,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,smul_eq_mul,
      mul_assoc,factor] <;>
    rw [integral_const_mul,mul_div_assoc]

theorem integralTransform_smul (c : ℂ) (f : Charts (LocalField F v)) :
    d.integralTransform v (c • f) = c • d.integralTransform v f := by
  have h := d.radonAt_smul v c f
  dsimp only [radonAt] at h
  apply Prod.ext <;> funext a b <;>
    simp only [integralTransform,transform,h,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,smul_eq_mul,
      mul_left_comm (d.character.localValue F v _) c,integral_const_mul,mul_left_comm _ c]

theorem finite_radonAt_add (p : HeightOneSpectrum (𝓞 F)) (Φ Ψ : d.schwartz (.inr p))
    (t : LocalField F (.inr p)) (ht : t ≠ 0) :
    let v : Place F := .inr p
    d.radonAt v (Φ.val+Ψ.val) t = d.radonAt v Φ.val t + d.radonAt v Ψ.val t := by
  let v : Place F := .inr p
  let dx := selfDual F d.character v
  let H := d.symbol v
  obtain ⟨fx,fy⟩ := d.finite_schwartz_line_integrals p Φ t ht
  obtain ⟨gx,gy⟩ := d.finite_schwartz_line_integrals p Ψ t ht
  apply Prod.ext
  · funext a b
    change (∫ x, lineIntegrandX H (Φ.val+Ψ.val) n t a b x ∂dx) / _ =
      (∫ x, lineIntegrandX H Φ.val n t a b x ∂dx)/_ + (∫ x, lineIntegrandX H Ψ.val n t a b x ∂dx)/_
    rw [← add_div,← integral_add (fx a b) (gx a b)]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    by_cases h : x ≠ 0 <;> simp [lineIntegrandX,H,v,h,add_mul]
  · funext a b
    change (∫ x, lineIntegrandY H (Φ.val+Ψ.val) n t a b x ∂dx) / _ =
      (∫ x, lineIntegrandY H Φ.val n t a b x ∂dx)/_ + (∫ x, lineIntegrandY H Ψ.val n t a b x ∂dx)/_
    rw [← add_div,← integral_add (fy a b) (gy a b)]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    by_cases h : x ≠ 0 <;> simp [lineIntegrandY,H,v,h,add_mul]

theorem TransformIntegrable.smul {f : Charts (LocalField F v)} (hf : d.TransformIntegrable v f) (c : ℂ) :
    d.TransformIntegrable v (c • f) := by
  constructor
  · intro a b
    simpa only [d.radonAt_smul,Prod.smul_fst,Pi.smul_apply,smul_eq_mul,mul_left_comm _ c]
      using ((hf.1 a b).const_mul c)
  · intro a b
    simpa only [d.radonAt_smul,Prod.smul_snd,Pi.smul_apply,smul_eq_mul,mul_left_comm _ c]
      using ((hf.2 a b).const_mul c)

theorem finite_transform_add (p : HeightOneSpectrum (𝓞 F)) (Φ Ψ : d.schwartz (.inr p))
    (hΦ : d.TransformIntegrable (.inr p) Φ.val) (hΨ : d.TransformIntegrable (.inr p) Ψ.val) :
    let v : Place F := .inr p
    d.TransformIntegrable v (Φ.val + Ψ.val) ∧
      d.integralTransform v (Φ.val+Ψ.val) = d.integralTransform v Φ.val + d.integralTransform v Ψ.val := by
  let v : Place F := .inr p
  let dx := selfDual F d.character v
  letI : NullSingletonClass dx := d.selfDual_nullSingleton v
  let ψ := d.character.localValue F v
  let X (f : Charts (LocalField F v)) (a : (LocalField F v)ˣ) (b t : LocalField F v) :=
    ψ t * (d.radonAt v f t).1 a b
  let Y (f : Charts (LocalField F v)) (a : LocalField F v) (b : (LocalField F v)ˣ) (t : LocalField F v) :=
    ψ t * (d.radonAt v f t).2 a b
  have xadd a b : X (Φ.val+Ψ.val) a b =ᵐ[dx] X Φ.val a b + X Ψ.val a b := by
    filter_upwards [dx.ae_ne 0] with t ht
    have he : d.radonAt v (Φ.val+Ψ.val) t = d.radonAt v Φ.val t + d.radonAt v Ψ.val t := d.finite_radonAt_add p Φ Ψ t ht
    simp only [X,he,Prod.fst_add,Pi.add_apply,mul_add]
  have yadd a b : Y (Φ.val+Ψ.val) a b =ᵐ[dx] Y Φ.val a b + Y Ψ.val a b := by
    filter_upwards [dx.ae_ne 0] with t ht
    have he : d.radonAt v (Φ.val+Ψ.val) t = d.radonAt v Φ.val t + d.radonAt v Ψ.val t := d.finite_radonAt_add p Φ Ψ t ht
    simp only [Y,he,Prod.snd_add,Pi.add_apply,mul_add]
  refine ⟨⟨fun a b => (((hΦ.1 a b).add (hΨ.1 a b))).congr (xadd a b).symm,
    fun a b => ((hΦ.2 a b).add (hΨ.2 a b)).congr (yadd a b).symm⟩,?_⟩
  apply Prod.ext
  · funext a b
    change _ * (∫ t, X (Φ.val + Ψ.val) a b t ∂dx) =
      _ * (∫ t, X Φ.val a b t ∂dx) + _ * (∫ t, X Ψ.val a b t ∂dx)
    rw [integral_congr_ae (xadd a b)]
    simp only [Pi.add_apply,integral_add (show Integrable (X Φ.val a b) dx from hΦ.1 a b)
      (show Integrable (X Ψ.val a b) dx from hΨ.1 a b),mul_add]
  · funext a b
    change _ * (∫ t, Y (Φ.val + Ψ.val) a b t ∂dx) =
      _ * (∫ t, Y Φ.val a b t ∂dx) + _ * (∫ t, Y Ψ.val a b t ∂dx)
    rw [integral_congr_ae (yadd a b)]
    simp only [Pi.add_apply,integral_add (show Integrable (Y Φ.val a b) dx from hΦ.2 a b)
      (show Integrable (Y Ψ.val a b) dx from hΨ.2 a b),mul_add]

end MetaplecticPoisson.Datum
