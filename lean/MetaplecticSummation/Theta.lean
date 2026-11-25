import MetaplecticSummation.ThetaSquare
import MetaplecticSummation.TensorDescent
import MetaplecticSummation.LocalGrowth

/-! The theta functional and its Fourier difference in Appendix B. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open Filter
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- The absolute convergence consequence of Lemma B.1 at the identity idele. -/
theorem summable_theta_pure (f : ∀ v, d.schwartz v) (hf) :
    Summable (fun z => ‖d.evaluation (d.pure f hf) z‖) := by
  obtain ⟨C,hC,hfin,hc,hz⟩ := d.theta_local_bounds f hf
  obtain ⟨_,_,hM⟩ := theta_majorant_bound (growthExponent_nonneg n) (growthExponent_le_one n) C hC hfin hc
  let a (_ : Place F) : ℝ := 1
  have ha : ∀ᶠ v in cofinite, a v = 1 := .of_forall fun _ => rfl
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hM a (fun _ => zero_lt_one) ha).1
  intro z
  have hunit : ∀ᶠ v in cofinite, d.localValue z v (f v) = 1 := by
    filter_upwards [hf,d.eventually_basic_value z] with v h he
    exact h ▸ he
  rw [d.evaluation_pure]
  change (normHom.toMonoidHom : ℂ →* ℝ) (∏ᶠ v, d.localValue z v (f v)) ≤ _
  rw [MonoidHom.map_finprod _ (eventually_cofinite.mp hunit)]
  change (∏ᶠ v, ‖d.localValue z v (f v)‖) ≤ ∏ᶠ v, localThetaBound (growthExponent n) v (C v) (a v*vectorModulus v z)
  apply finprod_mono_real (a := fun v => ‖d.localValue z v (f v)‖) (hunit.mono fun v h => by rw [h,norm_one])
    (localThetaBound_cofinite (growthExponent n) hc ha z) (fun _ => norm_nonneg _)
  intro v
  simpa only [a,one_mul] using hz z v

theorem summable_theta (Φ : d.Schwartz) : Summable (fun z => ‖d.evaluation Φ z‖) := by
  apply restrictedTensor_induction d.basic (P := fun f => Summable (fun z => ‖d.evaluation f z‖))
    (fun f hf => d.summable_theta_pure f hf) _ _ _ Φ
  · simp
  · intro x y hx hy
    rw [d.evaluation.map_add]
    apply (hx.add hy).of_norm_bounded
    intro z
    simpa only [norm_norm,Pi.add_apply] using norm_add_le (d.evaluation x z) (d.evaluation y z)
  · intro c x hx
    simpa only [d.evaluation.map_smul,Pi.smul_apply,smul_eq_mul,norm_mul] using hx.mul_left ‖c‖

/-- Summation on nonzero rational vectors. -/
def theta : d.Schwartz →ₗ[ℂ] ℂ where
  toFun Φ := ∑' z, d.evaluation Φ z
  map_add' Φ Ψ := by
    simp only [map_add,Pi.add_apply]
    exact (d.summable_theta Φ).of_norm.tsum_add (d.summable_theta Ψ).of_norm
  map_smul' c Φ := by simp only [map_smul,Pi.smul_apply,smul_eq_mul,tsum_mul_left,RingHom.id_apply]

def thetaDifference : d.Schwartz →ₗ[ℂ] ℂ := d.theta - d.theta.comp d.adelicFourier

theorem thetaDifference_fourier (Φ : d.Schwartz) :
    d.thetaDifference (d.adelicFourier Φ) = -d.thetaDifference Φ := by
  change d.theta (d.adelicFourier Φ) - d.theta (d.adelicFourier (d.adelicFourier Φ)) =
    -(d.theta Φ - d.theta (d.adelicFourier Φ))
  rw [show d.theta (d.adelicFourier (d.adelicFourier Φ)) = d.theta Φ from d.theta_fourier_square Φ,neg_sub]

end MetaplecticPoisson.Datum
