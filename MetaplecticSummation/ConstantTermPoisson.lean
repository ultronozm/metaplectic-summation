import MetaplecticSummation.FourierCoefficients.Basic
import MetaplecticSummation.ConstantTermSupport
import MetaplecticSummation.AdelicFourierIntegrals

/-! The two applications of additive Poisson summation in Proposition B.4. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Filter
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

private theorem tsum_zero_add_units (a : F → ℂ) (ha : Summable a) :
    (∑' x : F, a x) = a 0 + ∑' u : Fˣ, a u.val := by
  let S : Finset F := {0}
  let e : Fˣ ≃ ((S : Set F)ᶜ : Set F) := unitsEquivNeZero.trans (Equiv.subtypeEquivRight fun x => by simp [S])
  rw [← ha.sum_add_tsum_compl (s := S)]
  rw [show ∑ t ∈ S, a t = a 0 from Finset.sum_singleton _ _,← e.tsum_eq (fun x => a x.val)]
  rfl

/-- The first additive Poisson identity in B.4, for each rational power-class representative. -/
theorem axisLine_poisson (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) (y : Fˣ) :
    (∏ᶠ v, d.axisLine v (Φ v) (atPlace v y) 0) +
      (∑' t : Fˣ, ∏ᶠ v, d.marginal v (Φ v) (atPlace v (t^n/y))) =
    (∏ᶠ v, (d.leading v (d.fourier v (Φ v))).2 0 (atPlace v y)) +
      ∑' t : Fˣ, ∏ᶠ v, d.axis v (d.fourier v (Φ v)) (atPlace v (t^n*y)) := by
  let f := fun v => d.axisLine v (Φ v) (atPlace v y)
  have hf (v) : Bruhat v (f v) := d.axisLine_bruhat v _ _
  obtain ⟨ha,hb,eqn⟩ := d.additivePoisson_tensor f hf (d.eventually_axisLine_basic Φ hΦ y)
  rw [tsum_zero_add_units _ ha.of_norm,tsum_zero_add_units _ hb.of_norm] at eqn
  simp only [map_zero] at eqn
  change (∏ᶠ v, f v 0) + (∑' t : Fˣ, ∏ᶠ v, f v (atPlace v t)) =
    (∏ᶠ v, d.hat v (f v) 0) + ∑' t : Fˣ, ∏ᶠ v, d.hat v (f v) (atPlace v t) at eqn
  simpa only [f,d.axisLine_product,d.axisLine_hat_zero_product Φ y (fun v => Bruhat.integrable d (hf v)),
    d.axisLine_hat_product] using eqn

/-- The second additive Poisson identity in B.4, for each rational power-class representative. -/
theorem axisDensity_poisson (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) (x : Fˣ) :
    (∏ᶠ v, (d.leading v (Φ v)).2 0 (atPlace v (-1/x))) +
      (∑' t : Fˣ, ∏ᶠ v, d.axis v (Φ v) (atPlace v (-(t^n)/x))) =
    (∏ᶠ v, d.hat v (d.axisDensity v (Φ v) (atPlace v x)) 0) +
      ∑' t : Fˣ, ∏ᶠ v, d.marginal v (d.fourier v (Φ v)) (atPlace v (t^n*x)) := by
  let f := fun v => d.axisDensity v (Φ v) (atPlace v x)
  obtain ⟨ha,hb,eqn⟩ := d.additivePoisson_tensor f (fun v => d.axisDensity_bruhat v _ _) (d.eventually_axisDensity_basic Φ hΦ x)
  rw [tsum_zero_add_units _ ha.of_norm,tsum_zero_add_units _ hb.of_norm] at eqn
  simp only [map_zero] at eqn
  change (∏ᶠ v, f v 0) + (∑' t : Fˣ, ∏ᶠ v, f v (atPlace v t)) =
    (∏ᶠ v, d.hat v (f v) 0) + ∑' t : Fˣ, ∏ᶠ v, d.hat v (f v) (atPlace v t) at eqn
  simpa only [f,d.axisDensity_zero_product,d.axisDensity_product,d.axisDensity_hat_product] using eqn

/-- Absolute convergence of the rational marginal series in the constant term. -/
theorem summable_rational_marginal (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) :
    Summable (fun a : Fˣ => ‖∏ᶠ v, d.marginal v (Φ v) (atPlace v a)‖) := by
  let M (a : Fˣ) := ∏ᶠ v, d.marginal v (Φ v) (atPlace v a)
  let Q : Fˣ →* GlobalClass n F := QuotientGroup.mk' (powMonoidHom n : Fˣ →* Fˣ).range
  obtain ⟨C,hC⟩ := d.rational_marginal_supported_on_finite_classes Φ hΦ
  have fiber (c : GlobalClass n F) : Summable (fun a : {a : Fˣ | Q a = c} => ‖M a.val‖) := by
    let I := {a : Fˣ | Q a = c}
    let y := c.out⁻¹
    have roots (a : I) : ∃ t : Fˣ, t^n / y = a.val := by
      have he : Q (a.val/c.out) = 1 := by
        rw [map_div,a.property,show Q c.out = c from Quotient.out_eq c]
        exact div_self' c
      obtain ⟨t,ht⟩ := (QuotientGroup.eq_one_iff _).mp he
      change t^n = a.val / c.out at ht
      exact ⟨t,by rw [ht]; simp [y]⟩
    choose root hroot using roots
    have inj : Function.Injective root := fun x z h =>
      Subtype.ext ((hroot x).symm.trans ((congrArg (fun t => t^n / y) h).trans (hroot z)))
    let f (v : Place F) := d.axisLine v (Φ v) (atPlace v y)
    have ha := (d.additivePoisson_tensor f (fun v => d.axisLine_bruhat v _ _)
      (d.eventually_axisLine_basic Φ hΦ y)).1
    apply ((ha.comp_injective (Units.val_injective.comp inj))).congr
    intro a
    exact congrArg norm ((d.axisLine_product Φ y (root a)).trans (congrArg M (hroot a)))
  let g (c : GlobalClass n F) := {a : Fˣ | Q a = c}.indicator (fun a => ‖M a‖)
  have hg (c : GlobalClass n F) : Summable (g c) := summable_subtype_iff_indicator.mp (fiber c)
  apply (summable_sum (s := C) fun c _ => hg c).congr
  intro a
  by_cases h : Q a ∈ C
  · rw [Finset.sum_eq_single (Q a)]
    · simp [g,M]
    · intro b _ hb
      simp [g,Ne.symm hb]
    · exact fun hn => (hn h).elim
  · have hz : M a = 0 := not_ne_iff.mp fun hn => h (hC a hn)
    change (∑ c ∈ C, g c a) = ‖M a‖
    rw [hz,norm_zero]
    apply Finset.sum_eq_zero
    intro c hc
    have hne : Q a ≠ c := fun he => h (he ▸ hc)
    simp [g,hne]


private theorem hasSum_leading_classes (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) :
    HasSum (fun c : GlobalClass n F => ∏ᶠ v, (d.leading v (Φ v)).2 0 (atPlace v c.out))
      ((n : ℂ) * d.axisBoundary Φ) := by
  let Q : Fˣ →* GlobalClass n F := QuotientGroup.mk' (powMonoidHom n : Fˣ →* Fˣ).range
  let e := Equiv.divLeft (Q (-1))
  obtain ⟨C,hC⟩ := d.density_zero_supported_on_finite_classes Φ hΦ
  let b (c : GlobalClass n F) := ∏ᶠ v, (d.leading v (Φ v)).2 0 (atPlace v c.out)
  have hb : Function.HasFiniteSupport b := by
    apply (C.finite_toSet.preimage e.injective.injOn).subset
    intro c hc
    change e c ∈ C
    have he : Q (-1 / c.out) = e c := by
      rw [map_div]
      exact congrArg (Q (-1) / ·) (Quotient.out_eq c)
    rw [← he]
    apply hC
    rwa [d.axisDensity_zero_product,div_div_cancel]
  change HasSum b ((n:ℂ) * ((n:ℂ)⁻¹ * ∑ᶠ c, b c))
  rw [← mul_assoc,mul_inv_cancel₀ (NeZero.ne (n:ℂ)),one_mul,← (show (∑' c, b c) = ∑ᶠ c, b c from tsum_eq_finsum hb)]
  exact (summable_of_hasFiniteSupport hb).hasSum

/-- Proposition B.4, obtained by summing the two additive Poisson identities
over rational power classes and cancelling their zero-frequency sums by B.3. -/
theorem constantTerm_identity (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) :
    let dual := fun v => d.fourier v (Φ v)
    d.constantTerm Φ + d.axisBoundary Φ = d.constantTerm dual + d.axisBoundary dual := by
  let dual := fun v => d.fourier v (Φ v)
  have hd : ∀ᶠ v in cofinite, dual v = d.basic v := by
    filter_upwards [hΦ,d.eventually_fourier_basic] with v h h'
    exact (congrArg (d.fourier v) h).trans h'
  let A (Ψ : ∀ v, d.schwartz v) (t : Fˣ) := ∏ᶠ v, d.axis v (Ψ v) (atPlace v t)
  let M (Ψ : ∀ v, d.schwartz v) (t : Fˣ) := ∏ᶠ v, d.marginal v (Ψ v) (atPlace v t)
  let Q : Fˣ →* GlobalClass n F := QuotientGroup.mk' (powMonoidHom n : Fˣ →* Fˣ).range
  let Z (c : GlobalClass n F) := ∏ᶠ v, d.axisLine v (Φ v) (atPlace v c.out) 0
  let β (c : GlobalClass n F) := ∏ᶠ v, d.axisClassIntegral v (Φ v) (QuotientGroup.mk (atPlace v c.out))
  have hM : HasSum (fun c : GlobalClass n F => ∑' t : Fˣ, M Φ (t^n / c.out))
      ((n:ℂ) * ∑' a, M Φ a) := by
    have rep (c : GlobalClass n F) : Q c.out⁻¹ = (Equiv.inv (GlobalClass n F)) c :=
      (map_inv Q _).trans (congrArg Inv.inv (Quotient.out_eq c))
    apply (d.hasSum_powerClass_representatives (M Φ) (d.summable_rational_marginal Φ hΦ).of_norm _ _ rep).congr_fun
    intro c
    exact tsum_congr fun t => congrArg (M Φ) (by rw [div_eq_mul_inv,mul_comm])
  have hMd : HasSum (fun c : GlobalClass n F => ∑' t : Fˣ, M dual (t^n * (-1 / c.out)))
      ((n:ℂ) * ∑' a, M dual a) := by
    have rep (c : GlobalClass n F) : Q (-1/c.out) = Equiv.divLeft (Q (-1)) c :=
      (map_div Q _ _).trans (congrArg (Q (-1) / ·) (Quotient.out_eq c))
    apply (d.hasSum_powerClass_representatives (M dual) (d.summable_rational_marginal dual hd).of_norm _ _ rep).congr_fun
    intro c
    exact tsum_congr fun t => congrArg (M dual) (mul_comm ..)
  have hZ : HasSum Z ((n:ℂ)*d.axisBoundary dual + (n:ℂ)*(∑' a, A dual a) - (n:ℂ)*∑' a, M Φ a) := by
    apply (((d.hasSum_leading_classes dual hd).add (d.hasSum_axis_powerClasses dual hd).1).sub hM).congr_fun
    intro c
    exact eq_sub_iff_add_eq.mpr (d.axisLine_poisson Φ hΦ c.out)
  have hB : HasSum β ((n:ℂ)*d.axisBoundary Φ + (n:ℂ)*(∑' a, A Φ a) - (n:ℂ)*∑' a, M dual a) := by
    apply (((d.hasSum_leading_classes Φ hΦ).add (d.hasSum_axis_powerClasses Φ hΦ).1).sub hMd).congr_fun
    intro c
    have zero : (∏ᶠ v, d.hat v (d.axisDensity v (Φ v) (atPlace v (-1/c.out))) 0) = β c := by
      apply finprod_congr
      intro v
      rw [d.axisClassIntegral_eq_integral_density]
      simp only [atPlace,map_div,Units.map_neg,map_one,hat,zero_mul,Character.localValue_zero,mul_one]
    have H := d.axisDensity_poisson Φ hΦ (-1/c.out)
    rw [zero,div_div_cancel] at H
    have arg (t : Fˣ) : -(t^n) / (-1/c.out) = t^n*c.out := by simp [div_eq_mul_inv]
    simp_rw [arg] at H
    exact eq_sub_iff_add_eq.mpr H.symm
  have balance := hB.tsum_eq.symm.trans ((d.axisClassIntegral_sum_eq_axisLine_zero Φ
    (fun v => d.integrable_axis v _) (d.eventually_axisClassIntegral_basic Φ hΦ)).trans hZ.tsum_eq)
  change ((∑' a, A Φ a) + (∑' a, M Φ a)) + d.axisBoundary Φ =
    ((∑' a, A dual a) + (∑' a, M dual a)) + d.axisBoundary dual
  apply mul_left_cancel₀ (NeZero.ne (n:ℂ))
  linear_combination balance

end MetaplecticPoisson.Datum
