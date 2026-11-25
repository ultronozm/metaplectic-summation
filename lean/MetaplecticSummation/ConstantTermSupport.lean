import MetaplecticSummation.PowerClassPoisson
import MetaplecticSummation.TransformedMarginals
import MetaplecticSummation.PowerClassIntegrals

/-! Finite support on rational power classes for the marginal and the leading term. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain Filter
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

include d in
/-- Only finitely many rational classes have integral-unit classes away from a fixed finite set. -/
theorem finite_classes_integral_away (S : Finset (Prime F)) :
    {c : GlobalClass n F | ∀ p ∉ S,
      (QuotientGroup.mk (atPlace (.inr p) c.out) : PowerClass n (.inr p)) ∈ integralUnitClasses p n}.Finite := by
  let β : (v : Place F) → PowerClass n v → ℂ := fun v => match v with
    | .inl _ => 1
    | .inr p => if p ∈ S then 1 else unitClassTest p n
  have hb : ∀ᶠ p : Prime F in cofinite, β (.inr p) = unitClassTest p n :=
    S.eventually_cofinite_notMem.mono (fun p hp => ite_eq_right hp)
  apply (d.powerClass_poisson_finite_support β hb).1.subset
  intro c hc
  change (∏ᶠ v, β v (QuotientGroup.mk (atPlace v c.out))) ≠ 0
  rw [finprod_eq_one_of_forall_eq_one]
  · exact one_ne_zero
  intro v
  cases v with
  | inl w => rfl
  | inr p =>
    by_cases h : p ∈ S
    · simp [β,h]
    · simp only [β,ite_eq_right h,unitClassTest,ite_eq_left (hc p h)]

theorem axisDensity_basic_zero_of_not_unitClass (p : Prime F) (hp : p.asIdeal.absNorm.Coprime n)
    (a : (LocalField F (.inr p))ˣ) (ha : (QuotientGroup.mk a : PowerClass n (.inr p)) ∉ integralUnitClasses p n) :
    d.axisDensity (.inr p) (d.basic (.inr p)) a = 0 := by
  let v : Place F := .inr p
  let H := integralUnitClasses p n
  let q := QuotientGroup.mk' (powMonoidHom n : (LocalField F v)ˣ →* _).range
  let g := d.axisDensity (.inr p) (d.basic (.inr p)) a
  have away (u : (LocalField F v)ˣ) : g u = 0 := by
    rw [show g u = _ from d.axisDensity_unit v _ a u]
    rw [d.axis_basic_zero_of_not_unitClass p hp, mul_zero]
    intro h
    have he : q (-(u^n)/a) = q (-1) / q a := by
      rw [← neg_one_mul, map_div,map_mul,show q (u^n) = 1 from (QuotientGroup.eq_one_iff _).mpr ⟨u,rfl⟩]
      exact congrArg (fun c : PowerClass n v => c / q a) (mul_one (q (-1)))
    change q (-(u^n)/a) ∈ H at h
    rw [he] at h
    have hn : q (-1) ∈ H := ⟨-1,by change ‖((-1 : (LocalField F v)ˣ).val)‖ = 1; simp,rfl⟩
    have hh : q a ∈ H := (div_div_cancel (q (-1)) (q a)) ▸ H.div_mem hn h
    exact ha hh
  funext t
  change g t = 0
  by_cases ht : t = 0
  · subst t
    let : NontriviallyNormedField (LocalField F v) := FinitePlace.nontriviallyNormedCompletion p
    let : (𝓝[≠] (0 : LocalField F v)).NeBot := NormedField.nhdsNE_neBot _
    have hg : IsLocallyConstant g := (d.axisDensity_finite_bruhat p _ a).1
    obtain ⟨t,ht,he⟩ := Filter.nonempty_of_mem (f := 𝓝[≠] (0 : LocalField F v))
      (inter_mem (self_mem_nhdsWithin (s := {0}ᶜ)) (mem_nhdsWithin_of_mem_nhds (hg.eventually_eq 0)))
    exact he.symm.trans (away (Units.mk0 t ht))
  · exact away (Units.mk0 t ht)

/-- At almost all finite places the marginal of the basic vector vanishes
outside the classes represented by integral units. -/
theorem eventually_marginal_basic_zero :
    ∀ᶠ p : Prime F in cofinite, ∀ a : (LocalField F (.inr p))ˣ,
      (QuotientGroup.mk a : PowerClass n (.inr p)) ∉ integralUnitClasses p n →
        d.marginal (.inr p) (d.basic (.inr p)) a = 0 := by
  have fixed := (Sum.inr_injective (α := InfinitePlace F)).tendsto_cofinite.eventually d.eventually_fourier_basic
  filter_upwards [fixed,eventually_tame (F := F) (n := n)] with p hp ht
  intro a ha
  have h := d.reverse_marginal (.inr p) (d.basic (.inr p)) a 1
  rw [one_pow,one_mul,hp,d.axisDensity_basic_zero_of_not_unitClass p ht a ha] at h
  simpa [hat] using h

set_option backward.isDefEq.respectTransparency true in
private theorem marginal_factors_eventually_one (Φ : ∀ v, d.schwartz v)
    (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) (a : Fˣ) :
    ∀ᶠ w in cofinite, d.marginal w (Φ w) (atPlace w a) = 1 := by
  refine eventually_place_of_finite (F := F) (P := fun w => d.marginal w (Φ w) (atPlace w a) = 1) ?_
  have base := (Sum.inr_injective (α := InfinitePlace F)).tendsto_cofinite.eventually hΦ
  filter_upwards [base,eventually_tame (F := F) (n := n),eventually_diagonal_norm_one a.ne_zero,
    d.eventually_selfDual_volume_one] with p hf ht hu hv
  change Φ (.inr p) = d.basic (.inr p) at hf
  change ‖(atPlace (.inr p) a).val‖ = 1 at hu
  rw [hf,d.marginal_basic_unit p ht _ hu,hv,Complex.ofReal_one]

include d in
/-- Outside finitely many rational classes, any restricted product supported
locally on the integral-unit classes vanishes. -/
private theorem supported_on_finite_classes
    (f : (v : Place F) → (LocalField F v)ˣ → ℂ)
    (h₁ : ∀ a : Fˣ, ∀ᶠ v in cofinite, f v (atPlace v a) = 1)
    (h₀ : ∀ᶠ p : Prime F in cofinite, ∀ a : (LocalField F (.inr p))ˣ,
      (QuotientGroup.mk a : PowerClass n (.inr p)) ∉ integralUnitClasses p n → f (.inr p) a = 0) :
    ∃ C : Finset (GlobalClass n F), ∀ a : Fˣ,
      (∏ᶠ v, f v (atPlace v a)) ≠ 0 → QuotientGroup.mk a ∈ C := by
  let S := (eventually_cofinite.mp h₀).toFinset
  let C := d.finite_classes_integral_away S
  refine ⟨C.toFinset,fun a h => C.mem_toFinset.mpr ?_⟩
  intro p hp
  let v : Place F := .inr p
  let loc := (adelicClassAt n v).comp (rationalClassMap n F)
  have he := congrArg loc (Quotient.out_eq (QuotientGroup.mk a : GlobalClass n F))
  change (QuotientGroup.mk (atPlace v (QuotientGroup.mk a : GlobalClass n F).out) : PowerClass n v) =
    QuotientGroup.mk (atPlace v a) at he
  rw [he]
  by_contra hc
  have hg := not_not.mp (fun hn => hp ((eventually_cofinite.mp h₀).mem_toFinset.mpr hn))
  exact h (finprod_eq_zero (fun w => f w (atPlace w a)) (.inr p) (hg _ hc) (eventually_cofinite.mp (h₁ a)))

theorem rational_marginal_supported_on_finite_classes (Φ : ∀ v, d.schwartz v)
    (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) :
    ∃ C : Finset (GlobalClass n F), ∀ a : Fˣ,
      (∏ᶠ v, d.marginal v (Φ v) (atPlace v a)) ≠ 0 → QuotientGroup.mk a ∈ C := by
  apply d.supported_on_finite_classes _ (d.marginal_factors_eventually_one Φ hΦ)
  filter_upwards [(Sum.inr_injective (α := InfinitePlace F)).tendsto_cofinite.eventually hΦ,
    d.eventually_marginal_basic_zero] with p hp h a ha
  exact (congrArg (fun f => d.marginal (.inr p) f a) hp).trans (h a ha)

theorem density_zero_supported_on_finite_classes (Φ : ∀ v, d.schwartz v)
    (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) :
    ∃ C : Finset (GlobalClass n F), ∀ a : Fˣ,
      (∏ᶠ v, d.axisDensity v (Φ v) (atPlace v a) 0) ≠ 0 → QuotientGroup.mk a ∈ C := by
  apply d.supported_on_finite_classes (fun v a => d.axisDensity v (Φ v) a 0)
  · intro a
    apply eventually_place_of_finite
    filter_upwards [d.eventually_axisDensity_basic Φ hΦ a] with p h
    simpa only [norm_zero,zero_le_one,ite_true] using h 0
  · filter_upwards [(Sum.inr_injective (α := InfinitePlace F)).tendsto_cofinite.eventually hΦ,
      eventually_tame (F := F) (n := n)] with p hp ht a ha
    change Φ (.inr p) = d.basic (.inr p) at hp
    rw [hp,d.axisDensity_basic_zero_of_not_unitClass p ht a ha]
    rfl

end MetaplecticPoisson.Datum
