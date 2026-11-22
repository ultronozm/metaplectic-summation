import MetaplecticSummation.AdeleLattice
import MetaplecticSummation.MarginalDifference

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain MeasureTheory Filter
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- Finitely supported normalizing factors whose product over the places is one. -/
private def normalizations (F : Type) [Field F] [NumberField F] : Submonoid (Place F → ℂ) where
  carrier := {g | (∀ᶠ v in cofinite, g v = 1) ∧ ∏ᶠ v, g v = 1}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨ha,pa⟩ ⟨hb,pb⟩
    refine ⟨?_,(finprod_mul_distrib (eventually_cofinite.mp ha) (eventually_cofinite.mp hb)).trans ?_⟩
    · filter_upwards [ha,hb] with v h₁ h₂
      simp [h₁,h₂]
    · rw [pa,pb,mul_one]

private theorem normalization_map {g : Place F → ℂ} (hg : g ∈ normalizations F) (e : ℂ →* ℂ) :
    (fun v => e (g v)) ∈ normalizations F := by
  obtain ⟨hf,hp⟩ := hg
  refine ⟨hf.mono (fun _ hv => (congrArg e hv).trans e.map_one),?_⟩
  rw [← e.map_finprod (eventually_cofinite.mp hf),hp,e.map_one]

private theorem modulus_normalization (x : Fˣ) :
    (fun v => (modulus F v (atPlace v x) : ℂ)) ∈ normalizations F := by
  let m (v : Place F) := modulus F v (diagonal F v x.val)
  have hf : ∀ᶠ v in cofinite, m v = 1 :=
    eventually_place_of_finite (P := fun v => m v = 1) (eventually_diagonal_norm_one x.ne_zero)
  refine ⟨hf.mono (fun v hv => (congrArg Complex.ofReal hv).trans Complex.ofReal_one),?_⟩
  change (∏ᶠ v, Complex.ofRealHom.toMonoidHom (m v)) = 1
  rw [← MonoidHom.map_finprod _ (eventually_cofinite.mp hf),
    show finprod m = 1 from diagonal_modulus_product x.ne_zero,map_one]

private theorem fourier_normalization :
    (fun v : Place F => (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹) ∈ normalizations F := by
  refine ⟨eventually_place_of_finite ?_,transform_normalization_product⟩
  filter_upwards [eventually_diagonal_norm_one (F := F) (Nat.cast_ne_zero.mpr (NeZero.ne n))] with p hp
  rw [map_natCast] at hp
  simp [modulus,hp]

private theorem remove_normalization {g : Place F → ℂ} (hg : g ∈ normalizations F) (f : Place F → ℂ) :
    (∏ᶠ v, g v * f v) = ∏ᶠ v, f v := by
  obtain ⟨h₁,hp⟩ := hg
  by_cases hf : Function.HasFiniteMulSupport f
  · rw [finprod_mul_distrib (eventually_cofinite.mp h₁) hf,hp,one_mul]
  · rw [finprod_of_not_hasFiniteMulSupport hf,finprod_of_not_hasFiniteMulSupport]
    intro he
    apply hf
    apply eventually_cofinite.mp
    filter_upwards [h₁,eventually_cofinite.mpr he] with v h₁ hv
    simpa only [h₁,one_mul] using hv

private theorem axisLine_normalization (y : Fˣ) :
    (fun v => d.symbol v (-1) (atPlace v y) / (modulus F v (atPlace v y) : ℂ)) ∈ normalizations F := by
  simp_rw [div_eq_mul_inv]
  apply (normalizations F).mul_mem _ (normalization_map (modulus_normalization y) invMonoidHom)
  change (∀ᶠ v in cofinite, d.symbol v (-1) (atPlace v y) = 1) ∧
    ∏ᶠ v, d.symbol v (-1) (atPlace v y) = 1
  simpa only [atPlace,Units.map_neg,map_one] using d.symbol_reciprocity (-1) y

/-- The product of the vertical line kernels at a nonzero rational parameter. -/
theorem axisLine_product (Φ : ∀ v, d.schwartz v) (y t : Fˣ) :
    (∏ᶠ v, d.axisLine v (Φ v) (atPlace v y) (atPlace v t)) =
      ∏ᶠ v, d.marginal v (Φ v) (atPlace v (t^n/y)) := by
  simp_rw [d.axisLine_unit,atPlace,map_div,map_pow]
  exact remove_normalization (d.axisLine_normalization y) _

/-- At zero the remaining factors are the Hilbert-symbol-weighted axis integrals
that enter the power-class Poisson sum. -/
theorem axisLine_zero_product (Φ : ∀ v, d.schwartz v) (y : Fˣ) :
    (∏ᶠ v, d.axisLine v (Φ v) (atPlace v y) 0) =
      ∏ᶠ v, ∫ z, if hz : z ≠ 0 then d.symbol v (Units.mk0 z hz) (atPlace v y) *
        d.axis v (Φ v) (Units.mk0 z hz) else 0 ∂(selfDual F d.character v) := by
  simp_rw [d.axisLine_zero]
  exact remove_normalization (d.axisLine_normalization y) _

/-- The local densities at zero give exactly the global leading-term axis value. -/
theorem axisDensity_zero_product (Φ : ∀ v, d.schwartz v) (x : Fˣ) :
    (∏ᶠ v, d.axisDensity v (Φ v) (atPlace v x) 0) =
      ∏ᶠ v, (d.leading v (Φ v)).2 0 (atPlace v (-1/x)) := by
  let N := Units.mk0 (n : F) (Nat.cast_ne_zero.mpr (NeZero.ne n))
  have hn (v : Place F) : (atPlace v N).val = (n : LocalField F v) := map_natCast (diagonal F v) n
  have h (v : Place F) : atPlace v (-1/x) = -1 / atPlace v x := by simp [atPlace]
  simp_rw [d.axisDensity_zero,h,← hn,div_eq_mul_inv (modulus F _ _ : ℂ)]
  exact remove_normalization ((normalizations F).mul_mem (modulus_normalization N)
    (normalization_map (modulus_normalization x) invMonoidHom)) _

/-- At nonzero rational parameters the product of densities is an axis value. -/
theorem axisDensity_product (Φ : ∀ v, d.schwartz v) (x t : Fˣ) :
    (∏ᶠ v, d.axisDensity v (Φ v) (atPlace v x) (atPlace v t)) =
      ∏ᶠ v, d.axis v (Φ v) (atPlace v (-(t^n)/x)) := by
  let N := Units.mk0 (n : F) (Nat.cast_ne_zero.mpr (NeZero.ne n))
  have hn (v : Place F) : (atPlace v N).val = (n : LocalField F v) := map_natCast (diagonal F v) n
  have h (v : Place F) : atPlace v (-(t^n)/x) = -(atPlace v t)^n / atPlace v x := by simp [atPlace]
  simp_rw [d.axisDensity_unit,h,← hn,div_eq_mul_inv (modulus F _ _ : ℂ)]
  exact remove_normalization ((normalizations F).mul_mem ((normalizations F).mul_mem (modulus_normalization N)
    (normalization_map (modulus_normalization x) invMonoidHom))
    (normalization_map (modulus_normalization t) (powMonoidHom (n-1)))) _

/-- On the transformed side the product of the ordinary local Fourier integrals
is the axis value of the transformed tensor. -/
theorem axisLine_hat_product (Φ : ∀ v, d.schwartz v) (y u : Fˣ) :
    (∏ᶠ v, d.hat v (d.axisLine v (Φ v) (atPlace v y)) (atPlace v u)) =
      ∏ᶠ v, d.axis v (d.fourier v (Φ v)) (atPlace v (u^n*y)) := by
  have h (v : Place F) : atPlace v (u^n*y) = (atPlace v u)^n * atPlace v y := by simp [atPlace]
  simp_rw [h,d.axis_fourier]
  exact (remove_normalization ((normalizations F).mul_mem fourier_normalization
    (normalization_map (modulus_normalization u) (zpowGroupHom (1-(n : ℤ))))) _).symm

/-- The frequency-zero factors yield the axis value of the adelic leading term. -/
theorem axisLine_hat_zero_product (Φ : ∀ v, d.schwartz v) (y : Fˣ)
    (hi : ∀ v, Integrable (d.axisLine v (Φ v) (atPlace v y)) (selfDual F d.character v)) :
    (∏ᶠ v, d.hat v (d.axisLine v (Φ v) (atPlace v y)) 0) =
      ∏ᶠ v, (d.leading v (d.fourier v (Φ v))).2 0 (atPlace v y) := by
  simp_rw [← d.axisLine_hat_zero _ _ _ (hi _)]
  exact (remove_normalization fourier_normalization _).symm

/-- The reverse local identity gives the product of the Fourier transforms of
the densities at a rational frequency. -/
theorem axisDensity_hat_product (Φ : ∀ v, d.schwartz v) (x u : Fˣ) :
    (∏ᶠ v, d.hat v (d.axisDensity v (Φ v) (atPlace v x)) (atPlace v u)) =
      ∏ᶠ v, d.marginal v (d.fourier v (Φ v)) (atPlace v (u^n*x)) := by
  have he (v : Place F) := (d.schwartz_marginal_kernels v (Φ v) (atPlace v x) 1).2.2 (atPlace v u)
  have h (v : Place F) : atPlace v (u^n*x) = (atPlace v u)^n * atPlace v x := by simp [atPlace]
  simp_rw [h,he]
  exact (remove_normalization fourier_normalization _).symm

abbrev AdeleQuotient (F : Type) [Field F] [NumberField F] :=
  AdeleLattice.Quotient F

local instance : MeasurableSpace (AdeleQuotient F) := borel _
local instance : BorelSpace (AdeleQuotient F) := ⟨rfl⟩

theorem exists_quotient_measure :
    ∃! μ : Measure (AdeleQuotient F), μ.IsAddHaarMeasure ∧ IsProbabilityMeasure μ := by
  let C : TopologicalSpace.PositiveCompacts (AdeleQuotient F) := ⊤
  let μ := Measure.addHaarMeasure C
  letI : IsProbabilityMeasure μ := ⟨Measure.addHaarMeasure_self (K₀ := C)⟩
  refine ⟨μ,⟨inferInstance,inferInstance⟩,?_⟩
  rintro ν ⟨hH,hP⟩
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure ν μ

/-- The theta series at an upper unipotent translate, written in the common rational chart. -/
def translatedTheta (Φ : ∀ v, d.schwartz v) (u : Adeles F) : ℂ :=
  ∑' p : RationalPoint F, ∏ᶠ v,
    let z := diagonalPoint p v
    if p.val.1 ≠ 0 then xChart (Φ v) (z.1, z.2 + component u v * z.1) else yChart (Φ v) z

private def rationalShear (t : F) (p : RationalPoint F) : RationalPoint F :=
  ⟨(p.val.1,p.val.2+t*p.val.1),fun h => p.property (by
    have h₁ : p.val.1 = 0 := congrArg Prod.fst h
    exact Prod.ext h₁ (by simpa [h₁] using congrArg Prod.snd h))⟩

private def rationalShearEquiv (t : F) : RationalPoint F ≃ RationalPoint F where
  toFun := rationalShear t
  invFun := rationalShear (-t)
  left_inv p := by apply Subtype.ext; ext <;> simp [rationalShear]
  right_inv p := by apply Subtype.ext; ext <;> simp [rationalShear]

/-- Translating the unipotent parameter by a principal adele permutes the rational points. -/
theorem translatedTheta_add_diagonal (Φ : ∀ v, d.schwartz v) (u : Adeles F) (t : F) :
    d.translatedTheta Φ (u + algebraMap F (Adeles F) t) = d.translatedTheta Φ u := by
  let term (p : RationalPoint F) (u : Adeles F) (v : Place F) :=
    let z := diagonalPoint p v
    if p.val.1 ≠ 0 then xChart (Φ v) (z.1,z.2 + component u v*z.1) else yChart (Φ v) z
  change (∑' p, ∏ᶠ v, term p (u + algebraMap F (Adeles F) t) v) = ∑' p, ∏ᶠ v, term p u v
  rw [← (rationalShearEquiv t).tsum_eq (fun p => ∏ᶠ v, term p u v)]
  apply tsum_congr
  intro p
  apply finprod_congr
  intro v
  have hc : component (u + algebraMap F (Adeles F) t) v = component u v + diagonal F v t := by
    cases v <;> rfl
  by_cases hp : p.val.1 = 0
  · simp [term,rationalShearEquiv,rationalShear,diagonalPoint,hp]
  · simp only [term,rationalShearEquiv,rationalShear,Equiv.coe_fn_mk,diagonalPoint,hp,ne_eq,not_false_eq_true,
      if_true,hc,map_add,map_mul,add_mul]
    congr 2
    ring

/-- The integrand of the Fourier coefficient has the same value at every
representative of a class modulo the diagonal field. -/
def quotientIntegrand (Φ : ∀ v, d.schwartz v) (a : F) : AdeleQuotient F → ℂ :=
  Quotient.lift (fun u : Adeles F => d.translatedTheta Φ u * (d.character.toChar (-(algebraMap F (Adeles F) a * u)) : ℂ))
    (by
      intro u w h
      have he : (-u + w) ∈ AdeleRing.principalSubgroup (𝓞 F) F := QuotientAddGroup.leftRel_apply.mp h
      obtain ⟨t,ht⟩ := he
      have hw : w = u + algebraMap F (Adeles F) t := by rw [ht]; abel
      rw [hw,d.translatedTheta_add_diagonal, mul_add,neg_add,← map_mul,← map_neg,AddChar.map_add_eq_mul,
        d.character.trivial_diagonal,mul_one])

@[simp] theorem quotientIntegrand_mk (Φ : ∀ v, d.schwartz v) (a : F) (u : Adeles F) :
    d.quotientIntegrand Φ a (QuotientAddGroup.mk u) =
      d.translatedTheta Φ u * (d.character.toChar (-(algebraMap F (Adeles F) a * u)) : ℂ) := rfl

def coefficient (Φ : ∀ v, d.schwartz v) (a : F) : ℂ :=
  ∫ q : AdeleQuotient F, d.quotientIntegrand Φ a q
    ∂(exists_quotient_measure (F := F)).exists.choose

def constantTerm (Φ : ∀ v, d.schwartz v) :=
  (∑' y : Fˣ, ∏ᶠ v, d.axis v (Φ v) (atPlace v y)) +
    ∑' x : Fˣ, ∏ᶠ v, d.marginal v (Φ v) (atPlace v x)

theorem unfolding (Φ : ∀ v, d.schwartz v) (h : ∀ᶠ v in cofinite, Φ v = d.basic v) :
    d.coefficient Φ 0 = d.constantTerm Φ ∧
    Summable (fun c : Fˣ => ‖∏ᶠ v, d.jacquet v (Φ v) (atPlace v c)‖) ∧
    d.coefficient Φ 1 = ∑' c : Fˣ, ∏ᶠ v, d.jacquet v (Φ v) (atPlace v c) := by sorry

abbrev GlobalClass (n : ℕ) (F : Type) [Field F] := Fˣ ⧸ (powMonoidHom n : Fˣ →* Fˣ).range

/-- Appendix B's Poisson formula on multiplicative power classes. -/
theorem powerClass_poisson (β : (v : Place F) → PowerClass n v → ℂ)
    (hβ : ∀ᶠ p : HeightOneSpectrum (𝓞 F) in cofinite, ∀ c, β (.inr p) c =
      if ∃ u : (LocalField F (.inr p))ˣ, ‖(u : LocalField F (.inr p))‖ = 1 ∧
        QuotientGroup.mk u = c then 1 else 0) :
    let eval := fun (v : Place F) (x : GlobalClass n F) =>
      (QuotientGroup.mk (atPlace v x.out) : PowerClass n v)
    let dual := fun (v : Place F) (y : PowerClass n v) =>
      (n : ℂ)⁻¹ * ∑ᶠ c : PowerClass n v, d.symbol v c.out y.out * β v c
    (∑' x : GlobalClass n F, ∏ᶠ v, β v (eval v x)) =
      ∑' y : GlobalClass n F, ∏ᶠ v, dual v (eval v y) := by sorry

def axisBoundary (Φ : ∀ v, d.schwartz v) :=
  (n : ℂ)⁻¹ * ∑ᶠ y : GlobalClass n F, ∏ᶠ v,
    (d.leading v (Φ v)).2 0 (atPlace v y.out)

theorem constantTerm_identity (Φ : ∀ v, d.schwartz v) (h : ∀ᶠ v in cofinite, Φ v = d.basic v) :
    let dual := fun v => d.fourier v (Φ v)
    d.constantTerm Φ + d.axisBoundary Φ = d.constantTerm dual + d.axisBoundary dual := by sorry

end MetaplecticPoisson.Datum
