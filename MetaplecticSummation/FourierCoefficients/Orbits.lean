import MetaplecticSummation.FourierCoefficients.Periodization

/-! The rational upper-unipotent orbits in the constant and nonconstant coefficients. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField Filter MeasureTheory IsDedekindDomain
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- Coordinates for rational points on the fixed axis and the nonzero unipotent orbits. -/
def rationalShearOrbits (F : Type) [Field F] :
    Fˣ ⊕ (Fˣ × F) ≃ RationalPoint F where
  toFun
    | .inl y => ⟨(0,y.val),fun he => y.ne_zero (congrArg Prod.snd he)⟩
    | .inr (x,t) => ⟨(x.val,x.val*t),fun he => x.ne_zero (congrArg Prod.fst he)⟩
  invFun p := if h : p.val.1 = 0 then
      Sum.inl (Units.mk0 p.val.2 (fun hz => p.property (Prod.ext h hz)))
    else Sum.inr (Units.mk0 p.val.1 h, p.val.2 / p.val.1)
  left_inv := by
    rintro (y|⟨x,t⟩)
    · simp
    · simp [x.ne_zero]
  right_inv p := by
    apply Subtype.ext
    by_cases h : p.val.1 = 0
    · simp only [dite_eq_left h]
      exact Prod.ext h.symm rfl
    · simp only [dite_eq_right h]
      exact Prod.ext rfl (by change p.val.1 * (p.val.2 / p.val.1) = p.val.2; field_simp)

/-- The X-chart product on one rational horizontal coordinate, parametrized
by slope so that rational translations add to the adelic parameter. -/
def adelicSlopeSlice (Φ : ∀ v, d.schwartz v) (x : Fˣ) (u : Adeles F) : ℂ :=
  ∏ᶠ v, (Φ v).val.1 (atPlace v x) ((atPlace v x).val * component u v)

private theorem translated_axis (Φ : ∀ v, d.schwartz v) (u : Adeles F) (y : Fˣ) :
    d.translatedValue Φ u (rationalShearOrbits F (.inl y)) = ∏ᶠ v, d.axis v (Φ v) (atPlace v y) := by
  apply finprod_congr
  intro v
  simp [rationalShearOrbits,diagonalPoint,yChart,axis,atPlace]
  exact congrArg ((Φ v).val.2 0) (Units.ext rfl)

private theorem translated_slope (Φ : ∀ v, d.schwartz v) (u : Adeles F) (x : Fˣ) (t : F) :
    d.translatedValue Φ u (rationalShearOrbits F (.inr (x,t))) =
      d.adelicSlopeSlice Φ x (u + algebraMap F (Adeles F) t) := by
  apply finprod_congr
  intro v
  have h : diagonal F v x.val ≠ 0 := (map_ne_zero _).mpr x.ne_zero
  have e : component (u + algebraMap F (Adeles F) t) v = component u v + diagonal F v t := by cases v <;> rfl
  simp only [rationalShearOrbits,Equiv.coe_fn_mk,diagonalPoint,ne_eq,x.ne_zero,not_false_eq_true,ite_true,xChart,
    h,dite_true,map_mul,e,atPlace,Units.coe_map]
  rw [show Units.mk0 (diagonal F v x.val) h = atPlace v x from Units.ext rfl]
  apply congrArg ((Φ v).val.1 (atPlace v x))
  change diagonal F v x.val * diagonal F v t + component u v * diagonal F v x.val =
    diagonal F v x.val * (component u v + diagonal F v t)
  ring

theorem summable_translatedValue (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) (u : Adeles F) :
    Summable (fun p : RationalPoint F => ‖d.translatedValue Φ u p‖) := by
  choose g hg _ using fun v => d.exists_upper v (component u v)
  have h : ∀ᶠ v in cofinite, g v (Φ v) = d.basic v :=
    (hΦ.and (d.eventually_upper_basic u g hg)).mono fun v h => by rw [h.1,h.2]
  exact (d.summable_theta_pure _ h).congr fun p => congrArg norm (d.translatedValue_eq_upper u g hg Φ h p).symm

/-- Decompose the translated theta sum into the fixed axis and the nonzero
first-coordinate orbits of rational upper unipotents. -/
theorem translatedTheta_orbit_sum (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) (u : Adeles F) :
    d.translatedTheta Φ u = (∑' y : Fˣ, ∏ᶠ v, d.axis v (Φ v) (atPlace v y)) +
      ∑' x : Fˣ, ∑' t : F, d.adelicSlopeSlice Φ x (u + algebraMap F (Adeles F) t) := by
  let e := rationalShearOrbits F
  let f := d.translatedValue Φ u ∘ e
  have hs : Summable f := e.summable_iff.mpr (d.summable_translatedValue Φ hΦ u).of_norm
  rw [translatedTheta,← e.tsum_eq (d.translatedValue Φ u)]
  change (∑' a, f a) = _
  have hl : Summable (f ∘ Sum.inl) := hs.comp_injective Sum.inl_injective
  have hr : Summable (f ∘ Sum.inr) := hs.comp_injective Sum.inr_injective
  rw [hl.tsum_sum hr]
  change _ + (∑' z : Fˣ × F, (f ∘ Sum.inr) z) = _
  rw [hr.tsum_prod]
  congr 1
  · exact tsum_congr (d.translated_axis Φ u)
  · exact tsum_congr fun x => tsum_congr fun t => d.translated_slope Φ u x t

private theorem places_countable (F : Type) [Field F] [NumberField F] : Countable (Place F) := by
  let := GroundTheory.Global.countable_numberField F
  let : Countable (𝓞 F) := (show Function.Injective (fun a : 𝓞 F => (a : F)) from fun _ _ h => Subtype.ext h).countable
  have hI : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) :=
    fun I => IsNoetherian.noetherian I
  let := hI.countable
  let : Countable (Prime F) := (show Function.Injective (fun p : Prime F => p.asIdeal) from fun _ _ h => HeightOneSpectrum.ext_iff.mpr h).countable
  exact inferInstanceAs (Countable (InfinitePlace F ⊕ Prime F))

theorem eventually_slope_factor_one (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v)
    (x : Fˣ) (u : Adeles F) :
    ∀ᶠ v in cofinite, (Φ v).val.1 (atPlace v x) ((atPlace v x).val * component u v) = 1 := by
  apply eventually_place_of_finite
  filter_upwards [(Sum.inr_injective (α := InfinitePlace F)).tendsto_cofinite.eventually hΦ,
    eventually_tame (F := F) (n := n),eventually_diagonal_norm_one x.ne_zero,
    eventually_integral_component u] with p h ht hx hu
  change Φ (.inr p) = d.basic (.inr p) at h
  let v : Place F := .inr p
  have hxy : ‖(atPlace v x).val * component u v‖ ≤ 1 := by rw [norm_mul,show ‖(atPlace v x).val‖ = 1 from hx,one_mul]; exact hu
  have hval := d.basic_xChart_unit p ht (atPlace v x).val _ hx hxy
  rw [h]
  simpa only [xChart,dite_eq_left (atPlace v x).ne_zero,Units.mk0_val] using hval

theorem measurable_adelicSlopeSlice (Φ : ∀ v, d.schwartz v) (hΦ : ∀ᶠ v in cofinite, Φ v = d.basic v) (x : Fˣ) :
    Measurable (d.adelicSlopeSlice Φ x) := by
  let := places_countable F
  let f (v : Place F) (u : Adeles F) := (Φ v).val.1 (atPlace v x) ((atPlace v x).val * component u v)
  have hm (v) : Continuous (f v) := (d.continuous_schwartz_charts v _).1.comp
    (continuous_const.prodMk (continuous_const.mul (continuous_component v)))
  apply measurable_of_tendsto_metrizable' (atTop : Filter (Finset (Place F)))
    (fun S => (continuous_finsetProd S (fun v _ => hm v)).measurable)
  apply tendsto_pi_nhds.mpr
  intro u
  have fin : Function.HasFiniteMulSupport (fun v => f v u) := eventually_cofinite.mp (d.eventually_slope_factor_one Φ hΦ x u)
  change HasProd (fun v => f v u) (∏ᶠ v, f v u)
  rw [← (show (∏' v, f v u) = ∏ᶠ v, f v u from tprod_eq_finprod fin)]
  exact (multipliable_of_hasFiniteMulSupport fin).hasProd

end MetaplecticPoisson.Datum
