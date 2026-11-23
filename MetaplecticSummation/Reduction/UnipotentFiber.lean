import MetaplecticSummation.Reduction.OrbitIntegral
import MetaplecticSummation.FourierCoefficients.Periodization

/-! The adelic upper unipotent acts on the rational unipotent quotient. Its orbits
are parametrized by the compact additive quotient of the adeles. -/
noncomputable section
namespace MetaplecticPoisson
open MeasureTheory Set Topology NumberField
open scoped Matrix MatrixGroups Pointwise ENNReal
open Classical
variable (F : Type) [Field F] [NumberField F]
local notation "A" => Adeles F
local notation "G" => AdelicSL F
local notation "H" => rationalUnipotents F
local notation "Y" => UnipotentArithmeticQuotient F
local notation "ρ" => (Quotient.mk _ : G → Y)

abbrev adelicUpper (u : A) : G := upperUnipotentParam (Multiplicative.ofAdd u)

theorem adelicUpper_add (u v : A) : adelicUpper F (u+v) = adelicUpper F u * adelicUpper F v :=
  map_mul upperUnipotentParam (Multiplicative.ofAdd u) (Multiplicative.ofAdd v)

theorem adelicUpper_diagonal (x : F) :
    adelicUpper F (algebraMap F A x) = rationalSLMap F (upperUnipotentParam (Multiplicative.ofAdd x)) := by
  apply Subtype.ext
  change _ = Matrix.map _ (algebraMap F A)
  rw [show (adelicUpper F (algebraMap F A x)).val = _ from upperTransvection_matrix _, show (upperUnipotentParam (Multiplicative.ofAdd x)).val = _ from upperTransvection_matrix x]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem adelicUpper_commute (u : A) (h : H) : Commute (adelicUpper F u) h.val := by
  obtain ⟨_, _, ⟨x,rfl⟩, rfl⟩ := h
  change Commute (adelicUpper F u) (rationalSLMap F (upperUnipotentParam x))
  have hx : rationalSLMap F (upperUnipotentParam x) = adelicUpper F (algebraMap F A x.toAdd) :=
    (adelicUpper_diagonal F x.toAdd).symm
  rw [hx]
  exact (Commute.all (Multiplicative.ofAdd u) (Multiplicative.ofAdd (algebraMap F A x.toAdd))).map upperUnipotentParam

theorem continuous_adelicUpper : Continuous (adelicUpper F) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun u : A => (adelicUpper F u).val i j)
  have matrix (u : A) : (adelicUpper F u).val = !![1,u;0,1] := upperTransvection_matrix u
  simp_rw [matrix]
  fin_cases i <;> fin_cases j <;> first | exact continuous_id | exact continuous_const

def unipotentTranslate (u : A) : Y → Y :=
  Quotient.lift (fun x : G => ρ (adelicUpper F u * x)) fun x y h => by
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    have hr := QuotientGroup.rightRel_apply.mp h
    have hc := (adelicUpper_commute F u ⟨y*x⁻¹, hr⟩).eq
    change adelicUpper F u * (y*x⁻¹) = _ at hc
    suffices adelicUpper F u * y * (adelicUpper F u * x)⁻¹ = y*x⁻¹ by rwa [this]
    rw [mul_inv_rev, mul_assoc, ← mul_assoc y, ← mul_assoc, hc, mul_inv_cancel_right]

theorem measurable_unipotentTranslate (u : A) : Measurable (unipotentTranslate F u) :=
  measurable_from_quotient.mpr (measurable_quotient_mk''.comp (continuous_const_mul _).measurable)

theorem measurePreserving_unipotentTranslate (μ : Measure G) [μ.IsMulLeftInvariant] (u : A) :
    MeasurePreserving (unipotentTranslate F u) (unipotentQuotientMeasure F μ) (unipotentQuotientMeasure F μ) := by
  let a := adelicUpper F u
  let D := rationalUnipotentDomain F
  have hD := isFundamentalDomain_rationalUnipotents F μ
  have translated : IsFundamentalDomain H ((a * ·) '' D) μ :=
    hD.image_of_equiv (Equiv.mulLeft a) (measurePreserving_mul_left μ a⁻¹).quasiMeasurePreserving
      (Equiv.refl H) fun h x => (adelicUpper_commute F u h).left_comm x
  refine ⟨measurable_unipotentTranslate F u, ?_⟩
  unfold unipotentQuotientMeasure
  rw [Measure.map_map (measurable_unipotentTranslate F u) measurable_quotient_mk'']
  change ((μ.restrict D).map (ρ ∘ (a * ·))) = _
  rw [← Measure.map_map measurable_quotient_mk'' (continuous_const_mul a).measurable,
    ((measurePreserving_mul_left μ a).restrict_image_emb (Homeomorph.mulLeft a).measurableEmbedding D).map_eq]
  exact rightCoset_map_restrict_eq F translated hD


abbrev AdelicUnipotentQuotient := Quotient (QuotientGroup.rightRel (upperUnipotent A))
local notation "Z" => AdelicUnipotentQuotient F
local notation "T" => Datum.AdeleQuotient F
local notation "π" => (Quotient.mk _ : G → Z)
local notation "p" => (QuotientAddGroup.mk : A → T)
local notation "η" => Exists.choose (ExistsUnique.exists (Datum.exists_quotient_measure (F := F)))
local instance : MeasurableSpace T := borel _
local instance : BorelSpace T := ⟨rfl⟩

private theorem rationalUnipotents_le : H ≤ upperUnipotent A := by
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  exact ⟨Multiplicative.ofAdd (algebraMap F A t.toAdd), adelicUpper_diagonal F t.toAdd⟩

def adelicUnipotentProjection : Y → Z :=
  Quotient.lift π fun _ _ h => Quotient.sound
    (QuotientGroup.rightRel_apply.mpr (rationalUnipotents_le F (QuotientGroup.rightRel_apply.mp h)))

theorem measurable_adelicUnipotentProjection : Measurable (adelicUnipotentProjection F) :=
  measurable_from_quotient.mpr measurable_quotient_mk''

def adelicUnipotentQuotientMeasure (μ : Measure G) : Measure Z :=
  (unipotentQuotientMeasure F μ).map (adelicUnipotentProjection F)

/-- The fiber over the adelic unipotent orbit of a matrix, parametrized by 𝔸/F. -/
def unipotentFiber (x : G) : T → Y :=
  Quotient.lift (fun u : A => ρ (adelicUpper F u * x)) fun u v h => by
    obtain ⟨t,ht⟩ := QuotientAddGroup.leftRel_apply.mp h
    have hv : v = algebraMap F A t + u := by rw [ht]; abel
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    rw [hv, adelicUpper_add, mul_assoc (adelicUpper F _) (adelicUpper F u) x, mul_inv_cancel_right]
    exact ⟨_, ⟨Multiplicative.ofAdd t,rfl⟩, (adelicUpper_diagonal F t).symm⟩

theorem unipotentFiber_injective (x : G) : Function.Injective (unipotentFiber F x) := by
  intro q r
  induction q using Quotient.inductionOn with | _ u => _
  induction r using Quotient.inductionOn with | _ v => _
  intro h
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
  have eqn : adelicUpper F (algebraMap F A t.toAdd + u) * x = adelicUpper F v * x := by
    rw [adelicUpper_add, mul_assoc]
    exact (congrArg (· * (adelicUpper F u * x)) ((adelicUpper_diagonal F t.toAdd).trans ht)).trans
      (inv_mul_cancel_right _ _)
  have upperEntry (a : A) : (adelicUpper F a).val 0 1 = a :=
    congrArg (fun m : Matrix (Fin 2) (Fin 2) A => m 0 1) (upperTransvection_matrix a)
  have eqParam := congrArg (fun g : G => g.val 0 1) (mul_right_cancel eqn)
  change (adelicUpper F _).val 0 1 = (adelicUpper F v).val 0 1 at eqParam
  rw [upperEntry, upperEntry] at eqParam
  apply Quotient.sound
  apply QuotientAddGroup.leftRel_apply.mpr
  exact ⟨t.toAdd, by rw [← eqParam]; abel⟩

theorem range_unipotentFiber (x : G) :
    range (unipotentFiber F x) = (adelicUnipotentProjection F) ⁻¹' {π x} := by
  ext y
  induction y using Quotient.inductionOn with | _ g => _
  constructor
  · rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn with | _ u => _
    change adelicUnipotentProjection F (ρ g) = π x
    rw [← hq]
    exact Quotient.sound (QuotientGroup.rightRel_apply.mpr (by
      change x*(adelicUpper F u*x)⁻¹ ∈ upperUnipotent A
      rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
      exact (upperUnipotent A).inv_mem ⟨Multiplicative.ofAdd u, rfl⟩))
  · intro h
    change π g = π x at h
    obtain ⟨u, hu⟩ := QuotientGroup.rightRel_apply.mp (Quotient.exact h.symm)
    exact ⟨p u.toAdd, congrArg ρ (eq_mul_inv_iff_mul_eq.mp hu)⟩

private theorem fiber_mul (x : G) (v : A) (q : T) :
    unipotentFiber F (adelicUpper F v * x) q = unipotentFiber F x (q + p v) := by
  induction q using Quotient.inductionOn with | _ u => _
  change ρ (adelicUpper F u * (adelicUpper F v * x)) = ρ (adelicUpper F (u+v) * x)
  rw [adelicUpper_add,mul_assoc]

theorem measurable_unipotentFiber (x : G) : Measurable (unipotentFiber F x) :=
  Datum.measurable_of_quotientLift F (measurable_quotient_mk''.comp
    (((continuous_adelicUpper F).mul continuous_const).measurable))

def unipotentFiberLIntegral (f : Y → ℝ≥0∞) : Z → ℝ≥0∞ :=
  Quotient.lift (fun x : G => ∫⁻ q, f (unipotentFiber F x q) ∂η) fun x y h => by
    obtain ⟨v,hv⟩ := QuotientGroup.rightRel_apply.mp h
    have eqn : y = adelicUpper F v.toAdd * x := (eq_mul_inv_iff_mul_eq.mp hv).symm
    rw [eqn]
    simp_rw [fiber_mul]
    let : (η).IsAddHaarMeasure := (Datum.exists_quotient_measure (F := F)).exists.choose_spec.1
    exact (lintegral_add_right_eq_self (μ := η) (fun q => f (unipotentFiber F x q)) (p v.toAdd)).symm

def unipotentFiberIntegral (f : Y → ℂ) : Z → ℂ :=
  Quotient.lift (fun x : G => ∫ q, f (unipotentFiber F x q) ∂η) fun x y h => by
    obtain ⟨v,hv⟩ := QuotientGroup.rightRel_apply.mp h
    have eqn : y = adelicUpper F v.toAdd * x := (eq_mul_inv_iff_mul_eq.mp hv).symm
    rw [eqn]
    simp_rw [fiber_mul]
    let : (η).IsAddHaarMeasure := (Datum.exists_quotient_measure (F := F)).exists.choose_spec.1
    exact (integral_add_right_eq_self (μ := η) (fun q => f (unipotentFiber F x q)) (p v.toAdd)).symm

end MetaplecticPoisson
