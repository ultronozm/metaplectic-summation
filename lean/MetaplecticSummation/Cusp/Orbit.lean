import MetaplecticSummation.Cusp.Quotient
import MetaplecticSummation.Reduction.Vanishing

/-! Unfolding the square of the theta difference in Proposition B.6. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Filter Set
open scoped Matrix MatrixGroups ComplexConjugate ENNReal
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
local instance orbitSchwartzAddGroup : AddCommGroup d.Schwartz := Module.addCommMonoidToAddCommGroup ℂ
local notation "G" => AdelicSL F
local notation "X" => SLArithmeticQuotient F
local notation "Y" => UnipotentArithmeticQuotient F
local notation "ι" => rationalSLMap F

private def orbitValue (Φ : d.Schwartz) (p : RationalPoint F) :=
  d.evaluation Φ p * conj (d.theta Φ)

private theorem orbitValue_of_lift (Φ : d.Schwartz) {m : G} {g : ∀ v, d.cover v}
    (hg : d.IsRestrictedCover g) (pg : d.LiftsAdelicMatrix m g) (p : RationalPoint F) :
    d.orbitValue (d.liftedAction Φ m) p = d.orbitValue (d.coverAction g hg Φ) p := by
  obtain ⟨c,hc,e⟩ := d.coverAction_scalar_of_same_projection (d.exists_restricted_lift m).choose_spec.1 hg
    (d.exists_restricted_lift m).choose_spec.2 pg
  have h : c * conj c = 1 := by simp [Complex.mul_conj,Complex.normSq_eq_norm_sq,hc]
  simp only [orbitValue,liftedAction,e Φ,map_smul,Pi.smul_apply,smul_eq_mul,map_mul]
  linear_combination (d.evaluation (d.coverAction g hg Φ) p * conj (d.theta (d.coverAction g hg Φ))) * h

private theorem orbitValue_rational (Φ : d.Schwartz) (m : G) (γ : SL(2,F)) (p : RationalPoint F) :
    d.orbitValue (d.liftedAction Φ (ι γ*m)) p =
      d.orbitValue (d.liftedAction Φ m) (rationalRowPerm γ p) := by
  obtain ⟨r,hr,pr,ev,th⟩ := d.exists_rational_lift γ
  obtain ⟨hg,pg⟩ := (d.exists_restricted_lift m).choose_spec
  rw [d.orbitValue_of_lift Φ (hr.mul d hg) ((pr.adelic d).mul d pg),d.coverAction_mul _ _ hr hg]
  unfold orbitValue
  rw [ev,th]
  rfl

/-- The vertical evaluation times the conjugate theta value on the rational
unipotent quotient. The phase of the lift cancels between the factors. -/
def thetaOrbitIntegrand (Φ : d.Schwartz) : Y → ℂ :=
  Quotient.lift (fun m : G => d.orbitValue (d.liftedAction Φ m) (verticalPoint F)) (by
    intro a b h
    obtain ⟨γ,⟨t,rfl⟩,hγ⟩ := QuotientGroup.rightRel_apply.mp h
    rw [show b = ι (upperUnipotentParam t)*a from (eq_mul_inv_iff_mul_eq.mp hγ).symm,d.orbitValue_rational]
    have he : rationalRowPerm (upperUnipotentParam t) (verticalPoint F) = verticalPoint F := by
      apply Subtype.ext
      rw [rationalRowPerm_val,show (upperUnipotentParam t).val = _ from upperTransvection_matrix t.toAdd]
      simp [verticalPoint]
    rw [he])

theorem thetaOrbitIntegrand_mk (Φ : d.Schwartz) {m : G} {g : ∀ v, d.cover v}
    (hg : d.IsRestrictedCover g) (pg : d.LiftsAdelicMatrix m g) :
    d.thetaOrbitIntegrand Φ (Quotient.mk _ m) =
      d.evaluation (d.coverAction g hg Φ) (verticalPoint F) * conj (d.theta (d.coverAction g hg Φ)) :=
  d.orbitValue_of_lift Φ hg pg _

private theorem orbitTerm (Φ : d.Schwartz) (m : G) (q : RationalCosets F) :
    d.thetaOrbitIntegrand Φ (Quotient.mk _ (ι q.out*m)) =
      d.orbitValue (d.liftedAction Φ m) (rationalBottomRowEquiv q) := by
  change d.orbitValue _ _ = _
  rw [d.orbitValue_rational]
  exact congrArg (d.orbitValue _) (congrArg rationalBottomRowEquiv (Quotient.out_eq q))

private theorem liftedAction_sub_fourier (Φ : d.Schwartz) (m : G) :
    d.liftedAction (Φ-d.adelicFourier Φ) m = d.liftedAction Φ m - d.adelicFourier (d.liftedAction Φ m) := by
  dsimp only [liftedAction]
  rw [map_sub,d.coverAction_fourier]

private theorem theta_sub_fourier (Ψ : d.Schwartz) :
    d.theta (Ψ-d.adelicFourier Ψ) = d.thetaDifference Ψ := map_sub ..

/-- The rational orbit expansion of the unfolding integrand is exactly δ². -/
theorem arithmeticOrbitSum_thetaDifference (Φ : d.Schwartz) (x : X) :
    arithmeticOrbitSum F (d.thetaOrbitIntegrand (Φ-d.adelicFourier Φ)) x =
      ((((d.quotientThetaBounds Φ x).1)^2 : ℝ) : ℂ) := by
  induction x using Quotient.inductionOn with | _ m => _
  rw [arithmeticOrbitSum_mk]
  simp_rw [d.orbitTerm,d.liftedAction_sub_fourier]
  let Ψ := d.liftedAction Φ m
  change ∑' q, d.evaluation (Ψ-d.adelicFourier Ψ) (rationalBottomRowEquiv q) * conj (d.theta (Ψ-d.adelicFourier Ψ)) = _
  rw [tsum_mul_right,← (d.theta_coset_expansion _).2,d.theta_sub_fourier,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  rfl

/-- Absolute convergence in the unfolding is controlled pointwise by θδ. -/
theorem arithmeticOrbitSum_enorm_le (Φ : d.Schwartz) (x : X) :
    arithmeticOrbitSum F (fun y => ‖d.thetaOrbitIntegrand (Φ-d.adelicFourier Φ) y‖ₑ) x ≤
      ENNReal.ofReal ((d.quotientThetaBounds Φ x).2*(d.quotientThetaBounds Φ x).1) := by
  induction x using Quotient.inductionOn with | _ m => _
  let Ψ := d.liftedAction Φ m
  let Δ := Ψ-d.adelicFourier Ψ
  have hs := (d.summable_theta Ψ).add (d.summable_theta (d.adelicFourier Ψ))
  rw [arithmeticOrbitSum_mk]
  simp_rw [d.orbitTerm,d.liftedAction_sub_fourier]
  change ∑' q, ‖d.evaluation Δ (rationalBottomRowEquiv q) * conj (d.theta Δ)‖ₑ ≤ ENNReal.ofReal (d.thetaAbs Ψ * ‖d.thetaDifference Ψ‖)
  rw [← rationalBottomRowEquiv.symm.tsum_eq]
  simp only [Equiv.apply_symm_apply,enorm_mul,RCLike.enorm_conj,ENNReal.tsum_mul_right]
  rw [ENNReal.ofReal_mul (by exact tsum_nonneg fun p => add_nonneg (norm_nonneg _) (norm_nonneg _)),
    ← d.theta_sub_fourier,← ofReal_norm]
  apply mul_le_mul_left
  change (∑' p, ‖d.evaluation Δ p‖ₑ) ≤ ENNReal.ofReal (∑' p, (‖d.evaluation Ψ p‖ + ‖d.evaluation (d.adelicFourier Ψ) p‖))
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) hs]
  apply ENNReal.tsum_le_tsum
  intro p
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  dsimp only [Δ]
  rw [map_sub,Pi.sub_apply]
  exact norm_sub_le ..

private theorem vertical_upper (u : Adeles F) (Φ : d.Schwartz) :
    d.evaluation (d.coverAction (d.upperLift u) (d.upperLift_restricted u) Φ) (verticalPoint F) =
      d.evaluation Φ (verticalPoint F) := by
  let ev := (LinearMap.proj (R := ℂ) (φ := fun _ : RationalPoint F => ℂ) (verticalPoint F)).comp d.evaluation
  suffices eqn : ev.comp (d.coverAction (d.upperLift u) (d.upperLift_restricted u)) = ev from LinearMap.congr_fun eqn Φ
  apply d.ext_pure
  intro f hf
  change d.evaluation (d.coverAction _ _ (d.pure f hf)) _ = _
  rw [d.coverAction_pure,d.evaluation_pure]
  change _ = d.evaluation (d.pure f hf) (verticalPoint F)
  rw [d.evaluation_pure]
  apply finprod_congr
  intro v
  simpa [localValue,verticalPoint,diagonalPoint,yChart] using ((d.upperLift_isUpper u v (f v)).2 1)

local instance orbitAdeleQuotientMeasurable : MeasurableSpace (AdeleQuotient F) := borel _
local instance orbitAdeleQuotientBorel : BorelSpace (AdeleQuotient F) := ⟨rfl⟩
local notation "η" => Exists.choose (ExistsUnique.exists (exists_quotient_measure (F := F)))

/-- The inner integral in the unfolding vanishes at every matrix. -/
theorem integral_thetaOrbitIntegrand_fiber (Φ : ∀ v, d.schwartz v) (hf : ∀ᶠ v in cofinite, Φ v = d.basic v)
    (v t : Place F) (hv : d.leading v (Φ v) = 0) (ht : d.leading t (d.fourier t (Φ t)) = 0) (m : G) :
    ∫ q, d.thetaOrbitIntegrand (d.pure Φ hf - d.adelicFourier (d.pure Φ hf)) (unipotentFiber F m q) ∂η = 0 := by
  obtain ⟨g,hg,pg⟩ := d.exists_restricted_lift m
  let f := fun v => (g v).val (Φ v)
  have h : ∀ᶠ v in cofinite, f v = d.basic v :=
    (hf.and (d.restrictedCover_fixes_basic hg)).mono fun _ e => e.1 ▸ e.2
  let H := fun q => d.quotientIntegrand f 0 q - d.quotientIntegrand (fun v => d.fourier v (f v)) 0 q
  have hz : ∫ q, H q ∂η = 0 := by
    have he : (fun v => d.fourier v (f v)) = (fun v => (g v).val (d.fourier v (Φ v))) :=
      funext fun v => d.fourier_equivariant v _ _
    dsimp only [H]
    rw [he]
    exact d.translated_constantTerm_difference Φ g h v t hv ht
  let Δ := d.pure Φ hf - d.adelicFourier (d.pure Φ hf)
  let a := d.evaluation (d.coverAction g hg Δ) (verticalPoint F)
  have he (q) : d.thetaOrbitIntegrand Δ (unipotentFiber F m q) = a * conj (H q) := by
    induction q using QuotientAddGroup.induction_on with | _ u => _
    change d.thetaOrbitIntegrand Δ (Quotient.mk _ (adelicUpper F u*m)) = _
    rw [d.thetaOrbitIntegrand_mk Δ ((d.upperLift_restricted u).mul d hg) ((d.upperLift_projects u).mul d pg),
      d.coverAction_mul _ _ (d.upperLift_restricted u) hg,d.vertical_upper]
    congr 2
    dsimp only [H]
    rw [d.quotient_thetaDifference_mk _ h]
    dsimp only [Δ]
    rw [map_sub,map_sub,← d.coverAction_fourier,← d.coverAction_fourier,d.theta_sub_fourier,d.coverAction_pure]
  change ∫ q, d.thetaOrbitIntegrand Δ (unipotentFiber F m q) ∂η = _
  simp_rw [he]
  rw [integral_const_mul,integral_conj,hz,map_zero,mul_zero]

/-- The remaining topological inputs for B.6 are measurability of the product on the
unipotent quotient and continuity of the absolute theta difference on the SL₂ quotient. -/
theorem thetaDifference_eq_zero_of_quotient_regularity (Φ : ∀ v, d.schwartz v) (hf : ∀ᶠ v in cofinite, Φ v = d.basic v)
    (v t : Place F) (hv : d.leading v (Φ v) = 0) (ht : d.leading t (d.fourier t (Φ t)) = 0)
    (w : Prime F) (hδ : Continuous (fun x => (d.quotientThetaBounds (d.pure Φ hf) x).1))
    (hm : Measurable (d.thetaOrbitIntegrand (d.pure Φ hf - d.adelicFourier (d.pure Φ hf)))) :
    d.thetaDifference (d.pure Φ hf) = 0 := by
  let μ : Measure G := Measure.haar
  let : IsFiniteMeasure (slQuotientMeasure F μ) := finiteVolume_slQuotient F w μ
  obtain ⟨C,hC⟩ := d.quotientThetaBounds_bounded Φ hf v t hv ht w
  have hzero := eq_zero_of_unipotentFiber_cancellation F μ hm (by
    refine (lintegral_mono fun x => (d.arithmeticOrbitSum_enorm_le _ x).trans (ENNReal.ofReal_le_ofReal (hC x).2)).trans_lt ?_
    rw [lintegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))
    hδ (d.arithmeticOrbitSum_thetaDifference _) (d.integral_thetaOrbitIntegrand_fiber Φ hf v t hv ht)
  let one := fun v : Place F => (1 : d.cover v)
  have ho : d.IsRestrictedCover one := .of_forall fun p => (d.integralCover p).one_mem
  have po : d.LiftsAdelicMatrix 1 one := fun v => by simp [one]
  have he := congrFun hzero (Quotient.mk _ (1 : G))
  change (d.quotientThetaBounds (d.pure Φ hf) (Quotient.mk _ (1 : G))).1 = 0 at he
  rw [d.quotientThetaBounds_mk _ ho po,d.coverAction_pure] at he
  exact norm_eq_zero.mp he

end MetaplecticPoisson.Datum
