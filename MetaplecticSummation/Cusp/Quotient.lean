import MetaplecticSummation.Cusp.Lifts
import MetaplecticSummation.Cusp.Decay
import MetaplecticSummation.Reduction.SiegelIntegral

/-! The functions δ and θ of Proposition B.6 on the arithmetic quotient. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField Filter Set
open scoped Matrix MatrixGroups
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
local notation "G" => AdelicSL F
local notation "X" => SLArithmeticQuotient F
local notation "ι" => rationalSLMap F

/-- Sum of the absolute values of the two theta series. -/
def thetaAbs (Φ : d.Schwartz) : ℝ :=
  ∑' p, (‖d.evaluation Φ p‖ + ‖d.evaluation (d.adelicFourier Φ) p‖)

private theorem thetaAbs_smul {c : ℂ} (hc : ‖c‖ = 1) (Φ : d.Schwartz) :
    d.thetaAbs (c • Φ) = d.thetaAbs Φ := by
  unfold thetaAbs
  apply tsum_congr
  intro p
  simp only [map_smul,Pi.smul_apply,smul_eq_mul,norm_mul,hc,one_mul]

/-- Action on a section of one chosen restricted lift of an adelic matrix. -/
def liftedAction (Φ : d.Schwartz) (m : G) : d.Schwartz :=
  d.coverAction (d.exists_restricted_lift m).choose (d.exists_restricted_lift m).choose_spec.1 Φ

private theorem quantities_of_lift {m : G} {g : ∀ v, d.cover v} (hg : d.IsRestrictedCover g)
    (hm : d.LiftsAdelicMatrix m g) (Φ : d.Schwartz) :
    (‖d.thetaDifference (d.liftedAction Φ m)‖,d.thetaAbs (d.liftedAction Φ m)) =
      (‖d.thetaDifference (d.coverAction g hg Φ)‖,d.thetaAbs (d.coverAction g hg Φ)) := by
  obtain ⟨c,hc,e⟩ := d.coverAction_scalar_of_same_projection (d.exists_restricted_lift m).choose_spec.1 hg
    (d.exists_restricted_lift m).choose_spec.2 hm
  dsimp only [liftedAction]
  rw [e Φ,d.thetaAbs_smul hc,map_smul,smul_eq_mul,norm_mul,hc,one_mul]

theorem LiftsRationalMatrix.adelic {γ : SL(2,F)} {r : ∀ v, d.cover v} (h : d.LiftsRationalMatrix γ r) :
    d.LiftsAdelicMatrix (ι γ) r := by
  intro v
  rw [h v]
  cases v <;> rfl

theorem LiftsAdelicMatrix.mul {a b : G} {g h : ∀ v, d.cover v}
    (pg : d.LiftsAdelicMatrix a g) (ph : d.LiftsAdelicMatrix b h) :
    d.LiftsAdelicMatrix (a*b) (fun v => g v * h v) := fun v => by rw [map_mul,pg,ph,map_mul]

private theorem quantities_rational (Φ : d.Schwartz) (γ : SL(2,F)) (m : G) :
    (‖d.thetaDifference (d.liftedAction Φ (ι γ*m))‖,d.thetaAbs (d.liftedAction Φ (ι γ*m))) =
      (‖d.thetaDifference (d.liftedAction Φ m)‖,d.thetaAbs (d.liftedAction Φ m)) := by
  obtain ⟨r,hr,pr,ev,th⟩ := d.exists_rational_lift γ
  let g := (d.exists_restricted_lift m).choose
  obtain ⟨hg,pg⟩ := (d.exists_restricted_lift m).choose_spec
  rw [d.quantities_of_lift (hr.mul d hg) ((pr.adelic d).mul d pg),d.coverAction_mul]
  let Ψ := d.liftedAction Φ m
  change (‖d.thetaDifference (d.coverAction r hr Ψ)‖,d.thetaAbs (d.coverAction r hr Ψ)) = _
  apply Prod.ext
  · change ‖d.theta (d.coverAction r hr Ψ) - d.theta (d.adelicFourier (d.coverAction r hr Ψ))‖ = ‖d.theta Ψ-d.theta (d.adelicFourier Ψ)‖
    rw [d.coverAction_fourier,th,th]
  · change d.thetaAbs (d.coverAction r hr Ψ) = d.thetaAbs Ψ
    unfold thetaAbs
    rw [d.coverAction_fourier]
    simp_rw [ev]
    exact (rationalRowPerm γ).tsum_eq (fun p => ‖d.evaluation Ψ p‖ + ‖d.evaluation (d.adelicFourier Ψ) p‖)

/-- The absolute theta difference and the absolute theta sum on SL₂(F) ∖ SL₂(𝔸). -/
def quotientThetaBounds (Φ : d.Schwartz) : X → ℝ × ℝ :=
  Quotient.lift (fun m : G => (‖d.thetaDifference (d.liftedAction Φ m)‖,d.thetaAbs (d.liftedAction Φ m))) (by
    intro a b h
    obtain ⟨γ,hγ⟩ := QuotientGroup.rightRel_apply.mp h
    have e : b = ι γ*a := (eq_mul_inv_iff_mul_eq.mp hγ).symm
    exact e ▸ (d.quantities_rational Φ γ a).symm)

/-- Either coordinate of the descended function can be computed using any restricted lift. -/
theorem quotientThetaBounds_mk (Φ : d.Schwartz) {m : G} {g : ∀ v, d.cover v}
    (hg : d.IsRestrictedCover g) (hm : d.LiftsAdelicMatrix m g) :
    d.quotientThetaBounds Φ (Quotient.mk _ m) =
      (‖d.thetaDifference (d.coverAction g hg Φ)‖,d.thetaAbs (d.coverAction g hg Φ)) :=
  d.quantities_of_lift hg hm Φ

/-- The square of δ and the product θδ are bounded on the whole quotient under the
two leading-term vanishing hypotheses. -/
theorem quotientThetaBounds_bounded (Φ : ∀ v, d.schwartz v) (hf : ∀ᶠ v in cofinite, Φ v = d.basic v)
    (v t : Place F) (hv : d.leading v (Φ v) = 0) (ht : d.leading t (d.fourier t (Φ t)) = 0)
    (w : Prime F) : ∃ C : ℝ, ∀ x : X, let a := d.quotientThetaBounds (d.pure Φ hf) x
      a.1^2 ≤ C ∧ a.2*a.1 ≤ C := by
  obtain ⟨K,hK,hcover,_⟩ := exists_siegel_integral_bound F w
  obtain ⟨M,hM,decay⟩ := d.cusp_thetaDifference_decay Φ hf v t hv ht w K hK 3
  obtain ⟨T,hT,growth⟩ := d.cusp_theta_growth Φ hf w K hK
  refine ⟨max (M^2) (T*M),?_⟩
  intro x
  induction x using Quotient.inductionOn with | _ m => _
  obtain ⟨γ,u,k,ω,hω,hm⟩ := hcover m
  let b := adelicUpper F u * ideleDiagonal F (cuspIdele F w)^k * ω
  have e : (Quotient.mk _ m : X) = Quotient.mk _ b := by
    apply Eq.symm
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    exact ⟨γ,eq_mul_inv_iff_mul_eq.mpr (by simpa [b,mul_assoc] using hm.symm)⟩
  obtain ⟨g,hg,pg⟩ := d.exists_restricted_lift b
  rw [e,d.quotientThetaBounds_mk _ hg pg]
  let δ := ‖d.thetaDifference (d.coverAction g hg (d.pure Φ hf))‖
  let θ := d.thetaAbs (d.coverAction g hg (d.pure Φ hf))
  let q : ℝ := w.asIdeal.absNorm
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm w).le
  have hk : 1 ≤ q^(3*k) := one_le_pow₀ hq
  have θh : θ ≤ T*q^(3*k) := by
    dsimp only [θ,thetaAbs]
    rw [d.coverAction_fourier]
    exact growth u k ω hω g hg pg
  have δh : δ ≤ M*(q^(3*k))⁻¹ := by
    have h := decay u k ω hω g hg pg
    change δ ≤ M*q^(-(3:ℝ)*k) at h
    rwa [neg_mul,Real.rpow_neg (zero_le_one.trans hq),← Nat.cast_ofNat (n := 3),← Nat.cast_mul,Real.rpow_natCast] at h
  have hδ : 0 ≤ δ := norm_nonneg _
  have hδM := δh.trans (mul_le_of_le_one_right hM (inv_le_one_of_one_le₀ hk))
  change δ^2 ≤ _ ∧ θ*δ ≤ _
  refine ⟨(pow_le_pow_left₀ hδ hδM 2).trans (le_max_left ..),?_⟩
  refine ((mul_le_mul θh δh hδ (mul_nonneg hT (zero_le_one.trans hk))).trans_eq ?_).trans (le_max_right ..)
  field_simp [ne_of_gt (zero_lt_one.trans_le hk)]

end MetaplecticPoisson.Datum
