import MetaplecticSummation.Cusp.Regularity
import MetaplecticSummation.BoundaryConstruction

/-! Reduction of continuity on adelic SL₂ to finitely many local evaluations. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField Filter Set
open GroundTheory.Global (integralFiniteAdeles mem_integralFiniteAdeles isOpen_integralFiniteAdeles)
open scoped Topology Matrix MatrixGroups ComplexConjugate
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- All finite components are integral simultaneously in a neighborhood of one. -/
theorem eventually_integral_localMatrices :
    ∀ᶠ m in 𝓝 (1 : AdelicSL F), ∀ (p : Prime F) i j, ‖(localMatrix F (.inr p) m).val i j‖ ≤ 1 := by
  have h (i j : Fin 2) : ∀ᶠ m in 𝓝 (1 : AdelicSL F), (m.val i j).2 ∈ integralFiniteAdeles (𝓞 F) F := by
    have hc : Continuous (fun m : AdelicSL F => (m.val i j).2) :=
      continuous_snd.comp ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))
    apply hc.continuousAt.eventually (isOpen_integralFiniteAdeles.mem_nhds ?_)
    by_cases e : i = j
    · subst j
      simp only [Matrix.SpecialLinearGroup.coe_one,Matrix.one_apply_eq]
      exact (integralFiniteAdeles (𝓞 F) F).one_mem
    · simp only [Matrix.SpecialLinearGroup.coe_one,Matrix.one_apply,e,ite_false]
      exact (integralFiniteAdeles (𝓞 F) F).zero_mem
  filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr (h i))] with m hm p i j
  exact (mem_localIntegers_iff p _).mp (mem_integralFiniteAdeles.mp (hm i j) p)

/-- Outside a finite set, every integral lift gives value one at a prescribed
rational row for a restricted pure section. The exceptional set is uniform in the lift. -/
theorem exists_localValue_support (Φ : ∀ v, d.schwartz v) (hf : ∀ᶠ v in cofinite, Φ v = d.basic v)
    (x : RationalPoint F) : ∃ S : Finset (Place F), ∀ v ∉ S, ∃ p : Prime F, v = .inr p ∧
      ∀ g : d.cover (.inr p), g ∈ d.integralCover p → d.localValue x (.inr p) (g.val (Φ (.inr p))) = 1 := by
  have h : ∀ᶠ v : Place F in cofinite, ∃ p : Prime F, v = .inr p ∧ p.asIdeal.absNorm.Coprime n :=
    eventually_place_of_finite ((eventually_tame (F := F) (n := n)).mono fun p hp => ⟨p,rfl,hp⟩)
  let S := (eventually_cofinite.mp ((hf.and (d.eventually_basic_value x)).and h)).toFinset
  refine ⟨S,fun v hv => ?_⟩
  have ok : (Φ v = d.basic v ∧ d.localValue x v (d.basic v) = 1) ∧
      ∃ p : Prime F, v = .inr p ∧ p.asIdeal.absNorm.Coprime n := by simpa [S,and_assoc] using hv
  obtain ⟨⟨hf,he⟩,p,rfl,ht⟩ := ok
  refine ⟨p,rfl,fun g hg => ?_⟩
  rw [hf,d.integralCover_fixes_basic p ht hg,he]

/-- A local choice of lifts whose evaluations vary continuously at the identity. -/
def HasLocalEvaluationLifts (v : Place F) : Prop :=
  ∃ L : SL(2,LocalField F v) → d.cover v, (∀ a, d.coverProjection v (L a) = a) ∧
    ∀ (f : d.schwartz v) (p : RationalPoint F), ContinuousAt (fun a => d.localValue p v ((L a).val f)) 1

/-- A finite array of translated adelic evaluations admits continuous representatives
near any matrix, up to a common scalar of norm one. -/
theorem local_evaluation_representatives {I J : Type} [Fintype I] [Fintype J]
    (hl : ∀ v, d.HasLocalEvaluationLifts v) (Φ : I → ∀ v, d.schwartz v)
    (hf : ∀ i, ∀ᶠ v in cofinite, Φ i v = d.basic v) (p : J → RationalPoint F) (m : AdelicSL F) :
    ∃ A : I → J → AdelicSL F → ℂ, (∀ i j, ContinuousAt (A i j) m) ∧
      ∀ᶠ b in 𝓝 m, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i j, d.evaluation (d.liftedAction (d.pure (Φ i) (hf i)) b) (p j) = c*A i j b := by
  choose L proj cont using hl
  obtain ⟨r,hr,pr⟩ := d.exists_restricted_lift m
  let f := fun i v => (r v).val (Φ i v)
  have hfr (i) : ∀ᶠ v in cofinite, f i v = d.basic v :=
    ((hf i).and (d.restrictedCover_fixes_basic hr)).mono fun _ e => e.1 ▸ e.2
  choose T tail using fun i j => d.exists_localValue_support (f i) (hfr i) (p j)
  let S := Finset.univ.biUnion fun i : I => Finset.univ.biUnion fun j : J => T i j
  let a := fun (v : Place F) (b : AdelicSL F) => localMatrix F v (b*m⁻¹)
  let A := fun i j b => ∏ v ∈ S, d.localValue (p j) v ((L v (a v b)).val (f i v))
  have cm (v) : Continuous (a v) := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    have entry : Continuous (fun b : AdelicSL F => b.val i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
    exact (continuous_component v).comp (entry.comp (continuous_mul_const m⁻¹))
  refine ⟨A,fun i j => tendsto_finsetProd _ fun v _ => ?_,?_⟩
  · have eqn : a v m = 1 := by simp [a]
    exact ((eqn ▸ cont v (f i v) (p j)) : ContinuousAt _ (a v m)).comp (cm v).continuousAt
  · have hrel : Tendsto (fun b : AdelicSL F => b*m⁻¹) (𝓝 m) (𝓝 1) := by
      rw [← mul_inv_cancel m]
      exact (continuous_mul_const m⁻¹).continuousAt
    filter_upwards [hrel.eventually (eventually_integral_localMatrices (F := F))] with b hb
    let int (w : Prime F) := d.exists_integral_lift w (a (.inr w) b) (hb w)
    let g (v : Place F) : d.cover v := if v ∈ S then L v (a v b) else match v with
      | .inl w => L (.inl w) (a (.inl w) b)
      | .inr w => (int w).choose
    have hg : d.IsRestrictedCover g := by
      have hS : ∀ᶠ w : Prime F in cofinite, (Sum.inr w : Place F) ∉ S :=
        Sum.inr_injective.tendsto_cofinite.eventually (S.finite_toSet.compl_mem_cofinite)
      exact hS.mono fun w hw => by simpa only [g,ite_eq_right hw] using (int w).choose_spec.1
    have pg : d.LiftsAdelicMatrix (b*m⁻¹) g := by
      intro v
      dsimp only [g]
      split
      · exact proj v _
      · cases v with
        | inl w => exact proj _ _
        | inr w => exact (int w).choose_spec.2
    have pb : d.LiftsAdelicMatrix b (fun v => g v * r v) := by simpa only [inv_mul_cancel_right] using pg.mul d pr
    obtain ⟨c,hc,phase⟩ := d.coverAction_scalar_of_same_projection (d.exists_restricted_lift b).choose_spec.1 (hg.mul d hr)
      (d.exists_restricted_lift b).choose_spec.2 pb
    refine ⟨c,hc,fun i j => ?_⟩
    dsimp only [liftedAction]
    rw [phase,map_smul,Pi.smul_apply,smul_eq_mul,d.coverAction_mul _ _ hg hr,d.coverAction_pure,d.coverAction_pure,d.evaluation_pure]
    apply congrArg (c * ·)
    change (∏ᶠ v, d.localValue (p j) v ((g v).val (f i v))) = _
    rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ ?_]
    · apply Finset.prod_congr rfl
      intro v hv
      simp [g,hv]
    · intro v hv
      by_contra hn
      have ht : v ∉ T i j := fun H => hn (by simp [S]; exact ⟨i,j,H⟩)
      obtain ⟨w,rfl,one⟩ := tail i j v ht
      have hout : (Sum.inr w : Place F) ∉ S := hn
      exact hv (one _ (by simpa only [g,ite_eq_right hout] using (int w).choose_spec.1))

local instance localizationSchwartzAddGroup : AddCommGroup d.Schwartz := Module.addCommMonoidToAddCommGroup ℂ

/-- Local continuous evaluation lifts suffice for Proposition B.6. -/
theorem thetaDifference_eq_zero_of_local_evaluation_lifts (hl : ∀ v, d.HasLocalEvaluationLifts v) :
    d.VanishesOnLocalKernels d.thetaDifference := by
  intro Φ hf v t hv ht
  obtain ⟨I,hI,hprime⟩ := Ring.not_isField_iff_exists_prime.mp (NumberField.RingOfIntegers.not_isField F)
  let w : Prime F := ⟨I,hprime,hI⟩
  apply d.thetaDifference_eq_zero_of_continuous_evaluation_products Φ hf v t hv ht w
  intro p q
  let Ψ := fun v => d.fourier v (Φ v)
  have hΨ : ∀ᶠ v in cofinite, Ψ v = d.basic v := (hf.and d.eventually_fourier_basic).mono fun _ h => h.1 ▸ h.2
  let s (b : Bool) : ∀ v, d.schwartz v := if b then Ψ else Φ
  have hs (b) : ∀ᶠ v in cofinite, s b v = d.basic v := by cases b <;> first | exact hf | exact hΨ
  let row (j : Bool) := if j then q else p
  apply continuous_iff_continuousAt.mpr
  intro m
  obtain ⟨A,hA,near⟩ := d.local_evaluation_representatives hl s hs row m
  let V := fun j b => A false j b - A true j b
  have hV j : ContinuousAt (V j) m := (hA false j).sub (hA true j)
  apply ((hV false).mul (Complex.continuous_conj.continuousAt.comp (hV true))).congr_of_eventuallyEq
  filter_upwards [near] with b hb
  obtain ⟨c,hc,e⟩ := hb
  have ev (j) : d.evaluation (d.liftedAction (d.pure Φ hf - d.adelicFourier (d.pure Φ hf)) b) (row j) = c*V j b := by
    dsimp only [liftedAction]
    rw [map_sub,map_sub,Pi.sub_apply,d.adelicFourier_pure,mul_sub]
    exact congrArg₂ (· - ·) (e false j) (e true j)
  change d.evaluation _ (row false) * conj (d.evaluation _ (row true)) = _
  rw [ev,ev,map_mul]
  have hc' : c*conj c = 1 := by simp [Complex.mul_conj,Complex.normSq_eq_norm_sq,hc]
  change (c*V false b)*(conj c*conj (V true b)) = V false b*conj (V true b)
  linear_combination (V false b * conj (V true b)) * hc'

end MetaplecticPoisson.Datum
