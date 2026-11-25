import MetaplecticSummation.FiniteAdelicTests
import MetaplecticSummation.TraceConductor

/-! Integration and Fourier transformation of a restricted tensor on the finite adeles. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open GroundTheory.Global NumberField IsDedekindDomain MeasureTheory Filter
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} (d : Datum F n)
local notation "P" => HeightOneSpectrum (𝓞 F)
local notation "A" => FiniteAdeleRing (𝓞 F) F
set_option backward.isDefEq.respectTransparency false
local instance finiteTensorMeasurableSpace (p : P) : MeasurableSpace (p.adicCompletion F) := borel _
local instance finiteTensorBorelSpace (p : P) : BorelSpace (p.adicCompletion F) := ⟨rfl⟩

private theorem exchange_local_factor (p : P) {U V : A → ℂ} {f g : p.adicCompletion F → ℂ}
    (hU : U ∈ finiteSchwartzBruhat F) (hV : V ∈ finiteSchwartzBruhat F)
    (hf : Bruhat (.inr p) f) (hg : Bruhat (.inr p) g)
    (h : ∀ (x : A) (t : p.adicCompletion F), U (x - finiteAdeleSingleAdd p t) * g (x p) =
      V x * f (x p - t)) :
    (∫ x, U x ∂finiteAdeleMeasure F) * (∫ t, g t ∂selfDual F d.character (.inr p)) =
      (∫ x, V x ∂finiteAdeleMeasure F) * (∫ t, f t ∂selfDual F d.character (.inr p)) := by
  let : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  let : ProperSpace (p.adicCompletion F) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  let μ : Measure (p.adicCompletion F) := selfDual F d.character (.inr p)
  let ν := finiteAdeleMeasure F
  let : μ.IsAddHaarMeasure := (existsUnique_selfDual F d.character (.inr p)).exists.choose_spec.1
  let L (x : A) (t : p.adicCompletion F) := U x * g (t + x p)
  let R (x : A) (t : p.adicCompletion F) := V x * f (x p - t)
  have ev : Continuous (fun x : A => x p) := RestrictedProduct.continuous_eval p
  have hg' : IsLocallyConstant g ∧ HasCompactSupport g := hg
  have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf
  have gi : Integrable g μ := hg'.1.continuous.integrable_of_hasCompactSupport hg'.2
  have fi : Integrable f μ := hf'.1.continuous.integrable_of_hasCompactSupport hf'.2
  have Li : Integrable (Function.uncurry L) (ν.prod μ) := by
    apply (integrable_prod_iff ((hU.1.continuous.comp continuous_fst).mul
      (hg'.1.continuous.comp (continuous_snd.add (ev.comp continuous_fst)))).aestronglyMeasurable).2
    refine ⟨.of_forall fun x => (gi.comp_add_right (x p)).const_mul (U x),?_⟩
    change Integrable (fun x : A => ∫ t, ‖U x * g (t+x p)‖ ∂μ) ν
    simp only [norm_mul,integral_const_mul,integral_add_right_eq_self (fun t => ‖g t‖)]
    exact (integrable_of_mem_finiteSchwartzBruhat hU).norm.mul_const _
  have Ri : Integrable (Function.uncurry R) (ν.prod μ) := by
    apply (integrable_prod_iff ((hV.1.continuous.comp continuous_fst).mul
      (hf'.1.continuous.comp ((ev.comp continuous_fst).sub continuous_snd))).aestronglyMeasurable).2
    refine ⟨.of_forall fun x => (fi.comp_sub_left (x p)).const_mul (V x),?_⟩
    change Integrable (fun x : A => ∫ t, ‖V x * f (x p-t)‖ ∂μ) ν
    simp only [norm_mul,integral_const_mul,integral_sub_left_eq_self (fun t => ‖f t‖)]
    exact (integrable_of_mem_finiteSchwartzBruhat hV).norm.mul_const _
  have inner (t : p.adicCompletion F) : (∫ x, L x t ∂ν) = ∫ x, R x t ∂ν := by
    rw [← integral_sub_right_eq_self (fun x => L x t) (finiteAdeleSingleAdd p t)]
    apply integral_congr_ae
    filter_upwards with x
    have hp : (x - finiteAdeleSingleAdd p t) p = x p - t := by
      change x p - finiteAdeleSingleAdd p t p = x p - t
      rw [finiteAdeleSingleAdd_apply_self]
    change U _ * g (t + (x - finiteAdeleSingleAdd p t) p) = _
    rw [hp,add_sub_cancel]
    exact h x t
  change (∫ x, U x ∂ν) * (∫ t, g t ∂μ) = (∫ x, V x ∂ν) * (∫ t, f t ∂μ)
  calc
    _ = ∫ x, ∫ t, L x t ∂μ ∂ν := by
      simp only [L,integral_const_mul,integral_add_right_eq_self g,integral_mul_const]
    _ = ∫ t, ∫ x, L x t ∂ν ∂μ := integral_integral_swap Li
    _ = ∫ t, ∫ x, R x t ∂ν ∂μ := by simp_rw [inner]
    _ = ∫ x, ∫ t, R x t ∂μ ∂ν := (integral_integral_swap Ri).symm
    _ = _ := by simp only [R,integral_const_mul,integral_sub_left_eq_self f,integral_mul_const]


private theorem integer_volume_pos (p : P) :
    0 < (selfDual F d.character (.inr p)).real {x | ‖x‖ ≤ 1} := by
  obtain ⟨a,ha⟩ := d.exists_finite_conductor p
  rw [d.selfDual_volume_of_conductor p a ha]
  exact Real.sqrt_pos.mpr (norm_pos_iff.mpr a.ne_zero)

/-- The reference test at a finite place. -/
def localIntegerIndicator (p : P) (t : p.adicCompletion F) : ℂ := if ‖t‖ ≤ 1 then 1 else 0

private theorem localIntegerIndicator_eq_indicator (p : P) :
    localIntegerIndicator p = (p.adicCompletionIntegers F : Set (p.adicCompletion F)).indicator 1 := by
  ext t
  simp only [localIntegerIndicator,Set.indicator_apply,Pi.one_apply,SetLike.mem_coe,mem_localIntegers_iff]

theorem localIntegerIndicator_bruhat (p : P) : Bruhat (.inr p) (localIntegerIndicator p) := by
  have hc := FinitePlace.isCompact_adicCompletionIntegers p
  have ho := FinitePlace.isOpen_adicCompletionIntegers p
  rw [localIntegerIndicator_eq_indicator]
  exact ⟨(LocallyConstant.charFn ℂ ⟨hc.isClosed,ho⟩).isLocallyConstant,
    HasCompactSupport.intro hc (fun _ ht => Set.indicator_of_notMem ht _)⟩

private theorem integral_localIntegerIndicator (p : P) :
    (∫ t, localIntegerIndicator p t ∂selfDual F d.character (.inr p)) =
      ((selfDual F d.character (.inr p)).real {t | ‖t‖ ≤ 1} : ℂ) := by
  let O := (p.adicCompletionIntegers F : Set (p.adicCompletion F))
  have he : O = {t | ‖t‖ ≤ 1} := Set.ext (mem_localIntegers_iff p)
  let μ : Measure (p.adicCompletion F) := selfDual F d.character (.inr p)
  change (∫ t : p.adicCompletion F, localIntegerIndicator p t ∂μ) = (μ.real _ : ℂ)
  rw [localIntegerIndicator_eq_indicator,integral_indicator (FinitePlace.isOpen_adicCompletionIntegers p).measurableSet]
  simp only [Pi.one_def,integral_const,measureReal_restrict_apply_univ,Complex.real_smul,mul_one]
  exact congrArg (fun s => (μ.real s : ℂ)) he

/-- Integration of a restricted tensor with the reference local integer balls.
The local integrals are divided by the mass of those balls. -/
theorem integral_finiteTensor (f : (p : P) → p.adicCompletion F → ℂ)
    (hf : ∀ p, Bruhat (.inr p) (f p))
    (h : ∀ᶠ p in cofinite, ∀ t, f p t = if ‖t‖ ≤ 1 then 1 else 0) :
    (∫ x : A, (∏ᶠ p, f p (x p)) ∂finiteAdeleMeasure F) =
      ((finiteAdeleMeasure F).real (integralFiniteAdeles (𝓞 F) F) : ℂ) *
        ∏ᶠ p : P, (∫ t, f p t ∂selfDual F d.character (.inr p)) /
          ((selfDual F d.character (.inr p)).real {t | ‖t‖ ≤ 1} : ℂ) := by
  classical
  let vol (p : P) : ℂ := (selfDual F d.character (.inr p)).real {t | ‖t‖ ≤ 1}
  have vne (p : P) : vol p ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (d.integer_volume_pos p).ne'
  let ratio (p : P) := (∫ t, f p t ∂selfDual F d.character (.inr p)) / vol p
  let G (S : Finset P) (p : P) := if p ∈ S then f p else localIntegerIndicator p
  let T (S : Finset P) (x : A) := ∏ᶠ p, G S p (x p)
  have basic (S : Finset P) : ∀ᶠ p in cofinite, ∀ t, G S p t = if ‖t‖ ≤ 1 then 1 else 0 :=
    (show ∀ᶠ q in cofinite, q ∉ S from S.finite_toSet.compl_mem_cofinite).mono (fun p hp t => by simp only [G,ite_eq_right hp,localIntegerIndicator])
  have test (S : Finset P) : T S ∈ finiteSchwartzBruhat F :=
    finiteTensor_mem_schwartzBruhat _ (fun p => by by_cases hp : p ∈ S <;> simp [G,hp,hf,localIntegerIndicator_bruhat]) (basic S)
  have support (S : Finset P) (x : A) : Function.HasFiniteMulSupport (fun p => G S p (x p)) := by
    apply eventually_cofinite.mp
    filter_upwards [basic S,x.2] with p hp hx
    exact (hp _).trans (ite_eq_left ((mem_localIntegers_iff p _).mp hx))
  have integral (S : Finset P) : (∫ x, T S x ∂finiteAdeleMeasure F) =
      ((finiteAdeleMeasure F).real (integralFiniteAdeles (𝓞 F) F) : ℂ) * ∏ p ∈ S, ratio p := by
    induction S using Finset.induction_on with
    | empty =>
      have he : T ∅ = ((integralFiniteAdeles (𝓞 F) F : Set A)).indicator 1 := by
        funext x
        by_cases hx : x ∈ integralFiniteAdeles (𝓞 F) F
        · rw [Set.indicator_of_mem hx]
          exact finprod_eq_one_of_forall_eq_one fun p => by
            simp [G,localIntegerIndicator,(mem_localIntegers_iff p _).mp ((mem_integralFiniteAdeles.mp hx) p)]
        · rw [Set.indicator_of_notMem hx]
          obtain ⟨p,hp⟩ := not_forall.mp (fun hh => hx (mem_integralFiniteAdeles.mpr hh))
          have hn : ¬ ‖x p‖ ≤ 1 := fun h => hp ((mem_localIntegers_iff p _).mpr h)
          exact finprod_eq_zero _ p (by change localIntegerIndicator p (x p) = 0; exact ite_eq_right hn) (support ∅ x)
      rw [he,integral_indicator isOpen_integralFiniteAdeles.measurableSet]
      simp [Complex.real_smul]
    | insert p S hp ih =>
      have ex := d.exchange_local_factor p (test (insert p S)) (test S) (hf p) (localIntegerIndicator_bruhat p) (fun x t => by
        let y := x - finiteAdeleSingleAdd p t
        have self : y p = x p - t := by change x p - finiteAdeleSingleAdd p t p = _; rw [finiteAdeleSingleAdd_apply_self]
        have other (q : P) (hq : q ≠ p) : y q = x q := by
          change x q - finiteAdeleSingleAdd p t q = x q
          rw [finiteAdeleSingleAdd_apply_of_ne hq,sub_zero]
        change T (insert p S) y * _ = T S x * _
        dsimp only [T]
        rw [← mul_finprod_cond_ne p (support (insert p S) y),← mul_finprod_cond_ne p (support S x)]
        have he : (∏ᶠ (q) (_ : q ≠ p), G (insert p S) q (y q)) = ∏ᶠ (q) (_ : q ≠ p), G S q (x q) :=
          finprod_mem_congr (s := {q | q ≠ p}) rfl (fun q hq => by change q ≠ p at hq; simp [G,hq,other q hq])
        rw [he,self]
        simp [G,hp,mul_comm,mul_left_comm])
      rw [integral_localIntegerIndicator] at ex
      change _ * vol p = _ at ex
      rw [ih] at ex
      rw [Finset.prod_insert hp]
      have ex := (eq_div_iff (vne p)).mpr ex
      rw [ex]
      dsimp [ratio]
      ring
  let S := (eventually_cofinite.mp h).toFinset
  have outside (p : P) (hp : p ∉ S) : f p = localIntegerIndicator p := funext (of_not_not fun hn => hp ((eventually_cofinite.mp h).mem_toFinset.mpr hn))
  have he (p : P) : G S p = f p := by by_cases hp : p ∈ S <;> simp [G,hp,outside]
  have hs : Function.mulSupport ratio ⊆ S := by
    intro p hp
    by_contra hn
    apply hp
    dsimp only [ratio]
    rw [outside p hn,integral_localIntegerIndicator]
    exact div_self (vne p)
  change _ = _ * ∏ᶠ p, ratio p
  rw [finprod_eq_prod_of_mulSupport_subset _ hs,← integral]
  simp only [T,he]

private theorem eventually_finite_localValue_one (ψ : Character F) (x : A) :
    ∀ᶠ p : P in cofinite, ψ.localValue F (.inr p) (x p) = 1 := by
  filter_upwards [eventually_trivial_on_integers ψ,x.2] with p hp hx
  exact hp _ ((mem_localIntegers_iff p _).mp hx)

/-- The additive character on the finite adeles is the finite product of its local values. -/
theorem finite_character_eq_finprod (ψ : Character F) (x : A) :
    (ψ.toChar (0,x) : ℂ) = ∏ᶠ p : P, ψ.localValue F (.inr p) (x p) := by
  let g (v : Place F) := ψ.localValue F v (component (0,x) v)
  have hinf : HasProd (g ∘ Sum.inl) 1 := by
    rw [show g ∘ Sum.inl = (fun _ : InfinitePlace F => (1 : ℂ)) from funext (fun w => ψ.localValue_zero (.inl w))]
    exact
      (hasProd_one : HasProd (fun _ : InfinitePlace F => (1 : ℂ)) 1)
  have hfin := eventually_cofinite.mp (eventually_finite_localValue_one ψ x)
  have hf : HasProd (g ∘ Sum.inr) (∏ᶠ p : P, ψ.localValue F (.inr p) (x p)) := by
    rw [finprod_eq_prod _ hfin]
    exact hasProd_prod_of_ne_finset_one fun p hp => of_not_not (fun hn => hp (hfin.mem_toFinset.mpr hn))
  have hh := hinf.sum hf
  rw [one_mul] at hh
  exact (hasProd_localValue ψ (0,x)).unique hh

private theorem phase_test (ψ : Character F) (p : P) (y : p.adicCompletion F)
    {f : p.adicCompletion F → ℂ} (hf : Bruhat (.inr p) f) :
    Bruhat (.inr p) (fun t : p.adicCompletion F => f t * ψ.localValue F (.inr p) (y*t)) :=
  ⟨hf.1.mul ((ψ.locallyConstant_finiteValue p).comp_continuous (continuous_const.mul continuous_id)),
   hf.2.mul_right⟩


/-- The normalized finite adelic Fourier integral factors into the paper's
one-dimensional transforms, for every finite adelic frequency. -/
theorem finiteFourier_factorization (b : Fˣ)
    (hb : ∀ x : Adeles F, d.character.toChar x =
      adelicChar F (algebraMap F (Adeles F) b.val * x))
    (f : (p : P) → p.adicCompletion F → ℂ) (hf : ∀ p, Bruhat (.inr p) (f p))
    (h : ∀ᶠ p in cofinite, ∀ t, f p t = if ‖t‖ ≤ 1 then 1 else 0) (y : A) :
    ((∏ᶠ p : P, Real.sqrt ‖algebraMap F (p.adicCompletion F) b.val‖ : ℝ) : ℂ) *
      (∫ x : A, (∏ᶠ p, f p (x p)) * (d.character.toChar (0,y*x) : ℂ) ∂finiteAdeleMeasure F) =
        ∏ᶠ p : P, d.hat (.inr p) (f p) (y p) := by
  let g (p : P) (t : p.adicCompletion F) := f p t * d.character.localValue F (.inr p) (y p * t)
  have hg : ∀ᶠ p in cofinite, ∀ t, g p t = if ‖t‖ ≤ 1 then 1 else 0 := by
    filter_upwards [h,y.2,eventually_trivial_on_integers d.character] with p hp hy hχ
    intro t
    dsimp only [g]
    rw [hp]
    split_ifs with ht
    · have hyt := (p.adicCompletionIntegers F).toSubring.mul_mem hy ((mem_localIntegers_iff p _).mpr ht)
      rw [one_mul]
      exact hχ _ ((mem_localIntegers_iff p _).mp hyt)
    · rw [zero_mul]
  have ex := d.integral_finiteTensor g (fun p => phase_test _ p _ (hf p)) hg
  have e (x : A) : (∏ᶠ p, g p (x p)) =
      (∏ᶠ p, f p (x p)) * (d.character.toChar (0,y*x) : ℂ) := by
    rw [finite_character_eq_finprod]
    apply finprod_mul_distrib _ (eventually_cofinite.mp (eventually_finite_localValue_one _ (y*x)))
    apply eventually_cofinite.mp
    filter_upwards [h,x.2] with p hp hx
    exact (hp _).trans (ite_eq_left ((mem_localIntegers_iff p _).mp hx))
  simp_rw [e] at ex
  let vol (p : P) : ℝ := (selfDual F d.character (.inr p)).real {t | ‖t‖ ≤ 1}
  have hv : ∀ᶠ p in cofinite, vol p = 1 := d.eventually_selfDual_volume_one
  have hvC : ∀ᶠ p in cofinite, (vol p : ℂ) = 1 := hv.mono (fun p hp => by rw [hp,Complex.ofReal_one])
  have ht : ∀ᶠ p in cofinite, d.hat (.inr p) (f p) (y p) = 1 := by
    filter_upwards [hg,hvC] with p hp hh
    change (∫ t, g p t ∂selfDual F d.character (.inr p)) = 1
    rw [show g p = localIntegerIndicator p from funext hp,integral_localIntegerIndicator]
    exact hh
  change _ = _ * ∏ᶠ p : P, d.hat (.inr p) (f p) (y p) / (vol p : ℂ) at ex
  rw [finprod_div_distrib (eventually_cofinite.mp ht) (eventually_cofinite.mp hvC)] at ex
  have hprod := d.finite_selfDual_volume_product b hb
  change (∏ᶠ p, vol p) = _ at hprod
  have hpos : 0 < ∏ᶠ p, vol p := by
    rw [finprod_eq_prod _ (eventually_cofinite.mp hv)]
    exact Finset.prod_pos (fun p _ => d.integer_volume_pos p)
  have hc : ((∏ᶠ p, vol p : ℝ) : ℂ) = ∏ᶠ p, (vol p : ℂ) :=
    Complex.ofRealHom.toMonoidHom.map_finprod (eventually_cofinite.mp hv)
  rw [ex,← mul_assoc,← Complex.ofReal_mul,← hprod,hc]
  exact mul_div_cancel₀ _ (hc ▸ Complex.ofReal_ne_zero.mpr hpos.ne')

end MetaplecticPoisson.Datum
