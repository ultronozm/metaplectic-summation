import MetaplecticSummation.FiniteAdelicIntegrals
import MetaplecticSummation.AdelicTests
import MetaplecticSummation.ArchimedeanInversion
import MetaplecticSummation.ArchimedeanFourierSchwartz

/-! Comparison of the adelic Fourier integral with the product of the local self-dual transforms. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MetaplecticPoisson.Character
open GroundTheory.Global NumberField MeasureTheory
variable {F : Type} [Field F] [NumberField F]

def adelicHat (ψ : Character F) (f : Adeles F → ℂ) (y : Adeles F) :=
  ∫ x, f x * (ψ.toChar (x*y) : ℂ) ∂adeleMeasure F

theorem adelicHat_square (ψ : Character F) {f : Adeles F → ℂ} (hf : f ∈ schwartzBruhat F) (y : Adeles F) :
    ψ.adelicHat (ψ.adelicHat f) y = f (-y) := by
  obtain ⟨b,hb,_⟩ := ψ.existsUnique_trace_parameter
  let a := IdeleGroup.diagonal F b
  have hat (g : Adeles F → ℂ) : ψ.adelicHat g = fun z => adelicFourier F g (a • z) := by
    funext z
    apply integral_congr_ae
    filter_upwards with x
    change g x * (ψ.toChar (x*z) : ℂ) = g x * (adelicChar F (x*(algebraMap F (Adeles F) b.val*z)) : ℂ)
    rw [hb,mul_left_comm]
  rw [hat (ψ.adelicHat f),hat f]
  change adelicFourier F (fun z => adelicFourier F f (a • z)) (a • y) = _
  rw [adelicFourier_comp_smul a (adelicFourier F f),inv_smul_smul,adelicFourier_adelicFourier hf]
  simp [a,IdeleGroup.ideleModule_diagonal]

end MetaplecticPoisson.Character

namespace MetaplecticPoisson.Datum
open GroundTheory.Global NumberField IsDedekindDomain MeasureTheory Filter
open Classical
open scoped NNReal ContDiff
variable {F : Type} [Field F] [NumberField F] {n : ℕ} (d : Datum F n)
local notation "W" => InfinitePlace F
local notation "A∞" => InfiniteAdeleRing F

theorem infinite_character_product (ψ : Character F) (x : A∞) :
    (ψ.toChar (x,0) : ℂ) = ∏ w : W, ψ.localValue F (.inl w) (x w) := by
  let g (v : Place F) := ψ.localValue F v (component (x,0) v)
  have hzero : HasProd (g ∘ Sum.inr) 1 := by
    rw [show g ∘ Sum.inr = (fun _ => (1 : ℂ)) from funext (fun p => ψ.localValue_zero (.inr p))]
    exact hasProd_one
  have hh := (hasProd_fintype (g ∘ Sum.inl)).sum hzero
  rw [mul_one] at hh
  exact (hasProd_localValue ψ (x,0)).unique hh

/-- A single positive scalar compares the adelic and local Haar normalizations
at infinity, independently of the functions and frequency. -/
theorem exists_infinite_integral_factor :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ f : (w : W) → w.Completion → ℂ,
      (∫ x : A∞, ∏ w, f w (x w) ∂infiniteAdeleMeasure F) =
        (c : ℂ) * ∏ w : W, ∫ t, f w t ∂selfDual F d.character (.inl w) := by
  let μ (w : W) : Measure w.Completion := selfDual F d.character (.inl w)
  let (w : W) : (μ w).IsAddHaarMeasure := (existsUnique_selfDual F d.character (.inl w)).exists.choose_spec.1
  let π := Measure.pi μ
  let : π.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure μ
  let c := Measure.addHaarScalarFactor (infiniteAdeleMeasure F) π
  refine ⟨c,Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _,fun f => ?_⟩
  change _ = (c : ℂ) * ∏ w, ∫ t, f w t ∂μ w
  have he : infiniteAdeleMeasure F = c • π := Measure.isAddLeftInvariant_eq_smul _ _
  rw [he,integral_smul_nnreal_measure,NNReal.smul_def,Complex.real_smul,← integral_fintype_prod_eq_prod]
  rfl


private theorem exists_adelicHat_factor :
    ∃ c : ℝ, 0 < c ∧ ∀ (f : (v : Place F) → LocalField F v → ℂ)
      (_ : ∀ p : Prime F, Bruhat (.inr p) (f (.inr p)))
      (_ : ∀ᶠ p : Prime F in cofinite, ∀ t, f (.inr p) t = if ‖t‖ ≤ 1 then 1 else 0)
      (y : Adeles F), d.character.adelicHat (adelicTensor f) y =
        (c : ℂ) * adelicTensor (fun v => d.hat v (f v)) y := by
  obtain ⟨b,hb,_⟩ := d.character.existsUnique_trace_parameter
  obtain ⟨a,ha,harch⟩ := d.exists_infinite_integral_factor
  let r (p : Prime F) := Real.sqrt ‖algebraMap F (p.adicCompletion F) b.val‖
  have hr : 0 < ∏ᶠ p, r p := by
    have h : ∀ᶠ p in cofinite, r p = 1 :=
      (eventually_diagonal_norm_one b.ne_zero).mono (fun p hp => by change Real.sqrt _ = _; rw [← Real.sqrt_one]; exact congrArg Real.sqrt hp)
    rw [finprod_eq_prod _ (eventually_cofinite.mp h)]
    exact Finset.prod_pos (fun p _ => Real.sqrt_pos.mpr (norm_pos_iff.mpr ((algebraMap F (p.adicCompletion F)).injective.ne b.ne_zero)))
  refine ⟨a / ∏ᶠ p, r p,div_pos ha hr,fun f hf h y => ?_⟩
  let U (x : A∞) := ∏ w : W, f (.inl w) (x w) * d.character.localValue F (.inl w) (y.1 w * x w)
  let V (x : FiniteAdeleRing (𝓞 F) F) := (∏ᶠ p, f (.inr p) (x p)) * (d.character.toChar (0,y.2*x) : ℂ)
  have pair (x : Adeles F) : adelicTensor f x * (d.character.toChar (x*y) : ℂ) = U x.1 * V x.2 := by
    have split : x*y = (y.1*x.1,0) + (0,y.2*x.2) := Prod.ext ((mul_comm x.1 y.1).trans (add_zero _).symm) ((mul_comm x.2 y.2).trans (zero_add _).symm)
    rw [split,AddChar.map_add_eq_mul,Circle.coe_mul,infinite_character_product]
    dsimp only [U,V,adelicTensor]
    simp only [Pi.mul_apply,Finset.prod_mul_distrib]
    ac_rfl
  have arch := harch (fun w t => f (.inl w) t * d.character.localValue F (.inl w) (y.1 w * t))
  have finite := d.finiteFourier_factorization b hb (fun p => f (.inr p)) hf h y.2
  change (∫ x, U x ∂infiniteAdeleMeasure F) = (a : ℂ) * ∏ w, d.hat (.inl w) (f (.inl w)) (y.1 w) at arch
  change ((∏ᶠ p, r p : ℝ) : ℂ) * (∫ x, V x ∂finiteAdeleMeasure F) = _ at finite
  unfold Character.adelicHat
  simp_rw [pair]
  change (∫ x : A∞ × FiniteAdeleRing (𝓞 F) F, U x.1 * V x.2 ∂(infiniteAdeleMeasure F).prod (finiteAdeleMeasure F)) = _
  rw [integral_prod_mul U V,arch,adelicTensor,← finite,Complex.ofReal_div]
  field_simp [Complex.ofReal_ne_zero.mpr hr.ne']


open InfinitePlace.Completion in
private theorem exists_arch_test_one_at_zero (w : W) :
    ∃ f : w.Completion → ℂ, Bruhat (.inl w) f ∧ f 0 = 1 := by
  have test (L : Type) [RCLike L] : ∃ φ : SchwartzMap L ℂ, φ 0 = 1 := by
    let k : ContDiffBump (0 : L) := default
    let g : L → ℂ := fun x => (k x : ℝ)
    have h : HasCompactSupport g := k.hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) rfl
    have sm : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp k.contDiff
    refine ⟨h.toSchwartzMap sm,?_⟩
    change (k 0 : ℂ) = 1
    rw [k.eventuallyEq_one.eq_of_nhds]
    rfl
  by_cases hw : w.IsReal
  · obtain ⟨φ,hφ⟩ := test ℝ
    let e := ringEquivRealOfIsReal hw
    refine ⟨fun t => φ (e t),?_,by change φ (e 0) = 1; rw [map_zero,hφ]⟩
    simp only [Bruhat,dite_eq_left hw]
    exact ⟨φ,fun _ => rfl⟩
  · obtain ⟨φ,hφ⟩ := test ℂ
    let e := ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp hw)
    refine ⟨fun t => φ (e t),?_,by change φ (e 0) = 1; rw [map_zero,hφ]⟩
    simp only [Bruhat,dite_eq_right hw]
    exact ⟨φ,fun _ => rfl⟩

theorem hat_tensor_basic (f : (v : Place F) → LocalField F v → ℂ)
    (h : ∀ᶠ p : Prime F in cofinite, ∀ t, f (.inr p) t = if ‖t‖ ≤ 1 then 1 else 0) :
    ∀ᶠ p : Prime F in cofinite, ∀ t, d.hat (.inr p) (f (.inr p)) t = if ‖t‖ ≤ 1 then 1 else 0 := by
  filter_upwards [h,d.eventually_unramified] with p hp hu
  intro t
  unfold hat
  simp_rw [hp]
  simpa only [mul_comm t] using d.integral_unitBall_character p hu t

/-- The ordinary adelic Fourier integral of a tensor is exactly the product
of the local self-dual Fourier integrals. -/
theorem adelicHat_tensor_of_finite_bruhat (f : (v : Place F) → LocalField F v → ℂ)
    (hf : ∀ p : Prime F, Bruhat (.inr p) (f (.inr p)))
    (h : ∀ᶠ p : Prime F in cofinite, ∀ t, f (.inr p) t = if ‖t‖ ≤ 1 then 1 else 0) (y : Adeles F) :
    d.character.adelicHat (adelicTensor f) y = adelicTensor (fun v => d.hat v (f v)) y := by
  obtain ⟨c,hc,compare⟩ := d.exists_adelicHat_factor
  suffices c = 1 by simpa only [this,Complex.ofReal_one,one_mul] using compare f hf h y
  choose g hreg h0 using (exists_arch_test_one_at_zero (F := F))
  let k : (v : Place F) → LocalField F v → ℂ := fun v => match v with
    | .inl w => g w
    | .inr p => localIntegerIndicator p
  have hk (v : Place F) : Bruhat v (k v) := by
    cases v with
    | inl w => exact hreg w
    | inr p => exact localIntegerIndicator_bruhat p
  have hbase : ∀ᶠ p : Prime F in cofinite, ∀ t, k (.inr p) t = if ‖t‖ ≤ 1 then 1 else 0 := .of_forall (fun _ _ => rfl)
  have hz (v : Place F) : k v 0 = 1 := by
    cases v with
    | inl w => exact h0 w
    | inr p => simp [k,localIntegerIndicator]
  have zeroValue : adelicTensor k 0 = 1 := by
    change (∏ w : W, k (.inl w) 0) * ∏ᶠ p : Prime F, k (.inr p) 0 = 1
    simp only [hz,Finset.prod_const_one,finprod_one,one_mul]
  let l := fun v => d.hat v (k v)
  have hl (p : Prime F) : Bruhat (.inr p) (l (.inr p)) := d.hat_finite_bruhat p (hk _)
  have hh (v : Place F) : d.hat v (l v) 0 = 1 := by
    cases v with
    | inl w => exact (congrFun (d.arch_hat_hat w _ (hk _)) 0).trans (by rw [neg_zero]; exact hz (.inl w))
    | inr p => exact (d.hat_hat_finite p (hk _) 0).trans (by rw [neg_zero]; exact hz (.inr p))
  have hz' : adelicTensor (fun v => d.hat v (l v)) 0 = 1 := by
    change (∏ w : W, d.hat (.inl w) (l (.inl w)) 0) * ∏ᶠ p : Prime F, d.hat (.inr p) (l (.inr p)) 0 = 1
    simp only [hh,Finset.prod_const_one,finprod_one,one_mul]
  have eq1 : d.character.adelicHat (adelicTensor k) = fun x => (c : ℂ) * adelicTensor l x :=
    funext (compare k (fun p => hk (.inr p)) hbase)
  have eq2 := compare l hl (d.hat_tensor_basic k hbase) 0
  rw [hz',mul_one] at eq2
  have sq := d.character.adelicHat_square (adelicTensor_mem_schwartzBruhat k hk hbase) 0
  rw [neg_zero,zeroValue,eq1] at sq
  have scale : d.character.adelicHat (fun x => (c : ℂ) * adelicTensor l x) 0 =
      (c : ℂ) * d.character.adelicHat (adelicTensor l) 0 := by
    simp only [Character.adelicHat,mul_assoc,integral_const_mul]
  rw [scale,eq2,← Complex.ofReal_mul] at sq
  have hc2 : c*c = 1 := Complex.ofReal_injective (sq.trans Complex.ofReal_one.symm)
  nlinarith


/-- The ordinary adelic Fourier integral of a tensor is exactly the product
of the local self-dual Fourier integrals. -/
theorem adelicHat_tensor (f : (v : Place F) → LocalField F v → ℂ)
    (hf : ∀ v, Bruhat v (f v))
    (h : ∀ᶠ p : Prime F in cofinite, ∀ t, f (.inr p) t = if ‖t‖ ≤ 1 then 1 else 0) (y : Adeles F) :
    d.character.adelicHat (adelicTensor f) y = adelicTensor (fun v => d.hat v (f v)) y :=
  d.adelicHat_tensor_of_finite_bruhat f (fun p => hf (.inr p)) h y

theorem adelicTensor_eq_finprod (f : (v : Place F) → LocalField F v → ℂ)
    (h : ∀ᶠ p : Prime F in cofinite, ∀ t, f (.inr p) t = if ‖t‖ ≤ 1 then 1 else 0) (t : Adeles F) :
    adelicTensor f t = ∏ᶠ v, f v (component t v) := by
  let g (v : Place F) := f v (component t v)
  have hf : ∀ᶠ p : Prime F in cofinite, g (.inr p) = 1 := by
    filter_upwards [h,t.2.2] with p hp ht
    exact (hp _).trans (ite_eq_left ((mem_localIntegers_iff p _).mp ht))
  have hm := eventually_cofinite.mp (eventually_place_of_finite (F := F) (P := fun v => g v = 1) hf)
  have hr : Function.HasFiniteMulSupport (g ∘ Sum.inr) := eventually_cofinite.mp hf
  change (∏ w : W, g (.inl w)) * (∏ᶠ p : Prime F, g (.inr p)) = ∏ᶠ v, g v
  rw [← tprod_eq_finprod (L := SummationFilter.unconditional _) hm,
    Multipliable.tprod_sum (f := g) (hasProd_fintype _).multipliable (multipliable_of_hasFiniteMulSupport hr),
    tprod_fintype,tprod_eq_finprod (f := fun p => g (.inr p)) hr]

private theorem adelicTensor_diagonal (f : (v : Place F) → LocalField F v → ℂ)
    (h : ∀ᶠ p : Prime F in cofinite, ∀ t, f (.inr p) t = if ‖t‖ ≤ 1 then 1 else 0) (t : F) :
    adelicTensor f (algebraMap F (Adeles F) t) = ∏ᶠ v, f v (diagonal F v t) := by
  rw [adelicTensor_eq_finprod f h]
  exact finprod_congr fun v => by cases v <;> rfl

/-- Additive Poisson on a restricted tensor with the actual local self-dual Haar measures.
Both diagonal series converge absolutely. -/
theorem additivePoisson_tensor (f : (v : Place F) → LocalField F v → ℂ)
    (hf : ∀ v, Bruhat v (f v))
    (h : ∀ᶠ p : Prime F in cofinite, ∀ t, f (.inr p) t = if ‖t‖ ≤ 1 then 1 else 0) :
    let a := fun t : F => ∏ᶠ v, f v (diagonal F v t)
    let b := fun t : F => ∏ᶠ v, d.hat v (f v) (diagonal F v t)
    Summable (fun t => ‖a t‖) ∧ Summable (fun t => ‖b t‖) ∧ ∑' t, a t = ∑' t, b t := by
  have ht := d.character.adelic_poisson (adelicTensor_mem_schwartzBruhat f hf h)
  change Summable _ ∧ Summable (fun t : F => ‖d.character.adelicHat (adelicTensor f) (algebraMap F _ t)‖) ∧
    (∑' t : F, adelicTensor f (algebraMap F _ t)) = ∑' t : F, d.character.adelicHat (adelicTensor f) (algebraMap F _ t) at ht
  simpa only [d.adelicHat_tensor f hf h,adelicTensor_diagonal f h,
    adelicTensor_diagonal (fun v => d.hat v (f v)) (d.hat_tensor_basic f h)] using ht

end MetaplecticPoisson.Datum
