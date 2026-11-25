import MetaplecticSummation.FiniteGerms

/-! Absolute convergence on nonzero determinant fibers for finite-place Schwartz sections. -/

noncomputable section
namespace MetaplecticPoisson
open Set Filter MeasureTheory NumberField IsDedekindDomain
open scoped Topology
open Classical

variable {K : Type*} [Field K]
def lineIntegrandX (h : Kˣ → Kˣ → ℂ) (f : Charts K) (n : ℕ) (t : K) (a : Kˣ) (b x : K) : ℂ :=
  if hx : x ≠ 0 then f.1 (Units.mk0 x hx) ((x*b-t^n)/a.val) * h (Units.mk0 x hx) (-a) else 0

def lineIntegrandY (h : Kˣ → Kˣ → ℂ) (f : Charts K) (n : ℕ) (t a : K) (b : Kˣ) (y : K) : ℂ :=
  if hy : y ≠ 0 then f.2 ((a*y+t^n)/b.val) (Units.mk0 y hy) * h (Units.mk0 y hy) b * h (-1) b else 0

namespace Datum
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- On a line of nonzero determinant a Schwartz section agrees with a test section.
Cutting off in the determinant variable keeps the full fiber and removes a
neighborhood of the origin. -/
private theorem finite_test_on_line (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (a b z : LocalField F (.inr p)) (hz : z ≠ 0) :
    let v : Place F := .inr p
    ∃ f ∈ d.testSet v,
      (∀ (x : (LocalField F v)ˣ) y, x.val*b-a*y = z → f.1 x y = Φ.val.1 x y) ∧
      (∀ x (y : (LocalField F v)ˣ), x*b-a*y.val = z → f.2 x y = Φ.val.2 x y) := by
  let K := LocalField F (.inr p)
  letI : IsUltrametricDist K := inferInstanceAs (IsUltrametricDist (p.adicCompletion F))
  let det (q : K × K) := q.1*b-a*q.2
  let B := Metric.closedBall z (‖z‖/2)
  let S := det ⁻¹' B
  have hB : IsClopen B := IsUltrametricDist.isClopen_closedBall z (half_pos (norm_pos_iff.mpr hz)).ne'
  have hS : IsClopen S := hB.preimage ((continuous_fst.mul_const b).sub (continuous_snd.const_mul a) : Continuous det)
  have hzB : z ∈ B := Metric.mem_closedBall_self (half_pos (norm_pos_iff.mpr hz)).le
  have h₀ : (0 : K × K) ∉ S := by
    change ¬ dist ((0 : K)*b-a*0) z ≤ ‖z‖/2
    simp [half_lt_self (norm_pos_iff.mpr hz)]
  let χ (q : K × K) : ℂ := if q ∈ S then 1 else 0
  have hl : IsLocallyConstant χ := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro q
    by_cases hq : q ∈ S
    · filter_upwards [hS.isOpen.mem_nhds hq] with w hw
      simp [χ,hw,hq]
    · filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hq] with w hw
      simp [χ,show w ∉ S from hw,hq]
  let f : Charts K := (fun x y => χ (x.val,y)*Φ.val.1 x y, fun x y => χ (x,y.val)*Φ.val.2 x y)
  obtain ⟨hx,hy⟩ := d.locallyConstant_finite_schwartz p Φ
  obtain ⟨L,hL⟩ := d.exists_leading_finite p
  obtain ⟨C,hC,ho⟩ := (d.finite_support_and_germ_of_isLeadingTerm p Φ (hL Φ)).1
  have hX (q : K × K) : xChart f q = χ q*xChart Φ.val q := by
    rcases q with ⟨x,y⟩
    by_cases h : x ≠ 0 <;> simp [xChart,f,h]
  have hY (q : K × K) : yChart f q = χ q*yChart Φ.val q := by
    rcases q with ⟨x,y⟩
    by_cases h : y ≠ 0 <;> simp [yChart,f,h]
  refine ⟨f,⟨?_,?_⟩,?_,?_⟩
  · intro x y
    change χ (x.val,y.val) * Φ.val.1 x y.val = _ * (χ (x.val,y.val) * Φ.val.2 x.val y)
    rw [d.schwartz_glues _ Φ x y,mul_left_comm]
  · change finiteTest f
    refine ⟨(hl.comp_continuous ((Units.continuous_val.comp continuous_fst).prodMk continuous_snd)).mul hx,
      (hl.comp_continuous (continuous_fst.prodMk (Units.continuous_val.comp continuous_snd))).mul hy,
      C ∩ S,hC.inter_right hS.isClosed,fun h => h₀ h.2,?_⟩
    intro q hq
    rw [hX,hY]
    by_cases hs : q ∈ S
    · obtain ⟨hx,hy⟩ := ho q (fun h => hq ⟨h,hs⟩)
      simp [hx,hy]
    · simp [χ,hs]
  · intro x y h
    have hs : (x.val,y) ∈ S := show x.val*b-a*y ∈ B from h.symm ▸ hzB
    simp [f,χ,hs]
  · intro x y h
    have hs : (x,y.val) ∈ S := show x*b-a*y.val ∈ B from h.symm ▸ hzB
    simp [f,χ,hs]

/-- At every finite place the inner integrals in the transform of a Schwartz
section converge absolutely for each nonzero line parameter. -/
theorem finite_schwartz_line_integrals (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    (t : LocalField F (.inr p)) (ht : t ≠ 0) :
    let v : Place F := .inr p
    let dx := selfDual F d.character v
    (∀ a b, Integrable (lineIntegrandX (d.symbol v) Φ.val n t a b) dx) ∧
    (∀ a b, Integrable (lineIntegrandY (d.symbol v) Φ.val n t a b) dx) := by
  constructor
  · intro a b
    obtain ⟨f,hf,hx,_⟩ := d.finite_test_on_line p Φ a.val b (t^n) (pow_ne_zero _ ht)
    apply ((d.finiteTest_line_integrals p hf t).1 a b).congr
    filter_upwards with x
    by_cases h : x ≠ 0
    · simp only [lineIntegrandX,dif_pos h]
      rw [hx _ _ (by simp only [Units.val_mk0]; field_simp; ring)]
    · simp [lineIntegrandX,h]
  · intro a b
    obtain ⟨f,hf,_,hy⟩ := d.finite_test_on_line p Φ a b.val (t^n) (pow_ne_zero _ ht)
    apply ((d.finiteTest_line_integrals p hf t).2 a b).congr
    filter_upwards with y
    by_cases h : y ≠ 0
    · simp only [lineIntegrandY,dif_pos h]
      rw [hy _ _ (by simp only [Units.val_mk0]; field_simp; ring)]
    · simp [lineIntegrandY,h]

end Datum
end MetaplecticPoisson
