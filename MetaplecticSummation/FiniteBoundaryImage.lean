import MetaplecticSummation.Jacquet.PowerAverage
import MetaplecticSummation.FiniteGerms
import Mathlib.LinearAlgebra.Isomorphisms

/-! The image of the leading term at a finite place (§8). -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- Every finite-place leading term is already the leading term of a single
transformed test section. The untransformed generators have leading term zero. -/
theorem finite_leading_range (p : HeightOneSpectrum (𝓞 F)) :
    let v : Place F := .inr p
    (d.leading v).range = (d.leading v).ker.map ((d.leading v).comp (d.fourier v)) := by
  let v : Place F := .inr p
  let B := d.leading v
  let V := B.ker.map (B.comp (d.fourier v))
  apply le_antisymm
  · rintro _ ⟨Φ,rfl⟩
    change B Φ ∈ V
    refine Submodule.span_induction (p := fun f hf => B ⟨f,hf⟩ ∈ V) ?_ ?_ ?_ ?_ Φ.property
    · rintro f (hf | ⟨g,hg,rfl⟩)
      · rw [show B ⟨f,_⟩ = 0 from d.leading_finiteTest_eq_zero p _ hf]
        exact V.zero_mem
      · let Ψ : d.schwartz v := ⟨g,Submodule.subset_span (Or.inl hg)⟩
        exact ⟨Ψ,d.leading_finiteTest_eq_zero p Ψ hg,
          congrArg B (Subtype.ext (d.fourier_apply v Ψ))⟩
    · change B 0 ∈ V
      rw [map_zero]
      exact V.zero_mem
    · intro f g hf hg H J
      change B (⟨f,hf⟩ + ⟨g,hg⟩) ∈ V
      rw [map_add]
      exact V.add_mem H J
    · intro a f hf H
      change B (a • ⟨f,hf⟩) ∈ V
      rw [map_smul]
      exact V.smul_mem a H
  · rintro _ ⟨Φ,_,rfl⟩
    exact ⟨d.fourier v Φ,rfl⟩

open Filter Set Metric
open scoped Topology
open Classical

private theorem locallyConstant_dilated_charts {K : Type} [NontriviallyNormedField K] [ProperSpace K]
    [IsUltrametricDist K] {f : Kˣ → K → ℂ} (hl : IsLocallyConstant (Function.uncurry f))
    {C : Set (K×K)} (hC : IsCompact C) (h0 : (0 : K×K) ∉ C)
    (ho : ∀ (x : Kˣ) (y : K), (x.val,y) ∉ C → f x y = 0) :
    IsLocallyConstant (fun q : Kˣ × K => fun a : Kˣ => f (a*q.1) (a.val*q.2)) := by
  let G (z : (Kˣ×K)×K) := if z.2 = 0 then 0 else f (liftUnit z.2 * z.1.1) (z.2*z.1.2)
  let pt (z : (Kˣ×K)×K) : K×K := (z.2*z.1.1.val,z.2*z.1.2)
  have cp : Continuous pt := by dsimp [pt]; fun_prop
  have out (z : (Kˣ×K)×K) (hz : pt z ∉ C) : G z = 0 := by
    by_cases h : z.2 = 0
    · simp [G,h]
    · simp only [G,if_neg h]
      apply ho
      simpa [pt,liftUnit,h] using hz
  have hG : IsLocallyConstant G := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    by_cases hz : z.2 = 0
    · have hpt : pt z ∉ C := by simpa [pt,hz] using (show (0,0) ∉ C from h0)
      filter_upwards [cp.continuousAt.eventually (hC.isClosed.isOpen_compl.mem_nhds hpt)] with w hw
      exact (out w hw).trans (out z hpt).symm
    · have ha := (liftUnit_continuousAt hz).comp (continuous_snd (X := Kˣ×K)).continuousAt
      have c : ContinuousAt (fun w : (Kˣ×K)×K => (liftUnit w.2*w.1.1,w.2*w.1.2)) z :=
        (ha.mul (continuous_fst.comp continuous_fst).continuousAt).prodMk
          (continuous_snd.mul (continuous_snd.comp continuous_fst)).continuousAt
      filter_upwards [continuous_snd.continuousAt.eventually (eventually_ne_nhds hz),
        c.eventually (hl.eventually_eq _)] with w hw he
      simpa only [G,if_neg hw,if_neg hz,Function.uncurry] using he
  have slices := locallyConstant_slices_of_localSupport hG (by
    intro q
    obtain ⟨B,hB⟩ := (hC.image continuous_fst).isBounded.exists_norm_le
    refine ⟨closedBall 0 (B / ‖q.1.val‖),isCompact_closedBall ..,?_⟩
    filter_upwards [((locallyConstant_norm_units.comp_continuous continuous_fst).eventually_eq q)] with w hw
    intro a ha
    apply out
    intro hin
    have h := hB _ (mem_image_of_mem Prod.fst hin)
    have hpos := norm_pos_iff.mpr q.1.ne_zero
    apply ha
    rw [mem_closedBall_zero_iff,le_div_iff₀ hpos]
    change ‖w.1.val‖ = ‖q.1.val‖ at hw
    simpa only [pt,norm_mul,hw] using h)
  simpa only [Function.comp_def,G,if_neg (Units.ne_zero _),liftUnit,dif_pos (Units.ne_zero _),Units.mk0_val] using
    slices.comp (fun r : K → ℂ => fun a : Kˣ => r a.val)

omit [NeZero n] in
/-- At finite places both charts of the power average are locally constant,
including on the coordinate axes. -/
theorem locallyConstant_powerAverage (p : HeightOneSpectrum (𝓞 F)) {f : Charts (LocalField F (.inr p))}
    (hf : finiteTest f) :
    IsLocallyConstant (Function.uncurry (d.powerAverage (.inr p) f).1) ∧
    IsLocallyConstant (Function.uncurry (d.powerAverage (.inr p) f).2) := by
  let v : Place F := .inr p
  let K := p.adicCompletion F
  letI := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace (p.adicCompletion F) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)
  let avg (r : Kˣ → ℂ) := d.lineIntegral v fun a =>
    if ∃ t : Kˣ, a=t^n then ((modulus F v a.val ^ (1+1/(n:ℝ)) : ℝ) : ℂ)*r a else 0
  obtain ⟨hX,hY,C,hC,h0,ho⟩ := hf
  constructor
  · have hout (x : Kˣ) (y : K) (hx : (x.val,y) ∉ C) : f.1 x y = 0 := by
      simpa [xChart,x.ne_zero] using (ho (x.val,y) hx).1
    exact (locallyConstant_dilated_charts (K := p.adicCompletion F) (f := f.1) hX hC h0 hout).comp avg
  · have hswap : (0 : K × K) ∉ Prod.swap '' C := by
      rintro ⟨⟨x,y⟩,hxy,e⟩
      have he : (x,y) = (0,0) := congrArg Prod.swap e
      apply h0
      change (0,0) ∈ C
      rwa [← he]
    have L := locallyConstant_dilated_charts (K := p.adicCompletion F) (f := fun a b => f.2 b a)
      (hY.comp_continuous continuous_swap) (hC.image continuous_swap) hswap (by
        intro x y hx
        have ho' : (y,x.val) ∉ C := fun hh => hx ⟨_,hh,rfl⟩
        simpa [yChart,x.ne_zero] using (ho (y,x.val) ho').2)
    have LL : IsLocallyConstant (fun z : Kˣ × K => avg (fun a => f.2 (a.val*z.2) (a*z.1))) := L.comp avg
    have hy := LL.comp_continuous (continuous_swap : Continuous (Prod.swap : K × Kˣ → Kˣ × K))
    exact hy

/-- The finite-place leading-term range is precisely the set of intertwiners
of power averages of test sections. The normalization in Lemma 8.3 can be
absorbed by scaling the test section. -/
theorem finite_leading_eq_intertwiner_average (p : HeightOneSpectrum (𝓞 F))
    (g : Charts (LocalField F (.inr p))) :
    let v : Place F := .inr p
    g ∈ (d.leading v).range ↔ ∃ Φ : d.schwartz v, Φ.val ∈ d.testSet v ∧
      g = d.intertwiner v (d.powerAverage v Φ.val) := by
  let v : Place F := .inr p
  let K := LocalField F v
  let B := d.leading v
  let M := (modulus F v (n:K))^(3/2:ℝ)
  let c : ℂ := (n:ℂ)/(M:ℂ)
  have hn : (n:K) ≠ 0 := by
    simpa only [map_natCast,map_zero] using
      (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n:F) ≠ 0)
  have hp : 0 < M := Real.rpow_pos_of_pos (norm_pos_iff.mpr hn) _
  have hc : c ≠ 0 := div_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne n)) (Complex.ofReal_ne_zero.mpr hp.ne')
  constructor
  · intro hg
    rw [d.finite_leading_range p] at hg
    obtain ⟨Φ,hΦ,rfl⟩ := hg
    change B Φ = 0 at hΦ
    have ht : (c • Φ).val ∈ d.testSet v := (d.finite_germs p (c • Φ)).1.mp (by
      change B (c • Φ) = 0
      rw [map_smul,hΦ,smul_zero])
    refine ⟨c • Φ,ht,?_⟩
    have H := d.leading_fourier_test v (c • Φ) ht
    change B ((d.fourier v) (c • Φ)) = c • _ at H
    rw [map_smul,map_smul] at H
    exact (smul_right_injective _ hc) H
  · rintro ⟨Φ,hΦ,rfl⟩
    refine ⟨c⁻¹ • d.fourier v Φ,?_⟩
    rw [map_smul,d.leading_fourier_test v Φ hΦ]
    change c⁻¹ • c • _ = _
    rw [inv_smul_smul₀ hc]

/-- The forward image assertion of Corollary 8.4. -/
theorem finite_leading_intertwiner (p : HeightOneSpectrum (𝓞 F)) (g : Charts (LocalField F (.inr p)))
    (hg : g ∈ (d.leading (.inr p)).range) :
    let v : Place F := .inr p
    ∃ f : Charts (LocalField F v), Glues (d.symbol v) f ∧
      IsLocallyConstant (Function.uncurry f.1) ∧ IsLocallyConstant (Function.uncurry f.2) ∧
      (∀ u : (LocalField F v)ˣ, dilateCharts (u^n) f =
        ((modulus F v (u^n).val ^ (-1-1/(n:ℝ)) : ℝ) : ℂ) • f) ∧ g = d.intertwiner v f := by
  obtain ⟨Φ,hΦ,rfl⟩ := (d.finite_leading_eq_intertwiner_average p g).mp hg
  obtain ⟨hx,hy⟩ := d.locallyConstant_powerAverage p hΦ.2
  exact ⟨_,d.powerAverage_glues _ hΦ.1,hx,hy,d.powerAverage_homogeneous _ _,rfl⟩

section Cutoff
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- Select a coordinate of maximal norm, using the first in case of a tie. -/
private def pivot (x y : K) : Kˣ := liftUnit (if ‖y‖ ≤ ‖x‖ then x else y)

omit [IsUltrametricDist K] in
private theorem pivot_ne {x y : K} (h : x ≠ 0 ∨ y ≠ 0) :
    (if ‖y‖ ≤ ‖x‖ then x else y) ≠ 0 := by
  split_ifs with hle
  · rintro rfl
    simp only [norm_zero,norm_le_zero_iff] at hle
    exact h.elim (fun hn => hn rfl) (fun hn => hn hle)
  · rintro rfl
    exact hle (by simp)

omit [IsUltrametricDist K] in
private theorem norm_pivot {x y : K} (h : x ≠ 0 ∨ y ≠ 0) :
    ‖(pivot x y).val‖ = max ‖x‖ ‖y‖ := by
  rw [pivot,liftUnit_val (pivot_ne h)]
  split_ifs with hle
  · exact (max_eq_left hle).symm
  · exact (max_eq_right (le_of_not_ge hle)).symm

omit [IsUltrametricDist K] in
private theorem pivot_mul (a : Kˣ) {x y : K} (h : x ≠ 0 ∨ y ≠ 0) :
    pivot (a.val*x) (a.val*y) = a*pivot x y := by
  have hp := norm_pos_iff.mpr a.ne_zero
  have hz := pivot_ne h
  apply Units.ext
  simp only [pivot,Units.val_mul,norm_mul,mul_le_mul_iff_right₀ hp]
  split_ifs at hz ⊢ <;> rw [liftUnit_val (mul_ne_zero a.ne_zero hz),liftUnit_val hz]

private theorem pivot_weight_lc {P : Type*} [TopologicalSpace P] {x y : P → K}
    (cx : Continuous x) (cy : Continuous y) (hne : ∀ p, x p ≠ 0 ∨ y p ≠ 0)
    {W : Kˣ → ℂ} (hW : IsLocallyConstant W) :
    IsLocallyConstant (fun p => W (pivot (x p) (y p))) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro p
  have stable (t : P → K) (ct : Continuous t) (ht : t p ≠ 0) :
      ∀ᶠ q in 𝓝 p, ‖t q‖ = ‖t p‖ ∧ W (liftUnit (t q)) = W (liftUnit (t p)) := by
    have c := (liftUnit_continuousAt ht).comp ct.continuousAt
    filter_upwards [c.eventually (locallyConstant_norm_units.eventually_eq (liftUnit (t p))),
      c.eventually (hW.eventually_eq _),ct.continuousAt.eventually (eventually_ne_nhds ht)] with q h₁ h₂ h₃
    exact ⟨by simpa only [Function.comp_apply,liftUnit_val h₃,liftUnit_val ht] using h₁,h₂⟩
  by_cases hx : x p = 0
  · have hy := (hne p).resolve_left (not_not.mpr hx)
    have lt : ‖x p‖ < ‖y p‖ := by simpa [hx] using norm_pos_iff.mpr hy
    filter_upwards [cx.norm.continuousAt.eventually_lt cy.norm.continuousAt lt,stable y cy hy] with q hq h
    simpa only [pivot,if_neg (not_le.mpr hq),if_neg (not_le.mpr lt)] using h.2
  · by_cases hy : y p = 0
    · have lt : ‖y p‖ < ‖x p‖ := by simpa [hy] using norm_pos_iff.mpr hx
      filter_upwards [cy.norm.continuousAt.eventually_lt cx.norm.continuousAt lt,stable x cx hx] with q hq h
      simpa only [pivot,if_pos hq.le,if_pos lt.le] using h.2
    · filter_upwards [stable x cx hx,stable y cy hy] with q h₁ h₂
      simp only [pivot,h₁.1,h₂.1]
      split_ifs <;> first | exact h₁.2 | exact h₂.2

private theorem cutoff_test [ProperSpace K] {W : Kˣ → ℂ} (hk : HasCompactSupport W) (hW : IsLocallyConstant W)
    {f : Charts K} (hX : IsLocallyConstant (Function.uncurry f.1)) (hY : IsLocallyConstant (Function.uncurry f.2)) :
    finiteTest ((fun x y => W (pivot x.val y)*f.1 x y),(fun x y => W (pivot x y.val)*f.2 x y)) := by
  have lx := pivot_weight_lc (Units.continuous_val.comp continuous_fst) continuous_snd
    (fun z : Kˣ×K => Or.inl z.1.ne_zero) hW
  have ly := pivot_weight_lc continuous_fst (Units.continuous_val.comp continuous_snd)
    (fun z : K×Kˣ => Or.inr z.2.ne_zero) hW
  let S := Units.val '' tsupport W
  have hS : IsCompact S := hk.image Units.continuous_val
  obtain ⟨B,hB⟩ := hS.isBounded.exists_norm_le
  let D := closedBall (0:K) B
  let C := S ×ˢ D ∪ D ×ˢ S
  have hz : (0:K) ∉ S := by rintro ⟨a,_,ha⟩; exact a.ne_zero ha
  have ho (x y : K) (hn : x ≠ 0 ∨ y ≠ 0) (hout : (x,y) ∉ C) : W (pivot x y) = 0 := by
    by_contra h
    have hs : (pivot x y).val ∈ S := mem_image_of_mem _ (subset_tsupport W h)
    have hb := hB _ hs
    rw [norm_pivot hn] at hb
    have hx : x ∈ D := mem_closedBall_zero_iff.mpr ((le_max_left ..).trans hb)
    have hy : y ∈ D := mem_closedBall_zero_iff.mpr ((le_max_right ..).trans hb)
    rw [pivot,liftUnit_val (pivot_ne hn)] at hs
    split_ifs at hs
    · exact hout (Or.inl ⟨hs,hy⟩)
    · exact hout (Or.inr ⟨hx,hs⟩)
  refine ⟨lx.mul hX,ly.mul hY,C,(hS.prod (isCompact_closedBall ..)).union ((isCompact_closedBall ..).prod hS),
    fun h => h.elim (fun h => hz h.1) (fun h => hz h.2),?_⟩
  rintro ⟨x,y⟩ hout
  constructor
  · by_cases hx : x = 0
    · simp [xChart,hx]
    · simp [xChart,hx,ho x y (Or.inl hx) hout]
  · by_cases hy : y = 0
    · simp [yChart,hy]
    · simp [yChart,hy,ho x y (Or.inr hy) hout]
end Cutoff

/-- Each power class has a compact test of mass one. Translating makes a
single cutoff work in every direction of the punctured plane. -/
private theorem finite_cutoff_mass (p : HeightOneSpectrum (𝓞 F)) :
    let v : Place F := .inr p
    ∃ W : Weight v, HasCompactSupport W ∧ IsLocallyConstant W ∧
      ∀ x : (LocalField F v)ˣ, d.lineIntegral v (fun a =>
        if ∃ u : (LocalField F v)ˣ, a=u^n then W (a*x) else 0) = 1 := by
  let v : Place F := .inr p
  let K := p.adicCompletion F
  letI := FinitePlace.nontriviallyNormedCompletion p
  obtain ⟨w,hw,H⟩ := d.exists_classMoment_vector v (fun _ => 1)
  let W (a : Kˣ) := w a * ((‖a.val‖ ^ (1/(n:ℝ)) : ℝ) : ℂ)
  have hl : IsLocallyConstant w := hw.2
  refine ⟨W,hw.1.mul_right,hl.mul (locallyConstant_norm_units.comp (fun r : ℝ => ((r ^ (1/(n:ℝ)) : ℝ) : ℂ))),?_⟩
  intro x
  let g (a : Kˣ) := if (QuotientGroup.mk a : PowerClass n v) = QuotientGroup.mk x then W a else 0
  have hi : d.lineIntegral v g = 1 := congrFun H (QuotientGroup.mk x)
  rw [← d.lineIntegral_mul v x g] at hi
  convert hi using 2
  funext a
  have coset : (QuotientGroup.mk (x*a) : PowerClass n v) = QuotientGroup.mk x ↔
      ∃ u : Kˣ, a=u^n := by
    rw [QuotientGroup.eq_iff_div_mem,mul_comm x a,mul_div_cancel_right]
    exact ⟨fun ⟨u,hu⟩ => ⟨u,hu.symm⟩,fun ⟨u,hu⟩ => ⟨u,hu.symm⟩⟩
  simp only [g,coset]
  rw [mul_comm x a]
  rfl

/-- Cutting off a locally constant homogeneous genuine function on the
punctured plane gives a test section whose power average recovers it. -/
theorem finite_exists_powerAverage (p : HeightOneSpectrum (𝓞 F)) (f : Charts (LocalField F (.inr p)))
    (hg : Glues (d.symbol (.inr p)) f)
    (hX : IsLocallyConstant (Function.uncurry f.1)) (hY : IsLocallyConstant (Function.uncurry f.2))
    (hh : ∀ u : (LocalField F (.inr p))ˣ, dilateCharts (u^n) f =
      ((modulus F (.inr p) (u^n).val ^ (-1-1/(n:ℝ)) : ℝ) : ℂ) • f) :
    ∃ Φ : d.schwartz (.inr p), Φ.val ∈ d.testSet (.inr p) ∧ d.powerAverage (.inr p) Φ.val = f := by
  let v : Place F := .inr p
  let K := p.adicCompletion F
  letI := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace (p.adicCompletion F) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  obtain ⟨W,hk,hW,hMass⟩ := d.finite_cutoff_mass p
  let Ψ : Charts K := ((fun x y => W (pivot x.val y) * f.1 x y),(fun x y => W (pivot x y.val) * f.2 x y))
  have hΨ : Ψ ∈ d.testSet v := by
    refine ⟨?_,cutoff_test (K := p.adicCompletion F) hk hW hX hY⟩
    intro x y
    change W _ * f.1 _ _ = _ * (W _ * f.2 _ _)
    rw [hg x y,mul_left_comm]
  refine ⟨⟨Ψ,Submodule.subset_span (Or.inl hΨ)⟩,hΨ,?_⟩
  let e := 1+1/(n:ℝ)
  have eval (x : Kˣ) (z : ℂ) (r : Kˣ → ℂ)
      (hr : ∀ u : Kˣ, r (u^n) = W (u^n*x) * (((‖(u^n).val‖ ^ (-e) : ℝ) : ℂ) * z)) :
      d.lineIntegral v (fun a => if ∃ u : Kˣ, a=u^n then ((‖a.val‖^e : ℝ) : ℂ)*r a else 0) = z := by
    calc
      _ = z * d.lineIntegral v (fun a : Kˣ => if ∃ u : Kˣ, a=u^n then W (a*x) else 0) := by
        rw [← d.lineIntegral_const_mul]
        congr 1
        apply funext
        intro a
        change Kˣ at a
        change (if ∃ u : Kˣ, a=u^n then ((‖a.val‖^e : ℝ) : ℂ)*r a else 0) =
          z * (if ∃ u : Kˣ, a=u^n then W (a*x) else 0)
        split_ifs with ha
        · obtain ⟨u,rfl⟩ := ha
          have pos := norm_pos_iff.mpr (u^n).ne_zero
          rw [hr,Real.rpow_neg pos.le,Complex.ofReal_inv]
          let q : ℂ := ((‖(u^n).val‖ ^ e : ℝ) : ℂ)
          have hn : q ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos pos e).ne'
          change q * (W (u^n*x) * (q⁻¹*z)) = z * W (u^n*x)
          calc
            _ = (q*q⁻¹)*(z*W (u^n*x)) := by ring
            _ = _ := by rw [mul_inv_cancel₀ hn,one_mul]
        · rw [mul_zero]
      _ = z := (congrArg (z * ·) (hMass x)).trans (mul_one z)
  have expo : -1-1/(n:ℝ) = -e := by dsimp [e]; ring
  apply Prod.ext <;> funext x y
  · change Kˣ at x
    change K at y
    apply eval (pivot x.val y) (f.1 x y) (fun a => (dilateCharts a Ψ).1 x y)
    intro u
    have he := congrFun (congrFun (congrArg Prod.fst (hh u)) x) y
    simp only [Prod.smul_fst,Pi.smul_apply,smul_eq_mul,expo] at he
    change W (pivot ((u^n).val*x.val) ((u^n).val*y)) * (dilateCharts (u^n) f).1 x y = _
    rw [pivot_mul _ (Or.inl x.ne_zero)]
    exact congrArg (W _ * ·) he
  · change K at x
    change Kˣ at y
    apply eval (pivot x y.val) (f.2 x y) (fun a => (dilateCharts a Ψ).2 x y)
    intro u
    have he := congrFun (congrFun (congrArg Prod.snd (hh u)) x) y
    simp only [Prod.smul_snd,Pi.smul_apply,smul_eq_mul,expo] at he
    change W (pivot ((u^n).val*x) ((u^n).val*y.val)) * (dilateCharts (u^n) f).2 x y = _
    rw [pivot_mul _ (Or.inr y.ne_zero)]
    exact congrArg (W _ * ·) he

/-- Corollary 8.4, identifying the range of the finite-place leading term. -/
theorem finite_boundary_image (p : Prime F) (g : Charts (LocalField F (.inr p))) :
    let v : Place F := .inr p
    g ∈ LinearMap.range (d.leading v) ↔ ∃ f : Charts (LocalField F v),
      Glues (d.symbol v) f ∧ IsLocallyConstant (fun z : (LocalField F v)ˣ × LocalField F v => f.1 z.1 z.2) ∧
      IsLocallyConstant (fun z : LocalField F v × (LocalField F v)ˣ => f.2 z.1 z.2) ∧
      (∀ u : (LocalField F v)ˣ, dilateCharts (u^n) f =
        ((modulus F v (u^n : (LocalField F v)ˣ) ^ (-1-1/(n : ℝ)) : ℝ) : ℂ) • f) ∧
      g = d.intertwiner v f := by
  constructor
  · exact d.finite_leading_intertwiner p g
  · rintro ⟨f,gl,hx,hy,hh,rfl⟩
    obtain ⟨Φ,hΦ,rfl⟩ := d.finite_exists_powerAverage p f gl hx hy hh
    exact (d.finite_leading_eq_intertwiner_average p _).mpr ⟨Φ,hΦ,rfl⟩

/-- The subspace of finite-place Schwartz sections which are test sections. -/
def finiteTestSpace (p : HeightOneSpectrum (𝓞 F)) : Submodule ℂ (d.schwartz (.inr p)) :=
  (d.leading (.inr p)).ker.copy {Φ | Φ.val ∈ d.testSet (.inr p)}
    (Set.ext fun Φ => (d.finite_germs p Φ).1.symm)

/-- The quotient by test sections, identified with the image described in Corollary 8.4. -/
def finiteLeadingEquiv (p : HeightOneSpectrum (𝓞 F)) :
    (d.schwartz (.inr p) ⧸ d.finiteTestSpace p) ≃ₗ[ℂ] (d.leading (.inr p)).range :=
  (Submodule.quotEquivOfEq _ _ (Submodule.copy_eq _ _ _)).trans (d.leading (.inr p)).quotKerEquivRange

@[simp] theorem finiteLeadingEquiv_mk (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p)) :
    (d.finiteLeadingEquiv p (Submodule.Quotient.mk Φ)).val = d.leading (.inr p) Φ := rfl

/-- The support and germ criterion of Corollary 8.4. The preceding image
formula identifies exactly which intertwiners occur as the germ. -/
theorem finite_schwartz_iff_germ (p : HeightOneSpectrum (𝓞 F)) (f : Charts (LocalField F (.inr p)))
    (gl : Glues (d.symbol (.inr p)) f)
    (hx : IsLocallyConstant (Function.uncurry f.1)) (hy : IsLocallyConstant (Function.uncurry f.2)) :
    let v : Place F := .inr p
    let K := LocalField F v
    f ∈ d.schwartz v ↔
      (∃ C : Set (K×K), IsCompact C ∧ ∀ z ∉ C, xChart f z = 0 ∧ yChart f z = 0) ∧
      ∃ g ∈ (d.leading v).range, ∀ᶠ z in 𝓝 (0 : K×K),
        xChart f z = xChart g z ∧ yChart f z = yChart g z := by
  let v : Place F := .inr p
  let K := LocalField F v
  constructor
  · intro hf
    let Φ : d.schwartz v := ⟨f,hf⟩
    obtain ⟨hC,hg⟩ := d.finite_support_and_germ p Φ
    exact ⟨hC,_,⟨Φ,rfl⟩,hg⟩
  · rintro ⟨⟨C,hC,hf⟩,g,⟨Φ,rfl⟩,hg⟩
    obtain ⟨⟨D,hD,hΦ⟩,hΦg⟩ := d.finite_support_and_germ p Φ
    have hnear : ∀ᶠ z in 𝓝 (0 : K×K), xChart f z = xChart Φ z ∧ yChart f z = yChart Φ z := by
      filter_upwards [hg,hΦg] with z h k
      exact ⟨h.1.trans k.1.symm,h.2.trans k.2.symm⟩
    obtain ⟨U,hU,hoU,h0⟩ := _root_.mem_nhds_iff.mp hnear
    obtain ⟨lx,ly⟩ := d.locallyConstant_finite_schwartz p Φ
    have test : f-Φ.val ∈ d.testSet v := by
      refine ⟨?_,hx.sub lx,hy.sub ly,(C ∪ D) \ U,(hC.union hD).diff hoU,fun h => h.2 h0,?_⟩
      · intro x y
        change f.1 x _ - Φ.val.1 x _ = _ * (f.2 _ y - Φ.val.2 _ y)
        rw [gl,d.schwartz_glues v Φ,mul_sub]
      · intro z hz
        have eqs : xChart f z = xChart Φ z ∧ yChart f z = yChart Φ z := by
          by_cases h : z ∈ U
          · exact hU h
          · have out : z ∉ C ∪ D := fun hCD => hz ⟨hCD,h⟩
            have e := hf z fun hc => out (Or.inl hc)
            have k := hΦ z fun hd => out (Or.inr hd)
            exact ⟨e.1.trans k.1.symm,e.2.trans k.2.symm⟩
        have ex : xChart (f-Φ.val) z = xChart f z - xChart Φ z := by
          simp only [xChart]; split_ifs <;> simp
        have ey : yChart (f-Φ.val) z = yChart f z - yChart Φ z := by
          simp only [yChart]; split_ifs <;> simp
        exact ⟨by rw [ex,eqs.1,sub_self],by rw [ey,eqs.2,sub_self]⟩
    have mem : f-Φ.val ∈ d.schwartz v := Submodule.subset_span (Or.inl test)
    simpa only [sub_add_cancel] using (d.schwartz v).add_mem mem Φ.property

end MetaplecticPoisson.Datum
