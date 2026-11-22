import MetaplecticSummation.FiniteRays
import MetaplecticSummation.Schwartz

/-! Compact support and agreement with the leading term on a neighborhood
of the origin, at a finite place (§8). -/

noncomputable section
namespace MetaplecticPoisson
open Filter Set Metric
open scoped Topology
open Classical

variable {K : Type} [NontriviallyNormedField K] {n : ℕ}

/-- A compact subset of the dominant-coordinate chart meets every power ray
in that cone. The normalized dominant coordinate has norm between 1 and B. -/
private theorem compact_ray_shell [ProperSpace K] (hn : n ≠ 0) :
    ∃ (T : Set (Kˣ × K)) (B : ℝ), IsCompact T ∧ 0 < B ∧
    ∀ (a : Kˣ) (b : K), ‖b‖ ≤ ‖a.val‖ → ∃ (q : Kˣ × K) (u : Kˣ), q ∈ T ∧
      (u^n*q.1,u.val^n*q.2) = (a,b) ∧ ‖u.val‖^n ≤ ‖a.val‖ ∧ ‖a.val‖ ≤ B * ‖u.val‖^n := by
  obtain ⟨c,hc⟩ := NormedField.exists_one_lt_norm K
  let B := ‖c‖^n
  have hB : 1 < B := one_lt_pow₀ hc hn
  let A := closedBall (0:K) B ∩ {x : K | 1 ≤ ‖x‖}
  have hA : IsCompact A := (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  have hA' := Units.isEmbedding_val₀.isInducing.isCompact_preimage' hA (by
    intro x hx
    have hnz : x ≠ 0 := by
      rintro rfl
      exact (not_le_of_gt zero_lt_one) (by simpa using hx.2)
    exact ⟨Units.mk0 x hnz,rfl⟩)
  refine ⟨_ ×ˢ closedBall 0 B,B,hA'.prod (isCompact_closedBall _ _),zero_lt_one.trans hB,?_⟩
  intro a b hab
  obtain ⟨j,hj₁,hj₂⟩ := exists_mem_Ico_zpow (norm_pos_iff.mpr a.ne_zero) hB
  let u := (Units.mk0 c (norm_pos_iff.mp (zero_lt_one.trans hc))) ^ j
  have hu : ‖u.val‖^n = B^j := by
    simp only [u,Units.val_zpow_eq_zpow_val,Units.val_mk0,norm_zpow,B]
    rw [← zpow_natCast, ← zpow_natCast (‖c‖), ← zpow_mul, ← zpow_mul, mul_comm]
  have hval : ‖a.val‖ ≤ B * ‖u.val‖^n := by
    rw [hu,mul_comm,← zpow_add_one₀ (ne_of_gt (zero_lt_one.trans hB))]
    exact hj₂.le
  have hpos : 0 < ‖u.val‖^n := pow_pos (norm_pos_iff.mpr u.ne_zero) _
  let q : Kˣ × K := (a/u^n,b/u.val^n)
  have hq : ‖q.1.val‖ = ‖a.val‖ / ‖u.val‖^n := by simp [q,norm_div,norm_pow]
  refine ⟨q,u,⟨⟨?_,?_⟩,?_⟩,?_,hu ▸ hj₁,hval⟩
  · change q.1.val ∈ closedBall 0 B
    simpa [mem_closedBall,dist_zero_right,hq] using (div_le_iff₀ hpos).mpr hval
  · change 1 ≤ ‖q.1.val‖
    rw [hq,one_le_div hpos,hu]
    exact hj₁
  · simpa [q,mem_closedBall,dist_zero_right,norm_div,norm_pow] using (div_le_iff₀ hpos).mpr (hab.trans hval)
  · dsimp [q]
    ext <;> simp [field]

/-- Evaluation at frequency zero of a ray extension determines the leading
term at every dilate of the base point. -/
private theorem ray_extension_zero {P : Type*} [TopologicalSpace P] {dil : Kˣ → P → P}
    (hd : ∀ (s u : Kˣ) q, dil (s*u) q = dil s (dil u q))
    {E : P → K → ℂ} {f g : P → ℂ} (hE : SmoothFiniteFamily E)
    (hf : ∀ q (u : Kˣ), E q u.val = (‖u.val‖ : ℂ)^(n-1) * f (dil u q))
    (hl : ∀ q, Tendsto (fun s : Kˣ => (‖s.val‖ : ℂ)^(n-1) * f (dil s q))
      (comap Units.val (𝓝 0)) (𝓝 (g q))) (q : P) (u : Kˣ) :
    E q 0 = (‖u.val‖ : ℂ)^(n-1) * g (dil u q) := by
  letI : NeBot (comap (fun u : Kˣ => u.val) (𝓝 0)) := units_neBot_at_zero
  have hc : Continuous (E q) := (hE.1.comp_continuous (continuous_const.prodMk continuous_id)).continuous
  have ht : Tendsto (fun s : Kˣ => E q (s.val*u.val)) (comap Units.val (𝓝 0)) (𝓝 (E q 0)) := by
    apply (hc.tendsto 0).comp
    simpa only [zero_mul] using (tendsto_comap (f := fun s : Kˣ => s.val) (x := 𝓝 0)).mul_const u.val
  have he := (hl (dil u q)).const_mul ((‖u.val‖ : ℂ)^(n-1))
  have ht' := ht.congr (f₂ := fun s : Kˣ => (‖u.val‖ : ℂ)^(n-1) * ((‖s.val‖ : ℂ)^(n-1) * f (dil s (dil u q)))) (fun s => by
    change E q (s*u).val = _
    rw [hf,hd,Units.val_mul,norm_mul,Complex.ofReal_mul,mul_pow]
    ring)
  exact tendsto_nhds_unique ht' he

/-- Uniform support and constancy of the ray extensions imply the corresponding
bounds on the cone covered by a compact set of representatives. -/
private theorem ray_bounds {P : Type*} [TopologicalSpace P] {dil : Kˣ → P → P}
    (hd : ∀ (s u : Kˣ) q, dil (s*u) q = dil s (dil u q))
    {f g : P → ℂ} (hext : HasFiniteRayExtension n dil f)
    (hl : ∀ q, Tendsto (fun s : Kˣ => (‖s.val‖ : ℂ)^(n-1) * f (dil s q))
      (comap Units.val (𝓝 0)) (𝓝 (g q))) {T : Set P} (hT : IsCompact T) (B : ℝ) :
    ∃ R δ : ℝ, 0 < δ ∧ ∀ q ∈ T, ∀ u : Kˣ,
      (R < B * ‖u.val‖^n → f (dil u q) = 0) ∧
      (‖u.val‖^n < δ → f (dil u q) = g (dil u q)) := by
  obtain ⟨E,hE,hf⟩ := hext
  obtain ⟨C,hC,ho⟩ := (hE.2 T hT).2.1
  obtain ⟨M,hM⟩ := hC.isBounded.exists_norm_le
  obtain ⟨r,hr,hper⟩ := Metric.mem_nhds_iff.mp ((hE.2 T hT).2.2)
  refine ⟨max B 0 * (max M 0)^n,r^n,pow_pos hr _,?_⟩
  intro q hq u
  have hne : (‖u.val‖ : ℂ)^(n-1) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr u.ne_zero))
  constructor
  · intro h
    have hu : u.val ∉ C := by
      intro hc
      exact h.not_ge (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (norm_nonneg _) ((hM _ hc).trans (le_max_left _ _)) _)
        (pow_nonneg (norm_nonneg _) _) (le_max_right _ _))
    exact (mul_eq_zero.mp ((hf q u).symm.trans (ho q hq _ hu))).resolve_left hne
  · intro hu
    have hut : u.val ∈ ball (0:K) r := by
      rw [mem_ball_zero_iff]
      exact lt_of_not_ge fun h => hu.not_ge (pow_le_pow_left₀ hr.le h n)
    have hz := ray_extension_zero hd hE hf hl q u
    apply mul_left_cancel₀ hne
    rw [← hf, ← hz]
    simpa using hper hut q hq 0


private theorem ray_leading_properties {P : Type*} [TopologicalSpace P] {dil : Kˣ → P → P}
    (hd : ∀ (s u : Kˣ) q, dil (s*u) q = dil s (dil u q)) (h1 : ∀ q, dil 1 q = q)
    {f g : P → ℂ} (hext : HasFiniteRayExtension n dil f)
    (hl : ∀ q, Tendsto (fun s : Kˣ => (‖s.val‖ : ℂ)^(n-1) * f (dil s q))
      (comap Units.val (𝓝 0)) (𝓝 (g q))) :
    IsLocallyConstant g ∧ ∀ q (u : Kˣ), (‖u.val‖ : ℂ)^(n-1) * g (dil u q) = g q := by
  obtain ⟨E,hE,hf⟩ := hext
  have h := ray_extension_zero hd hE hf hl
  have h0 (q : P) : E q 0 = g q := by simpa [h1] using h q 1
  constructor
  · have hc : IsLocallyConstant (fun q => E q 0) := hE.1.comp_continuous (continuous_id.prodMk continuous_const)
    simpa only [h0] using hc
  · exact fun q u => (h q u).symm.trans (h0 q)

private theorem cone_bounds [ProperSpace K] {P : Type*} [TopologicalSpace P] {dil : Kˣ → P → P}
    (hd : ∀ (s u : Kˣ) q, dil (s*u) q = dil s (dil u q))
    (i : Kˣ × K → P) (hi : Continuous i)
    (hiu : ∀ u q, dil u (i q) = i (u^n*q.1,u.val^n*q.2)) (hn : n ≠ 0)
    {f g : P → ℂ} (hext : HasFiniteRayExtension n dil f)
    (hl : ∀ q, Tendsto (fun s : Kˣ => (‖s.val‖ : ℂ)^(n-1) * f (dil s q))
      (comap Units.val (𝓝 0)) (𝓝 (g q))) :
    ∃ R δ : ℝ, 0 < δ ∧ ∀ (a : Kˣ) (b : K), ‖b‖ ≤ ‖a.val‖ →
      (R < ‖a.val‖ → f (i (a,b)) = 0) ∧ (‖a.val‖ < δ → f (i (a,b)) = g (i (a,b))) := by
  obtain ⟨T,B,hT,_,hs⟩ := compact_ray_shell (K := K) hn
  obtain ⟨R,δ,hδ,h⟩ := ray_bounds hd hext hl (hT.image hi) B
  refine ⟨R,δ,hδ,?_⟩
  intro a b hab
  obtain ⟨q,u,hq,hqu,hlo,hhi⟩ := hs a b hab
  have hq' := h (i q) ⟨q,hq,rfl⟩ u
  rw [hiu,hqu] at hq'
  exact ⟨fun hr => hq'.1 (hr.trans_le hhi),fun hr => hq'.2 (hlo.trans_lt hr)⟩

private theorem chart_eq_of_dominant {h : Kˣ → Kˣ → ℂ} (hn : ∀ x y, h x y ≠ 0)
    {f g : Charts K} (hf : Glues h f) (hg : Glues h g) (z : K × K)
    (hx : ∀ a : Kˣ, a.val = z.1 → ‖z.2‖ ≤ ‖z.1‖ → f.1 a z.2 = g.1 a z.2)
    (hy : ∀ b : Kˣ, b.val = z.2 → ‖z.1‖ ≤ ‖z.2‖ → f.2 z.1 b = g.2 z.1 b) :
    xChart f z = xChart g z ∧ yChart f z = yChart g z := by
  rcases z with ⟨x,y⟩
  by_cases h₁ : x = 0
  · subst x
    by_cases h₂ : y = 0
    · simp [h₂,xChart,yChart]
    · simpa [xChart,yChart,h₂] using hy (Units.mk0 y h₂) rfl (by simp)
  by_cases h₂ : y = 0
  · subst y
    simpa [xChart,yChart,h₁] using hx (Units.mk0 x h₁) rfl (by simp)
  let a := Units.mk0 x h₁
  let b := Units.mk0 y h₂
  simp only [xChart,yChart,h₁,h₂,ne_eq,not_false_eq_true,dif_pos]
  change f.1 a b.val = g.1 a b.val ∧ f.2 a.val b = g.2 a.val b
  rcases le_total ‖y‖ ‖x‖ with hle | hle
  · have e := hx a rfl hle
    exact ⟨e,mul_left_cancel₀ (hn a b) ((hf a b).symm.trans (e.trans (hg a b)))⟩
  · have e := hy b rfl hle
    exact ⟨(hf a b).trans ((congrArg (h a b * ·) e).trans (hg a b).symm),e⟩

namespace Datum
open NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] [NeZero n] (d : Datum F n)

theorem finite_leading_glues (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    {g : Charts (LocalField F (.inr p))} (hg : IsLeadingTerm n (modulus F (.inr p)) Φ.val g) :
    Glues (d.symbol (.inr p)) g := by
  let v : Place F := .inr p
  let K := LocalField F v
  letI : NontriviallyNormedField K := FinitePlace.nontriviallyNormedCompletion p
  letI : NeBot (comap (fun u : Kˣ => u.val) (𝓝 0)) := units_neBot_at_zero
  let H := d.lineSymbol v (d.finite_steinberg p)
  intro x y
  have he (s : Kˣ) : d.symbol v (s^n*x) (s^n*y) = d.symbol v x y := by
    change ((H.pairing _ _ : ℂˣ) : ℂ) = (H.pairing x y : ℂ)
    simp [map_mul,MonoidHom.mul_apply]
    exact congrArg Units.val (H.torsion s y)
  apply tendsto_nhds_unique (hg.1 x y.val)
  apply ((hg.2 x.val y).const_mul (d.symbol v x y)).congr
  intro s
  have gl := d.schwartz_glues v Φ (s^n*x) (s^n*y)
  rw [he] at gl
  simp only [Units.val_mul,Units.val_pow_eq_pow_val] at gl
  rw [gl,mul_left_comm]

/-- Smoothness and homogeneity of degree (1−n) in the power-ray parameter. -/
theorem finite_leading_properties (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p)) :
    let K := LocalField F (.inr p)
    let g := d.leading (.inr p) Φ
    (IsLocallyConstant (fun q : Kˣ × K => g.1 q.1 q.2) ∧
      ∀ (a : Kˣ) (b : K) (u : Kˣ), (‖u.val‖ : ℂ)^(n-1) * g.1 (u^n*a) (u.val^n*b) = g.1 a b) ∧
    (IsLocallyConstant (fun q : K × Kˣ => g.2 q.1 q.2) ∧
      ∀ (a : K) (b u : Kˣ), (‖u.val‖ : ℂ)^(n-1) * g.2 (u.val^n*a) (u^n*b) = g.2 a b) := by
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  let K := p.adicCompletion F
  let X (s : Kˣ) (q : Kˣ × K) := (s^n*q.1,s.val^n*q.2)
  let Y (s : Kˣ) (q : K × Kˣ) := (s.val^n*q.1,s^n*q.2)
  obtain ⟨ex,ey⟩ := d.finite_schwartz_rayExtensions p Φ
  have hx := ray_leading_properties (K := p.adicCompletion F) (dil := X)
    (fun s u q => by simp [X,mul_pow,mul_assoc]) (fun q => by simp [X]) ex
    (fun q => (d.leading_spec _ Φ).1 q.1 q.2)
  have hy := ray_leading_properties (K := p.adicCompletion F) (dil := Y)
    (fun s u q => by simp [Y,mul_pow,mul_assoc]) (fun q => by simp [Y]) ey
    (fun q => (d.leading_spec _ Φ).2 q.1 q.2)
  exact ⟨⟨hx.1,fun a b => hx.2 (a,b)⟩,⟨hy.1,fun a b => hy.2 (a,b)⟩⟩

theorem finite_support_and_germ_of_isLeadingTerm (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    {g : Charts (LocalField F (.inr p))} (hg : IsLeadingTerm n (modulus F (.inr p)) Φ.val g) :
    (∃ C : Set (LocalField F (.inr p) × LocalField F (.inr p)), IsCompact C ∧
      ∀ z ∉ C, xChart Φ z = 0 ∧ yChart Φ z = 0) ∧
    ∀ᶠ z in 𝓝 (0 : LocalField F (.inr p) × LocalField F (.inr p)),
      xChart Φ z = xChart g z ∧
      yChart Φ z = yChart g z := by
  let v : Place F := .inr p
  let K := p.adicCompletion F
  letI : NontriviallyNormedField (p.adicCompletion F) := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace (p.adicCompletion F) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  let X (s : Kˣ) (q : Kˣ × K) := (s^n*q.1,s.val^n*q.2)
  let Y (s : Kˣ) (q : K × Kˣ) := (s.val^n*q.1,s^n*q.2)
  obtain ⟨ex,ey⟩ := d.finite_schwartz_rayExtensions p Φ
  obtain ⟨Rx,δx,hδx,hx⟩ := cone_bounds (K := p.adicCompletion F) (dil := X)
    (fun s u q => by simp [X,mul_pow,mul_assoc]) id continuous_id (fun _ _ => rfl) (NeZero.ne n)
    ex (fun q => hg.1 q.1 q.2)
  obtain ⟨Ry,δy,hδy,hy⟩ := cone_bounds (K := p.adicCompletion F) (dil := Y)
    (fun s u q => by simp [Y,mul_pow,mul_assoc]) Prod.swap continuous_swap (fun _ _ => rfl) (NeZero.ne n)
    ey (fun q => hg.2 q.1 q.2)
  have hsym (a b : Kˣ) : d.symbol v a b ≠ 0 := (d.unitPairing v a b).ne_zero
  have glue := d.schwartz_glues v Φ
  let R := max Rx Ry
  change (∃ C : Set (K × K), IsCompact C ∧ ∀ z ∉ C, xChart Φ.val z = 0 ∧ yChart Φ.val z = 0) ∧
    ∀ᶠ z in 𝓝 (0 : K × K), xChart Φ.val z = xChart g z ∧ yChart Φ.val z = yChart g z
  constructor
  · refine ⟨closedBall (0:K) R ×ˢ closedBall (0:K) R,(isCompact_closedBall _ _).prod (isCompact_closedBall _ _),?_⟩
    intro z hz
    have hout : R < max ‖z.1‖ ‖z.2‖ := by
      by_contra! h
      exact hz ⟨mem_closedBall_zero_iff.mpr ((le_max_left _ _).trans h),
        mem_closedBall_zero_iff.mpr ((le_max_right _ _).trans h)⟩
    have he := chart_eq_of_dominant hsym glue (g := 0) (fun _ _ => by simp) z (by
      intro a ha hle
      apply (hx a z.2 (ha ▸ hle)).1
      exact ha ▸ (le_max_left _ _).trans_lt (hout.trans_le (max_le le_rfl hle))) (by
      intro b hb hle
      apply (hy b z.1 (hb ▸ hle)).1
      exact hb ▸ (le_max_right _ _).trans_lt (hout.trans_le (max_le hle le_rfl)))
    exact ⟨he.1.trans (by simp [xChart]),he.2.trans (by simp [yChart])⟩
  · have h₁ := (continuous_fst.tendsto (0 : K × K)).eventually (ball_mem_nhds (0:K) hδx)
    have h₂ := (continuous_snd.tendsto (0 : K × K)).eventually (ball_mem_nhds (0:K) hδy)
    filter_upwards [h₁,h₂] with z hz₁ hz₂
    apply chart_eq_of_dominant hsym glue (d.finite_leading_glues p Φ hg) z
    · intro a ha hle
      apply (hx a z.2 (ha ▸ hle)).2
      rw [ha]
      exact mem_ball_zero_iff.mp hz₁
    · intro b hb hle
      apply (hy b z.1 (hb ▸ hle)).2
      rw [hb]
      exact mem_ball_zero_iff.mp hz₂

theorem finite_support_and_germ (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p)) :
    (∃ C : Set (LocalField F (.inr p) × LocalField F (.inr p)), IsCompact C ∧
      ∀ z ∉ C, xChart Φ z = 0 ∧ yChart Φ z = 0) ∧
    ∀ᶠ z in 𝓝 (0 : LocalField F (.inr p) × LocalField F (.inr p)),
      xChart Φ z = xChart (d.leading (.inr p) Φ) z ∧
      yChart Φ z = yChart (d.leading (.inr p) Φ) z :=
  d.finite_support_and_germ_of_isLeadingTerm p Φ (d.leading_spec _ Φ)

/-- The finite-place germ theorem for any chart pair satisfying the defining ray limits. -/
theorem finite_germs_of_isLeadingTerm (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p))
    {g : Charts (LocalField F (.inr p))} (hlead : IsLeadingTerm n (modulus F (.inr p)) Φ.val g) :
    (g = 0 ↔ Φ.val ∈ d.testSet (.inr p)) ∧
    (∃ C : Set (LocalField F (.inr p) × LocalField F (.inr p)), IsCompact C ∧
      ∀ z ∉ C, xChart Φ z = 0 ∧ yChart Φ z = 0) ∧
    ∀ᶠ z in 𝓝 (0 : LocalField F (.inr p) × LocalField F (.inr p)),
      xChart Φ z = xChart g z ∧
      yChart Φ z = yChart g z := by
  let K := LocalField F (.inr p)
  letI : NontriviallyNormedField K := FinitePlace.nontriviallyNormedCompletion p
  letI : NeBot (comap (fun u : Kˣ => u.val) (𝓝 0)) := units_neBot_at_zero
  obtain ⟨⟨C,hC,hout⟩,hg⟩ := d.finite_support_and_germ_of_isLeadingTerm p Φ hlead
  refine ⟨⟨?_,fun hf => hlead.unique (finiteTest_zero_leading n (NeZero.ne n) _ hf.2)⟩,⟨C,hC,hout⟩,hg⟩
  intro hb
  rw [hb] at hg
  obtain ⟨U,hU,ho,h0⟩ := _root_.mem_nhds_iff.mp hg
  obtain ⟨hx,hy⟩ := d.locallyConstant_finite_schwartz p Φ
  refine ⟨d.schwartz_glues _ Φ,hx,hy,C \ U,hC.diff ho,fun h => h.2 h0,?_⟩
  intro z hz
  by_cases hc : z ∈ C
  · have hu : z ∈ U := by_contra fun hn => hz ⟨hc,hn⟩
    simpa [xChart,yChart] using hU hu
  · exact hout z hc

theorem finite_germs (p : HeightOneSpectrum (𝓞 F)) (Φ : d.schwartz (.inr p)) :
    (d.leading (.inr p) Φ = 0 ↔ Φ.val ∈ d.testSet (.inr p)) ∧
    (∃ C : Set (LocalField F (.inr p) × LocalField F (.inr p)), IsCompact C ∧
      ∀ z ∉ C, xChart Φ z = 0 ∧ yChart Φ z = 0) ∧
    ∀ᶠ z in 𝓝 (0 : LocalField F (.inr p) × LocalField F (.inr p)),
      xChart Φ z = xChart (d.leading (.inr p) Φ) z ∧
      yChart Φ z = yChart (d.leading (.inr p) Φ) z :=
  d.finite_germs_of_isLeadingTerm p Φ (d.leading_spec _ Φ)

end Datum
end MetaplecticPoisson
