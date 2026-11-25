import MetaplecticSummation.PowerRootSums
import MetaplecticSummation.RadonConvergence

/-! The integral kernel of the local transform (the root-kernel lemma of §4).
The line integrand is jointly integrable in the line parameter and the coordinate,
by the chart bound (4.2) after splitting the exponent between the two variables.
Integrating first over the line parameter and changing variables z = τⁿ and
z = xy′ − x′y expresses the transform as an absolutely convergent integral of
the X-chart against the sum over the n-th roots of the determinant. -/

noncomputable section
open MeasureTheory Set Filter
open Classical
namespace MetaplecticPoisson

/-- Splitting a two-sided power of a maximum into a product of one-variable weights. -/
theorem min_max_rpow_le {a b γ β : ℝ} (ha : 0 < a) (hb : 0 < b) (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (hγ : γ ≤ 2) :
    min ((max a b)^(-γ)) ((max a b)^(-(4:ℝ))) ≤
      min (a^(-(γ-β))) (a^(-(2:ℝ))) * min (b^(-β)) (b^(-(2:ℝ))) := by
  set M := max a b
  have hM : 0 < M := lt_max_of_lt_left ha
  have haM : a ≤ M := le_max_left _ _
  have hbM : b ≤ M := le_max_right _ _
  have anti (x : ℝ) (hx : 0 < x) (hxM : x ≤ M) (e : ℝ) (he : 0 ≤ e) : M^(-e) ≤ x^(-e) :=
    Real.rpow_le_rpow_of_nonpos hx hxM (neg_nonpos.mpr he)
  have prod (e f : ℝ) : M^(-e) * M^(-f) = M^(-(e+f)) := by
    rw [← Real.rpow_add hM]; ring_nf
  have key (e f : ℝ) (he : 0 ≤ e) (hf : 0 ≤ f) (h1 : γ ≤ e + f) (h2 : e + f ≤ 4) :
      min (M^(-γ)) (M^(-(4:ℝ))) ≤ M^(-e) * M^(-f) := by
    rw [prod]
    rcases le_total M 1 with h|h
    · exact (min_le_left _ _).trans (Real.rpow_le_rpow_of_exponent_ge hM h (by linarith))
    · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_exponent_le h (by linarith))
  have bound (e f : ℝ) (he : 0 ≤ e) (hf : 0 ≤ f) (h1 : γ ≤ e + f) (h2 : e + f ≤ 4) :
      min (M^(-γ)) (M^(-(4:ℝ))) ≤ a^(-e) * b^(-f) :=
    (key e f he hf h1 h2).trans (mul_le_mul (anti a ha haM e he) (anti b hb hbM f hf)
      (by positivity) (by positivity))
  rcases min_choice (a^(-(γ-β))) (a^(-(2:ℝ))) with h₁|h₁ <;>
  rcases min_choice (b^(-β)) (b^(-(2:ℝ))) with h₂|h₂ <;> rw [h₁,h₂]
  · exact bound _ _ (by linarith) hβ (by linarith) (by linarith)
  · exact bound _ _ (by linarith) (by norm_num) (by linarith) (by linarith)
  · exact bound _ _ (by norm_num) hβ (by linarith) (by linarith)
  · exact bound _ _ (by norm_num) (by norm_num) (by linarith) (by linarith)

namespace Datum
open NumberField
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (v : Place F)
local notation "Kv" => LocalField F v
local notation "dx" => selfDual F d.character v
local notation "m" => modulus F v

omit [NeZero n] in
/-- Two-sided powers of the modulus are integrable for the additive measure when the
exponent is below one at the origin and above one at infinity. -/
theorem integrable_modulus_two_sided {p q : ℝ} (_hp0 : 0 ≤ p) (hp : p < 1) (hq : 1 < q) :
    Integrable (fun x : Kv => min ((m x)^(-p)) ((m x)^(-q))) dx := by
  let e := min (1-p) (q-1)
  have he : 0 < e := lt_min (by linarith) (by linarith)
  have hmc : Continuous fun u : Kvˣ => m u.val := by
    show Continuous fun u : Kvˣ => modulus F v u.val
    cases v with
    | inl w => exact (continuous_norm.pow _).comp Units.continuous_val
    | inr p => exact continuous_norm.comp Units.continuous_val
  have hpos (u : Kvˣ) : 0 < m u.val := by cases v <;> simp [modulus,norm_pos_iff.mpr u.ne_zero,pow_pos]
  apply (d.lineMeasure_modulus v (fun x : Kv => min ((m x)^(-p)) ((m x)^(-q)))).1.mp
  have hcont : Continuous (fun u : Kvˣ => m u.val • min ((m u.val)^(-p)) ((m u.val)^(-q))) := by
    refine hmc.smul (Continuous.min ?_ ?_) <;> exact hmc.rpow_const fun u => Or.inl (hpos u).ne'
  refine (d.integrable_modulus_min_rpow v he).mono' hcont.aestronglyMeasurable (.of_forall fun u => ?_)
  have hu := hpos u
  rw [smul_eq_mul,Real.norm_of_nonneg (by positivity),mul_min_of_nonneg _ _ hu.le]
  have e1 : m u.val * (m u.val)^(-p) = (m u.val)^(1-p) := by
    rw [Real.rpow_sub hu,Real.rpow_one,Real.rpow_neg hu.le]; field_simp
  have e2 : m u.val * (m u.val)^(-q) = (m u.val)^(1-q) := by
    rw [Real.rpow_sub hu,Real.rpow_one,Real.rpow_neg hu.le]; field_simp
  rw [e1,e2]
  have h1 : e ≤ 1 - p := min_le_left _ _
  have h2 : e ≤ q - 1 := min_le_right _ _
  rcases le_total (m u.val) 1 with h|h
  · have a1 : (m u.val)^(1-p) ≤ (m u.val)^e := Real.rpow_le_rpow_of_exponent_ge hu h h1
    have a2 : (m u.val)^e ≤ (m u.val)^(-e) := Real.rpow_le_rpow_of_exponent_ge hu h (by linarith)
    exact (min_le_left _ _).trans (le_min a1 (a1.trans a2))
  · have a1 : (m u.val)^(1-q) ≤ (m u.val)^(-e) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
    have a2 : (m u.val)^(-e) ≤ (m u.val)^e := Real.rpow_le_rpow_of_exponent_le h (by linarith)
    exact (min_le_right _ _).trans (le_min (a1.trans a2) a1)

/-- The normalized modulus is quasi-additive. -/
theorem modulus_add_le (a b : Kv) : m (a+b) ≤ 4 * max (m a) (m b) := by
  cases v with
  | inr p =>
    show ‖a+b‖ ≤ 4 * max ‖a‖ ‖b‖
    calc ‖a+b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
      _ ≤ 4 * max ‖a‖ ‖b‖ := by linarith [le_max_left ‖a‖ ‖b‖, le_max_right ‖a‖ ‖b‖, norm_nonneg a]
  | inl w =>
    show ‖a+b‖^w.mult ≤ 4 * max (‖a‖^w.mult) (‖b‖^w.mult)
    have hk : w.mult ≤ 2 := by unfold NumberField.InfinitePlace.mult; split <;> norm_num
    have hM : ‖a+b‖ ≤ 2 * max ‖a‖ ‖b‖ :=
      (norm_add_le _ _).trans (by linarith [le_max_left ‖a‖ ‖b‖, le_max_right ‖a‖ ‖b‖])
    have hmax : max (‖a‖^w.mult) (‖b‖^w.mult) = (max ‖a‖ ‖b‖)^w.mult :=
      (pow_left_monotoneOn (n := w.mult)).map_max (norm_nonneg a) (norm_nonneg b) |>.symm
    rw [hmax]
    calc ‖a+b‖^w.mult ≤ (2 * max ‖a‖ ‖b‖)^w.mult := pow_le_pow_left₀ (norm_nonneg _) hM _
      _ = 2^w.mult * (max ‖a‖ ‖b‖)^w.mult := mul_pow _ _ _
      _ ≤ 4 * (max ‖a‖ ‖b‖)^w.mult := by
          gcongr
          calc (2:ℝ)^w.mult ≤ 2^2 := pow_le_pow_right₀ (by norm_num) hk
            _ = 4 := by norm_num

omit [NumberField F] [NeZero n] in
theorem aesm_of_continuousOn {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopology X] {G : X → ℂ} {s : Set X} (hs : IsOpen s)
    (hG : ContinuousOn G s) (h0 : ∀ z ∉ s, G z = 0) (μ : Measure X) : AEStronglyMeasurable G μ := by
  have he : s.indicator G = G := indicator_eq_self.mpr fun z hz => by
    by_contra h
    exact hz (h0 z h)
  rw [← he]
  exact (aestronglyMeasurable_indicator_iff hs.measurableSet).mpr (hG.aestronglyMeasurable hs.measurableSet)

/-- The X-chart line integrand of a Schwartz section is jointly integrable in the
line parameter τ and the coordinate x, for every fixed output vector. -/
theorem integrable_lineIntegrandX_joint (Φ : d.schwartz v) (x' : Kvˣ) (y' : Kv) :
    Integrable (fun z : Kv × Kv => lineIntegrandX (d.symbol v) Φ.val n z.1 x' y' z.2)
      ((dx).prod dx) := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let : NullSingletonClass dx := d.selfDual_nullSingleton v
  let : SecondCountableTopology Kv := by
    cases v with
    | inl w => exact (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    | inr p => exact inferInstanceAs (SecondCountableTopology (p.adicCompletion F))
  let : NontriviallyNormedField Kv := { localNormedField F v with
    non_trivial := by
      cases v with
      | inl w => exact (archNontriviallyNormedCompletion w).non_trivial
      | inr p => exact (FinitePlace.nontriviallyNormedCompletion p).non_trivial }
  obtain ⟨C,hC,H⟩ := d.schwartz_chart_growth v Φ 4 (by decide)
  let γ := growthExponent n
  have hγ0 : 0 ≤ γ := growthExponent_nonneg n
  have hγ1 : γ < 1 := by
    simp only [γ,growthExponent]
    rw [div_lt_one (by exact_mod_cast NeZero.pos n)]
    exact_mod_cast Nat.sub_lt (NeZero.pos n) one_pos
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast NeZero.one_le
  let β := γ/(2*n)
  have hβ0 : 0 ≤ β := by positivity
  have hnβ : (n:ℝ)*β = γ/2 := by simp only [β]; field_simp
  have hβγ : β ≤ γ := by
    simp only [β]; rw [div_le_iff₀ (by positivity)]; nlinarith
  let A (x : Kv) := min ((m x)^(-(γ-β))) ((m x)^(-(2:ℝ)))
  let B (τ : Kv) := min ((m τ)^(-((n:ℝ)*β))) ((m τ)^(-(2*(n:ℝ))))
  have hA : Integrable A dx := d.integrable_modulus_two_sided v (by linarith) (by linarith) (by norm_num)
  have hB : Integrable B dx := d.integrable_modulus_two_sided v (by positivity) (by rw [hnβ]; linarith)
    (by linarith)
  let C₂ := max 1 (4*(m y' + m x'.val))
  have hC₂ : 1 ≤ C₂ := le_max_left _ _
  have hm0 (z : Kv) : 0 ≤ m z := by cases v <;> simp [modulus,pow_nonneg]
  have hmpos (z : Kv) (hz : z ≠ 0) : 0 < m z := by cases v <;> simp [modulus,norm_pos_iff.mpr hz,pow_pos]
  have mmul (a b : Kv) : m (a*b) = m a * m b := by cases v <;> simp [modulus,norm_mul,mul_pow]
  have mpow (a : Kv) : m (a^n) = m a ^ n := by cases v <;> simp [modulus,norm_pow,← pow_mul,mul_comm]
  have mneg (a : Kv) : m (-a) = m a := by cases v <;> simp [modulus]
  -- pointwise bound away from the axes
  have bound (τ x : Kv) (hτ : τ ≠ 0) (hx : x ≠ 0) :
      ‖lineIntegrandX (d.symbol v) Φ.val n τ x' y' x‖ ≤ (C*C₂^(4:ℝ)) * (B τ * A x) := by
    let y := (x*y' - τ^n)/x'.val
    have hz : (x,y) ≠ (0 : Kv × Kv) := fun h => hx (congrArg Prod.fst h)
    have hb := (H (x,y) hz).1
    simp only [xChart,ne_eq,hx,not_false_eq_true,dite_true] at hb
    have hL : ‖lineIntegrandX (d.symbol v) Φ.val n τ x' y' x‖ = ‖Φ.val.1 (Units.mk0 x hx) y‖ := by
      simp [lineIntegrandX,hx,y,norm_symbol]
    rw [hL]
    set r := max (m x) (m y)
    have hxpos := hmpos x hx
    have hr : 0 < r := lt_max_of_lt_left hxpos
    have hτn : τ^n = x*y' + -(x'.val*y) := by simp only [y]; field_simp; ring
    have hτm : m τ ^ n ≤ C₂ * r := by
      rw [← mpow,hτn]
      refine (modulus_add_le v _ _).trans ?_
      rw [mneg,mmul,mmul]
      have h1 : m x * m y' ≤ (m y' + m x'.val) * r :=
        (mul_le_mul (le_max_left _ _) (by linarith [hm0 x'.val]) (hm0 _) hr.le).trans_eq (mul_comm _ _)
      have h2 : m x'.val * m y ≤ (m y' + m x'.val) * r :=
        mul_le_mul (by linarith [hm0 y']) (le_max_right _ _) (hm0 _) (by linarith [hm0 y',hm0 x'.val])
      calc 4 * max (m x * m y') (m x'.val * m y) ≤ 4 * ((m y' + m x'.val) * r) :=
            by gcongr; exact max_le h1 h2
        _ = (4*(m y' + m x'.val)) * r := by ring
        _ ≤ C₂ * r := by gcongr; exact le_max_right _ _
    set M := max (m x) (m τ ^ n)
    have hMr : M ≤ C₂ * r := max_le (le_max_left _ _ |>.trans (le_mul_of_one_le_left hr.le hC₂)) hτm
    have hMpos : 0 < M := lt_max_of_lt_left hxpos
    have hτpos : 0 < m τ ^ n := pow_pos (hmpos τ hτ) n
    -- compare the two-sided powers at r and at M
    have hcmp : min (r^(-γ)) (r^(-((4:ℕ):ℝ))) ≤ C₂^(4:ℝ) * min (M^(-γ)) (M^(-(4:ℝ))) := by
      have hMC : M / C₂ ≤ r := by rw [div_le_iff₀ (by linarith)]; linarith
      have hMCpos : 0 < M / C₂ := div_pos hMpos (by linarith)
      have e (t : ℝ) (ht : 0 ≤ t) (ht4 : t ≤ 4) : r^(-t) ≤ C₂^(4:ℝ) * M^(-t) := by
        calc r^(-t) ≤ (M/C₂)^(-t) := Real.rpow_le_rpow_of_nonpos hMCpos hMC (by linarith)
          _ = C₂^t * M^(-t) := by
              rw [Real.div_rpow hMpos.le (by linarith),Real.rpow_neg (by linarith : (0:ℝ) ≤ C₂),
                div_inv_eq_mul,mul_comm]
          _ ≤ C₂^(4:ℝ) * M^(-t) := by
              gcongr
      rw [mul_min_of_nonneg _ _ (by positivity)]
      push_cast
      exact min_le_min (e γ hγ0 (by linarith)) (e 4 (by norm_num) le_rfl)
    have hsplit := min_max_rpow_le hxpos hτpos hβ0 hβγ (by linarith)
    have hBeq : min ((m τ ^ n)^(-β)) ((m τ ^ n)^(-(2:ℝ))) = B τ := by
      have hτ0 := (hmpos τ hτ).le
      simp only [B]
      rw [← Real.rpow_natCast,← Real.rpow_mul hτ0,← Real.rpow_mul hτ0]
      congr 2 <;> ring
    rw [hBeq] at hsplit
    calc ‖Φ.val.1 (Units.mk0 x hx) y‖ ≤ C * min (r^(-γ)) (r^(-((4:ℕ):ℝ))) := hb
      _ ≤ C * (C₂^(4:ℝ) * min (M^(-γ)) (M^(-(4:ℝ)))) := by gcongr
      _ ≤ C * (C₂^(4:ℝ) * (A x * B τ)) := by gcongr
      _ = (C*C₂^(4:ℝ)) * (B τ * A x) := by ring
  -- measurability
  have hcont := (d.continuous_schwartz_charts v Φ).1
  have hm : AEStronglyMeasurable (fun z : Kv × Kv => lineIntegrandX (d.symbol v) Φ.val n z.1 x' y' z.2)
      ((dx).prod dx) := by
    have hopen : IsOpen {z : Kv × Kv | z.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
    apply aesm_of_continuousOn hopen
    · intro z hz
      have hz' : z.2 ≠ 0 := hz
      have hc : ContinuousAt (fun z : Kv × Kv => Φ.val.1 (liftUnit z.2) ((z.2*y' - z.1^n)/x'.val) *
          d.symbol v (liftUnit z.2) (-x')) z := by
        apply ContinuousAt.mul
        · exact hcont.continuousAt.comp (((liftUnit_continuousAt hz').comp continuousAt_snd).prodMk
            (by fun_prop))
        · exact ((d.continuous_symbol v).comp (continuous_id.prodMk continuous_const)).continuousAt.comp
            ((liftUnit_continuousAt hz').comp continuousAt_snd)
      refine (hc.congr ?_).continuousWithinAt
      filter_upwards [(isOpen_ne_fun continuous_snd continuous_const).mem_nhds hz'] with w hw
      have hw' : w.2 ≠ 0 := hw
      simp only [lineIntegrandX,ne_eq,hw',not_false_eq_true,dite_true]
      rw [show liftUnit w.2 = Units.mk0 w.2 hw' from Units.ext (liftUnit_val hw')]
    · intro z hz
      have hz0 : z.2 = 0 := by simpa using hz
      simp [lineIntegrandX,hz0]
  refine ((hB.mul_prod hA).const_mul (C*C₂^(4:ℝ))).mono' hm ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae ((dx).ae_ne 0)] with z hτ
  by_cases hx : z.2 = 0
  · simp only [lineIntegrandX,hx,ne_eq,not_true_eq_false,dite_false,norm_zero]
    exact mul_nonneg (by positivity) (mul_nonneg
      (le_min (Real.rpow_nonneg (hm0 _) _) (Real.rpow_nonneg (hm0 _) _))
      (le_min (Real.rpow_nonneg (hm0 _) _) (Real.rpow_nonneg (hm0 _) _)))
  · exact bound z.1 z.2 hτ hx

omit [NeZero n] in
/-- An affine change of the additive variable. -/
theorem integral_affine_local {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Kv → E) (k : Kvˣ) (b : Kv) :
    (∫ z, f (k.val*z+b) ∂dx) = (m k.val)⁻¹ • ∫ z, f z ∂dx := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let e := MeasurableEquiv.smul (α := Kv) k
  have h := e.measurableEmbedding.integral_map (μ := dx) (fun t => f (t+b))
  change (∫ t, f (t+b) ∂Measure.map (fun t => k.val*t) dx) = ∫ z, f (k.val*z+b) ∂dx at h
  have hmk : 0 ≤ m k.val := by cases v <;> simp [modulus,pow_nonneg]
  rw [← h,d.map_local_mul,integral_smul_nnreal_measure,integral_add_right_eq_self,NNReal.smul_def,
    NNReal.coe_inv,Real.coe_toNNReal _ hmk]

omit [NeZero n] in
theorem integrable_affine_local {f : Kv → ℂ} (hf : Integrable f dx) (k : Kvˣ) (b : Kv) :
    Integrable (fun z => f (k.val*z+b)) dx := by
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let e := MeasurableEquiv.smul (α := Kv) k
  have hi := (measurePreserving_add_right dx b).integrable_comp_of_integrable hf
  apply (e.measurableEmbedding.integrable_map_iff (g := fun t => f (t+b))).mp
  change Integrable _ (Measure.map (fun t => k.val*t) dx)
  rw [d.map_local_mul]
  exact hi.smul_measure_nnreal

/-- A sum over the n-th roots is continuous away from zero. -/
theorem rootSum_continuousOn_ne {g : Kv → ℂ} (hg : ContinuousOn g {0}ᶜ) :
    ContinuousOn (fun z : Kv => ∑ τ ∈ Polynomial.nthRootsFinset n z, g τ) {0}ᶜ := by
  let : NontriviallyNormedField Kv := { localNormedField F v with
    non_trivial := by
      cases v with
      | inl w => exact (archNontriviallyNormedCompletion w).non_trivial
      | inr p => exact (FinitePlace.nontriviallyNormedCompletion p).non_trivial }
  have hprop := place_proper (F := F) v
  have hP := place_powers_open (F := F) (n := n) v
  obtain ⟨hGc,hG0⟩ := rootSum_continuousOn hP hg
  let P := (powMonoidHom n : Kvˣ →* Kvˣ).range
  have hPc : IsClosed (P : Set Kvˣ) := Subgroup.isClosed_of_isOpen _ hP
  intro z hz
  have hz' : z ≠ 0 := hz
  let G (u : Kvˣ) := ∑ τ ∈ Polynomial.nthRootsFinset n u.val, g τ
  have hl : ContinuousAt liftUnit z := liftUnit_continuousAt hz'
  have hlz : liftUnit z = Units.mk0 z hz' := Units.ext (liftUnit_val hz')
  have heq : (fun z : Kv => ∑ τ ∈ Polynomial.nthRootsFinset n z, g τ) =ᶠ[nhds z] (G ∘ liftUnit) := by
    filter_upwards [isOpen_ne.mem_nhds hz'] with y hy
    simp [G,Function.comp,liftUnit_val (show y ≠ 0 from hy)]
  refine (ContinuousAt.congr ?_ heq.symm).continuousWithinAt
  apply ContinuousAt.comp _ hl
  rw [hlz]
  by_cases hu : Units.mk0 z hz' ∈ (P : Set Kvˣ)
  · exact (hGc _ hu).continuousAt (hP.mem_nhds hu)
  · apply continuousAt_const (y := (0:ℂ)) |>.congr
    filter_upwards [hPc.isOpen_compl.mem_nhds hu] with u hu'
    exact (hG0 u hu').symm

/-- The defining integral of the transform as an integral against the root kernel. -/
theorem integralTransform_root_kernel (Φ : d.schwartz v) (x' : Kvˣ) (y' : Kv) :
    let ψ := d.character.localValue F v
    let S := fun z : Kv => ∑ τ ∈ Polynomial.nthRootsFinset n z, ψ τ * (m τ : ℂ)^(1-(n:ℤ))
    let G := fun z : Kv × Kv => if hx : z.1 ≠ 0 then
      Φ.val.1 (Units.mk0 z.1 hx) z.2 * d.symbol v (Units.mk0 z.1 hx) (-x') * S (z.1*y' - z.2*x'.val) else 0
    Integrable G ((dx).prod dx) ∧
      (d.integralTransform v Φ.val).1 x' y' = (Real.sqrt (m (n:Kv)) : ℂ)⁻¹ * (m (n:Kv) : ℂ)⁻¹ *
        ∫ z, G z ∂((dx).prod dx) := by
  intro ψ S G
  let : (dx).IsAddHaarMeasure := (existsUnique_selfDual F d.character v).exists.choose_spec.1
  let L (τ x : Kv) := lineIntegrandX (d.symbol v) Φ.val n τ x' y' x
  have hJ := d.integrable_lineIntegrandX_joint v Φ x' y'
  have hψc : Continuous ψ := d.character.continuous_localValue v
  have hJψ : Integrable (fun z : Kv × Kv => ψ z.1 * L z.1 z.2) ((dx).prod dx) :=
    hJ.bdd_mul (hψc.comp continuous_fst).aestronglyMeasurable
      (.of_forall fun z => by rw [d.character.norm_localValue])
  let : NullSingletonClass dx := d.selfDual_nullSingleton v
  have mneg (a : Kv) : m (-a) = m a := by cases v <;> simp [modulus]
  have hmpos (z : Kv) (hz : z ≠ 0) : 0 < m z := by cases v <;> simp [modulus,norm_pos_iff.mpr hz,pow_pos]
  have hx'0 : (m x'.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hmpos _ x'.ne_zero).ne'
  have hnK : (n : Kv) ≠ 0 := by
    have hnz := (diagonal F v).injective.ne (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n:F) ≠ 0)
    simpa only [map_natCast,map_zero] using hnz
  have hn0 : (m (n:Kv) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hmpos _ hnK).ne'
  have hΦc := (d.continuous_schwartz_charts v Φ).1
  -- the slice computation at a fixed nonzero first coordinate
  let kx (X : Kvˣ) (z : Kv) := Φ.val.1 X ((X.val*y' - z)/x'.val)
  have hkc (X : Kvˣ) : Continuous (kx X) :=
    hΦc.comp (continuous_const.prodMk ((continuous_const.sub continuous_id).div_const _))
  have hL (X : Kvˣ) (τ : Kv) : L τ X.val = kx X (τ^n) * d.symbol v X (-x') := by
    simp [L,lineIntegrandX,kx,X.ne_zero]
  have haff (X : Kvˣ) (y : Kv) : kx X ((-x').val*y + X.val*y') = Φ.val.1 X y := by
    simp only [kx]
    rw [show (X.val*y' - ((-x').val*y + X.val*y'))/x'.val = y by
      simp only [Units.val_neg]; field_simp; ring]
  have hdet (X : Kvˣ) (y : Kv) : (-x').val*y + X.val*y' = X.val*y' - y*x'.val := by
    simp only [Units.val_neg]; ring
  have slice (X : Kvˣ) (hX : Integrable (fun τ => ψ τ * L τ X.val) dx) :
      Integrable (fun y => G (X.val,y)) dx ∧
      (∫ τ, ψ τ * L τ X.val ∂dx) = (m x'.val : ℂ) / (m (n:Kv) : ℂ) * ∫ y, G (X.val,y) ∂dx := by
    have hsym : ‖d.symbol v X (-x')‖ = 1 := d.norm_symbol v _ _
    have hsym0 : d.symbol v X (-x') ≠ 0 := norm_ne_zero_iff.mp (by rw [hsym]; norm_num)
    have hi : Integrable (fun τ => kx X (τ^n) * ψ τ) dx := by
      refine (hX.const_mul (d.symbol v X (-x'))⁻¹).congr (.of_forall fun τ => ?_)
      simp only [hL]; field_simp
    obtain ⟨hint,heq⟩ := d.integral_pow_change v (g := ψ) (h := kx X) hψc.continuousOn
      (hkc X).continuousOn hi
    have hGy (y : Kv) : G (X.val,y) = d.symbol v X (-x') *
        (kx X ((-x').val*y + X.val*y') * S ((-x').val*y + X.val*y')) := by
      dsimp only [G]
      simp only [ne_eq,X.ne_zero,not_false_eq_true,dite_true,Units.mk0_val]
      rw [haff,hdet]; ring
    constructor
    · refine ((d.integrable_affine_local v hint (-x') (X.val*y')).const_mul (d.symbol v X (-x'))).congr
        (.of_forall fun y => (hGy y).symm)
    · have haffint : (∫ y, kx X ((-x').val*y + X.val*y') * S ((-x').val*y + X.val*y') ∂dx) =
          (m x'.val)⁻¹ • ∫ z, kx X z * S z ∂dx := by
        have h := d.integral_affine_local v (fun z => kx X z * S z) (-x') (X.val*y')
        rwa [Units.val_neg,mneg] at h
      simp_rw [hGy]
      rw [integral_const_mul,haffint]
      have e1 : (∫ τ, ψ τ * L τ X.val ∂dx) = d.symbol v X (-x') * ∫ τ, kx X (τ^n) * ψ τ ∂dx := by
        rw [← integral_const_mul]; congr 1; funext τ; rw [hL]; ring
      rw [e1,show (∫ τ, kx X (τ^n) * ψ τ ∂dx) = (m (n:Kv) : ℂ)⁻¹ * ∫ z, kx X z * S z ∂dx by
        rw [heq]; field_simp,Complex.real_smul]
      push_cast
      field_simp
  -- norm bound on each slice
  let T (z : Kv) : ℝ := ∑ τ ∈ Polynomial.nthRootsFinset n z, (m τ)^(1-(n:ℤ))
  have hm0 (z : Kv) : 0 ≤ m z := by cases v <;> simp [modulus,pow_nonneg]
  have hT0 (z : Kv) : 0 ≤ T z := Finset.sum_nonneg fun τ _ => zpow_nonneg (hm0 τ) _
  have hST (z : Kv) : ‖S z‖ ≤ T z := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun τ _ => ?_))
    rw [norm_mul,d.character.norm_localValue,one_mul,norm_zpow,Complex.norm_real,Real.norm_of_nonneg (hm0 τ)]
  have nslice (X : Kvˣ) (hX : Integrable (fun τ => ψ τ * L τ X.val) dx) :
      (∫ y, ‖G (X.val,y)‖ ∂dx) ≤ m (n:Kv) / m x'.val * ∫ τ, ‖L τ X.val‖ ∂dx := by
    have hsym : ‖d.symbol v X (-x')‖ = 1 := d.norm_symbol v _ _
    have hi : Integrable (fun τ => ((‖kx X (τ^n)‖ : ℝ) : ℂ) * 1) dx := by
      refine (hX.norm.ofReal).congr (.of_forall fun τ => ?_)
      simp only [ψ,hL,norm_mul,hsym,d.character.norm_localValue,one_mul,mul_one]
      rfl
    obtain ⟨hint,heq⟩ := d.integral_pow_change v (g := fun _ => 1) (h := fun z => ((‖kx X z‖ : ℝ) : ℂ))
      continuousOn_const (Complex.continuous_ofReal.comp (hkc X).norm).continuousOn hi
    let Fr (z : Kv) : ℝ := ‖kx X z‖ * T z
    have hF (z : Kv) : ((‖kx X z‖ : ℝ) : ℂ) * ∑ τ ∈ Polynomial.nthRootsFinset n z, 1 * (m τ : ℂ)^(1-(n:ℤ)) =
        (Fr z : ℂ) := by simp only [Fr,T,one_mul]; push_cast; rfl
    simp_rw [hF] at hint heq
    have hFr : Integrable Fr dx := by simpa using hint.re
    have hval : (∫ z, Fr z ∂dx) = m (n:Kv) * ∫ τ, ‖L τ X.val‖ ∂dx := by
      have h1 : ((∫ z, Fr z ∂dx : ℝ) : ℂ) = ((m (n:Kv) * ∫ τ, ‖kx X (τ^n)‖ ∂dx : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal,heq]; push_cast; rw [← integral_complex_ofReal]; simp
      have h2 := Complex.ofReal_injective h1
      rw [h2]
      congr 1; congr 1; funext τ
      rw [hL,norm_mul,hsym,mul_one]
    have hbound (y : Kv) : ‖G (X.val,y)‖ ≤ Fr ((-x').val*y + X.val*y') := by
      dsimp only [G]
      simp only [ne_eq,X.ne_zero,not_false_eq_true,dite_true,Units.mk0_val]
      rw [norm_mul,norm_mul,hsym,mul_one]
      simp only [Fr]
      rw [haff,← hdet]
      exact mul_le_mul_of_nonneg_left (hST _) (norm_nonneg _)
    have haffi := d.integrable_affine_local v hint (-x') (X.val*y')
    have haffr : Integrable (fun y => Fr ((-x').val*y + X.val*y')) dx := by
      have := haffi.re; simpa using this
    calc (∫ y, ‖G (X.val,y)‖ ∂dx) ≤ ∫ y, Fr ((-x').val*y + X.val*y') ∂dx := by
          refine integral_mono_of_nonneg (.of_forall fun _ => norm_nonneg _) haffr (.of_forall hbound)
      _ = (m x'.val)⁻¹ * ∫ z, Fr z ∂dx := by
          rw [d.integral_affine_local v Fr (-x') (X.val*y'),Units.val_neg,mneg,smul_eq_mul]
      _ = m (n:Kv) / m x'.val * ∫ τ, ‖L τ X.val‖ ∂dx := by rw [hval]; ring
  -- measurability of the kernel integrand
  let D (z : Kv × Kv) := z.1*y' - z.2*x'.val
  have hDc : Continuous D := by fun_prop
  have hnull : ∀ᵐ z ∂((dx).prod dx), D z ≠ 0 := by
    have hs : MeasurableSet {z : Kv × Kv | D z ≠ 0} :=
      (isOpen_ne_fun hDc continuous_const).measurableSet
    refine (Measure.ae_prod_mem_iff_ae_ae_mem hs).mpr (.of_forall fun x => ?_)
    filter_upwards [(dx).ae_ne (x*y'/x'.val)] with y hy
    intro h
    apply hy
    change x*y' - y*x'.val = 0 at h
    field_simp
    linear_combination -h
  have hSc : ContinuousOn S {0}ᶜ := by
    apply rootSum_continuousOn_ne v
    intro τ hτ
    have hτ' : τ ≠ 0 := hτ
    have hmc : ContinuousAt (fun τ : Kv => (m τ : ℂ)) τ := by
      apply Complex.continuous_ofReal.continuousAt.comp
      show ContinuousAt (modulus F v) τ
      cases v with
      | inl w => exact (continuous_norm.pow _).continuousAt
      | inr p => exact continuous_norm.continuousAt
    exact (hψc.continuousAt.mul (hmc.zpow₀ _ (Or.inl (Complex.ofReal_ne_zero.mpr (hmpos τ hτ').ne')))).continuousWithinAt
  let : NontriviallyNormedField Kv := { localNormedField F v with
    non_trivial := by
      cases v with
      | inl w => exact (archNontriviallyNormedCompletion w).non_trivial
      | inr p => exact (FinitePlace.nontriviallyNormedCompletion p).non_trivial }
  let : SecondCountableTopology Kv := by
    cases v with
    | inl w => exact (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    | inr p => exact inferInstanceAs (SecondCountableTopology (p.adicCompletion F))
  let U : Set (Kv × Kv) := {z | z.1 ≠ 0} ∩ {z | D z ≠ 0}
  have hU : IsOpen U := (isOpen_ne_fun continuous_fst continuous_const).inter (isOpen_ne_fun hDc continuous_const)
  let G' (z : Kv × Kv) := if z ∈ U then G z else 0
  have hG'c : ContinuousOn G' U := by
    intro z hz
    have hz1 : z.1 ≠ 0 := hz.1
    have hc : ContinuousAt (fun z : Kv × Kv => Φ.val.1 (liftUnit z.1) z.2 * d.symbol v (liftUnit z.1) (-x') * S (D z)) z := by
      refine (ContinuousAt.mul ?_ ?_).mul ((hSc.continuousAt (isOpen_ne.mem_nhds hz.2)).comp hDc.continuousAt)
      · exact hΦc.continuousAt.comp (((liftUnit_continuousAt hz1).comp continuousAt_fst).prodMk continuousAt_snd)
      · exact ((d.continuous_symbol v).comp (continuous_id.prodMk continuous_const)).continuousAt.comp
          ((liftUnit_continuousAt hz1).comp continuousAt_fst)
    refine (hc.congr ?_).continuousWithinAt
    filter_upwards [hU.mem_nhds hz] with w hw
    have hw1 : w.1 ≠ 0 := hw.1
    simp only [G',hw,ite_true,G,ne_eq,hw1,not_false_eq_true,dite_true,D]
    rw [show liftUnit w.1 = Units.mk0 w.1 hw1 from Units.ext (liftUnit_val hw1)]
  have hG'm : AEStronglyMeasurable G' ((dx).prod dx) :=
    aesm_of_continuousOn hU hG'c (fun z hz => by simp [G',hz]) _
  have hGG' : G =ᵐ[(dx).prod dx] G' := by
    filter_upwards [hnull] with z hz
    by_cases h1 : z.1 = 0
    · simp [G,G',h1]
    · simp [G',U,h1,hz]
  have hGm : AEStronglyMeasurable G ((dx).prod dx) := hG'm.congr hGG'.symm
  have hsl : ∀ᵐ x ∂dx, Integrable (fun τ => ψ τ * L τ x) dx := hJψ.prod_left_ae
  have hG : Integrable G ((dx).prod dx) := by
    refine (integrable_prod_iff hGm).mpr ⟨?_,?_⟩
    · filter_upwards [hsl,(dx).ae_ne 0] with x hx hx0
      exact (slice (Units.mk0 x hx0) hx).1
    · refine (hJ.integral_norm_prod_right.const_mul (m (n:Kv) / m x'.val)).mono'
        hGm.norm.integral_prod_right' ?_
      filter_upwards [hsl,(dx).ae_ne 0] with x hx hx0
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact nslice (Units.mk0 x hx0) hx
  refine ⟨hG,?_⟩
  have hA : (d.integralTransform v Φ.val).1 x' y' =
      (Real.sqrt (m (n:Kv)) : ℂ)⁻¹ * ∫ τ, ψ τ * ((∫ x, L τ x ∂dx) / (m x'.val : ℂ)) ∂dx := rfl
  rw [hA]
  have hC : (∫ τ, ψ τ * ((∫ x, L τ x ∂dx) / (m x'.val : ℂ)) ∂dx) =
      (m x'.val : ℂ)⁻¹ * ∫ τ, ∫ x, ψ τ * L τ x ∂dx ∂dx := by
    rw [← integral_const_mul]
    congr 1; funext τ
    rw [integral_const_mul,div_eq_mul_inv]
    ring
  rw [hC,integral_integral_swap (f := fun τ x => ψ τ * L τ x) hJψ]
  have hB : (∫ x, ∫ τ, ψ τ * L τ x ∂dx ∂dx) =
      ∫ x, (m x'.val : ℂ) / (m (n:Kv) : ℂ) * ∫ y, G (x,y) ∂dx ∂dx := by
    apply integral_congr_ae
    filter_upwards [hsl,(dx).ae_ne 0] with x hx hx0
    exact (slice (Units.mk0 x hx0) hx).2
  rw [hB,integral_const_mul,← integral_prod G hG]
  field_simp

end Datum
end MetaplecticPoisson
