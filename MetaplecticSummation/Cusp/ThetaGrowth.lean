import MetaplecticSummation.Cusp.LocalBounds
import MetaplecticSummation.Cusp.Rows
import MetaplecticSummation.Cusp.Majorant

/-! Growth of the translated theta series and rapid decay of its off-axis terms. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain Filter Set
open scoped Matrix MatrixGroups
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)
local notation "P" => Prime F
local notation "G" => AdelicSL F
local notation "A" => Adeles F

/-- A restricted family projects to the specified adelic matrix at every place. -/
def LiftsAdelicMatrix (m : G) (g : ∀ v, d.cover v) : Prop :=
  ∀ v, d.coverProjection v (g v) = localMatrix F v m

private theorem translated_norm_factors (Φ : ∀ v, d.schwartz v) (hf : ∀ᶠ v in cofinite, Φ v = d.basic v)
    {m : G} {g : ∀ v, d.cover v} (hg : d.IsRestrictedCover g) (hm : d.LiftsAdelicMatrix m g) (p : RationalPoint F) :
    let f := fun v => d.sectionNorm v (Φ v) (diagonalRow F v p ᵥ* (localMatrix F v m).val)
    (∀ᶠ v in cofinite, f v = 1) ∧ ‖d.evaluation (d.coverAction g hg (d.pure Φ hf)) p‖ = ∏ᶠ v, f v := by
  let b := fun v => d.localValue p v ((g v).val (Φ v))
  have hb : ∀ᶠ v in cofinite, b v = 1 := by
    filter_upwards [hf,d.restrictedCover_fixes_basic hg,d.eventually_basic_value p] with v hv hg' he
    simpa only [b,hv,hg'] using he
  have e (v : Place F) : ‖b v‖ = d.sectionNorm v (Φ v) (diagonalRow F v p ᵥ* (localMatrix F v m).val) := by
    rw [← hm v,← d.sectionNorm_cover]
    exact (d.sectionNorm_diagonal v p _).symm
  refine ⟨hb.mono fun v hv => (e v).symm.trans (by rw [hv,norm_one]),?_⟩
  rw [d.coverAction_pure,d.evaluation_pure]
  change normHom.toMonoidHom (∏ᶠ v, b v) = _
  rw [MonoidHom.map_finprod _ (eventually_cofinite.mp hb)]
  exact finprod_congr e

private theorem row_modulus_pos (v : Place F) {x : Fin 2 → LocalField F v} (hx : x ≠ 0) :
    0 < localRowModulus F v x := by
  have pos (a : LocalField F v) (ha : a ≠ 0) : 0 < modulus F v a := by
    cases v with
    | inl w => exact pow_pos (norm_pos_iff.mpr ha) _
    | inr p => exact norm_pos_iff.mpr ha
  by_cases h : x 0 = 0
  · have hy : x 1 ≠ 0 := fun hh => hx (funext fun i => by fin_cases i <;> simp [h,hh])
    exact (pos _ hy).trans_le (le_max_right ..)
  · exact (pos _ h).trans_le (le_max_left ..)

private theorem row_ne_zero (p : RationalPoint F) (v : Place F) (m : G) :
    diagonalRow F v p ᵥ* (localMatrix F v m).val ≠ 0 := by
  let a := localMatrix F v m
  intro he
  have eqn := congrArg (fun z : Fin 2 → LocalField F v => z ᵥ* a⁻¹.val) he
  have h : a.val*a⁻¹.val = 1 := congrArg Subtype.val (mul_inv_cancel a)
  change (diagonalRow F v p ᵥ* a.val) ᵥ* a⁻¹.val = (0 : Fin 2 → _) ᵥ* a⁻¹.val at eqn
  rw [Matrix.vecMul_vecMul,h,Matrix.vecMul_one,Matrix.zero_vecMul] at eqn
  apply p.property
  exact Prod.ext ((map_eq_zero (diagonal F v)).mp (congrFun eqn 0)) ((map_eq_zero (diagonal F v)).mp (congrFun eqn 1))

/-- Multiplying each off-axis summand by the L-th power of the cusp height still
gives a sum bounded by the cube of the height. -/
theorem weighted_cusp_theta (Φ : ∀ v, d.schwartz v) (hf : ∀ᶠ v in cofinite, Φ v = d.basic v)
    (w : P) (K : Set G) (hK : IsCompact K) (L : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (u : A) (k : ℕ), ∀ ω ∈ K, ∀ g : ∀ v, d.cover v, ∀ hg : d.IsRestrictedCover g,
      d.LiftsAdelicMatrix (adelicUpper F u * ideleDiagonal F (cuspIdele F w)^k * ω) g →
      let term := fun p : RationalPoint F => (if p.val.1 = 0 then 1 else (w.asIdeal.absNorm : ℝ)^k)^L *
        ‖d.evaluation (d.coverAction g hg (d.pure Φ hf)) p‖
      Summable term ∧ (∑' p, term p) ≤ M*(w.asIdeal.absNorm : ℝ)^(3*k) := by
  let S := cuspScale F w
  let q : ℝ := w.asIdeal.absNorm
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm w).le
  obtain ⟨B,hB,b₁,geo⟩ := cusp_row_bounds_on_compact F w hK
  obtain ⟨C,hC,c₁,localBound⟩ := d.weighted_section_bounds Φ hf L
  obtain ⟨M,hM,maj⟩ := cusp_majorant_sum (growthExponent_nonneg n) (growthExponent_le_one n)
    C B S hC hB (cuspScale_one_le F w) c₁ b₁ (cuspScale_cofinite F w) hq (cuspScale_product F w)
  let V := (∏ᶠ v, B v)^L
  have hV : 0 ≤ V := pow_nonneg (finprod_nonneg fun v => zero_le_one.trans (hB v)) _
  refine ⟨V*M,mul_nonneg hV hM,?_⟩
  intro u k ω hω g hg hm
  let m := adelicUpper F u * ideleDiagonal F (cuspIdele F w)^k * ω
  obtain ⟨σ,_,rows⟩ := geo u k ω hω
  let a := fun v => (B v*S v^k)⁻¹
  have s₁ := cuspScale_cofinite F w
  have a₁ : ∀ᶠ v in cofinite, a v = 1 := by filter_upwards [b₁,s₁] with v hb hs; simp [a,S,hb,hs]
  let β := thetaMajorant (growthExponent n) C a
  let f := fun p => ‖d.evaluation (d.coverAction g hg (d.pure Φ hf)) p‖
  let W := fun (p : RationalPoint F) => if p.val.1 = 0 then (1:ℝ) else q^k
  have nonneg (p) : 0 ≤ W p^L*f p := mul_nonneg (pow_nonneg (by dsimp [W]; split <;> positivity) _) (norm_nonneg _)
  have domination (p) : W p ^ L * f p ≤ V*β (σ p) := by
    let y := fun v => diagonalRow F v p ᵥ* (localMatrix F v m).val
    let r := fun v => localRowModulus F v (y v)
    let b := fun v => d.sectionNorm v (Φ v) (y v)
    let t := fun v => if p.val.1 = 0 then 1 else S v^k * modulus F v (diagonal F v p.val.1)
    obtain ⟨bco,he⟩ := d.translated_norm_factors Φ hf hg hm p
    have ht₀ (v) : 0 ≤ t v := by
      dsimp only [t]
      split
      · exact zero_le_one
      · apply mul_nonneg (pow_nonneg (zero_le_one.trans (cuspScale_one_le F w v)) _)
        cases v <;> simp [modulus]
    have tco : ∀ᶠ v in cofinite, t v = 1 := by
      by_cases hx : p.val.1 = 0
      · exact .of_forall fun v => by simp [t,hx]
      · filter_upwards [s₁,modulus_eventually_one hx] with v hs hv
        simp [t,hx,S,hs,hv]
    have ht : ∏ᶠ v, t v = W p := by
      by_cases hx : p.val.1 = 0
      · simp [t,W,hx]
      · simp only [t,W,ite_eq_right hx]
        rw [finprod_mul_distrib (f := fun v => S v^k) ((show Function.HasFiniteMulSupport S from eventually_cofinite.mp s₁).pow k)
          (eventually_cofinite.mp (modulus_eventually_one hx)),← finprod_pow (eventually_cofinite.mp s₁),cuspScale_product,diagonal_modulus_product hx,mul_one]
    let H := fun v => localThetaBound (growthExponent n) v (C v) (a v * vectorModulus v (σ p))
    have hc := localThetaBound_cofinite (growthExponent n) c₁ a₁ (σ p)
    have e (v) : t v ^ L * b v ≤ B v ^ L * H v := by
      obtain ⟨hy,hexp⟩ := rows p v
      have hn := row_ne_zero p v m
      have hr := row_modulus_pos v hn
      have pos : 0 < a v * vectorModulus v (σ p) := mul_pos (inv_pos.mpr (mul_pos (zero_lt_one.trans_le (hB v))
        (pow_pos (zero_lt_one.trans_le (cuspScale_one_le F w v)) _))) (vectorModulus_pos v _)
      have hb : 0 ≤ b v := by dsimp only [b,sectionNorm]; split <;> exact norm_nonneg _
      have hpos := zero_le_one.trans (hB v)
      have hmax := le_max_right 1 (r v)
      have ht' : t v ≤ B v * max 1 (r v) := by
        dsimp only [t]
        split
        · exact one_le_mul_of_one_le_of_one_le (hB v) (le_max_left ..)
        · exact hexp.trans (mul_le_mul_of_nonneg_left hmax hpos)
      calc
        _ ≤ (B v * max 1 (r v))^L * b v := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (ht₀ v) ht' _) hb
        _ = B v^L * ((max 1 (r v))^L * b v) := by rw [mul_pow,mul_assoc]
        _ ≤ B v^L * H v := mul_le_mul_of_nonneg_left ((localBound v (y v) hn).trans
          (localThetaBound_antitone v (growthExponent_nonneg n) (zero_le_one.trans (hC v)) pos hy)) (pow_nonneg hpos _)
    have co₁ : ∀ᶠ v in cofinite, t v^L*b v = 1 := by filter_upwards [tco,bco] with v ht hb; simp only [ht,one_pow,one_mul]; exact hb
    have co₂ : ∀ᶠ v in cofinite, B v^L*H v = 1 := by filter_upwards [b₁,hc] with v hb hv; simp only [hb,one_pow,one_mul]; exact hv
    have bound := finprod_mono_real co₁ co₂ (fun v => mul_nonneg (pow_nonneg (ht₀ v) _) (by dsimp only [b,sectionNorm]; split <;> exact norm_nonneg _)) e
    have splitProd (T b : Place F → ℝ) (a₁ : ∀ᶠ v in cofinite, T v = 1) (b₁ : ∀ᶠ v in cofinite, b v = 1) :
        (∏ᶠ v, T v^L*b v) = (∏ᶠ v, T v)^L * ∏ᶠ v, b v := by
      rw [finprod_mul_distrib (f := fun v => T v^L) ((show Function.HasFiniteMulSupport T from eventually_cofinite.mp a₁).pow L)
        (eventually_cofinite.mp b₁),← finprod_pow (eventually_cofinite.mp a₁)]
    rw [splitProd t b tco bco,splitProd B H b₁ hc,ht] at bound
    exact (congrArg (W p^L * ·) he).trans_le bound
  obtain ⟨summable,bound⟩ := maj k
  have hs : Summable (fun p => V*β (σ p)) := (σ.summable_iff.mpr summable).mul_left V
  have ht := hs.of_nonneg_of_le nonneg domination
  refine ⟨ht,(ht.tsum_le_tsum domination hs).trans ?_⟩
  rw [tsum_mul_left,σ.tsum_eq β,mul_assoc]
  exact mul_le_mul_of_nonneg_left bound hV

private theorem cusp_theta_norm (Φ : ∀ v, d.schwartz v) (hf : ∀ᶠ v in cofinite, Φ v = d.basic v)
    (w : P) (K : Set G) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (u : A) (k : ℕ), ∀ ω ∈ K, ∀ g : ∀ v, d.cover v, ∀ hg : d.IsRestrictedCover g,
      d.LiftsAdelicMatrix (adelicUpper F u * ideleDiagonal F (cuspIdele F w)^k * ω) g →
      (∑' p, ‖d.evaluation (d.coverAction g hg (d.pure Φ hf)) p‖) ≤ M*(w.asIdeal.absNorm : ℝ)^(3*k) := by
  obtain ⟨M,hM,h⟩ := d.weighted_cusp_theta Φ hf w K hK 0
  exact ⟨M,hM,fun u k ω hw g hg hm => by simpa only [pow_zero,one_mul] using (h u k ω hw g hg hm).2⟩

/-- Lemma B.8 for the sum of absolute values of a translated pure section and
its Fourier transform, for every restricted lift and every unipotent parameter. -/
theorem cusp_theta_growth (Φ : ∀ v, d.schwartz v) (hf : ∀ᶠ v in cofinite, Φ v = d.basic v)
    (w : P) (K : Set G) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (u : A) (k : ℕ), ∀ ω ∈ K, ∀ g : ∀ v, d.cover v, ∀ hg : d.IsRestrictedCover g,
      d.LiftsAdelicMatrix (adelicUpper F u * ideleDiagonal F (cuspIdele F w)^k * ω) g →
      (∑' p, (‖d.evaluation (d.coverAction g hg (d.pure Φ hf)) p‖ +
        ‖d.evaluation (d.coverAction g hg (d.adelicFourier (d.pure Φ hf))) p‖)) ≤
        M*(w.asIdeal.absNorm : ℝ)^(3*k) := by
  let Ψ := fun v => d.fourier v (Φ v)
  have hΨ : ∀ᶠ v in cofinite, Ψ v = d.basic v := (hf.and d.eventually_fourier_basic).mono fun _ h => h.1 ▸ h.2
  obtain ⟨M,hM,h⟩ := d.cusp_theta_norm Φ hf w K hK
  obtain ⟨N,hN,h'⟩ := d.cusp_theta_norm Ψ hΨ w K hK
  refine ⟨M+N,add_nonneg hM hN,fun u k ω hω g hg hm => ?_⟩
  rw [d.adelicFourier_pure,(d.summable_theta _).tsum_add (d.summable_theta _),add_mul]
  exact add_le_add (h u k ω hω g hg hm) (h' u k ω hω g hg hm)

/-- The off-axis series of absolute values decays faster than every inverse
power of the cusp height. -/
theorem cusp_offAxis_decay (Φ : ∀ v, d.schwartz v) (hf : ∀ᶠ v in cofinite, Φ v = d.basic v)
    (w : P) (K : Set G) (hK : IsCompact K) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (u : A) (k : ℕ), ∀ ω ∈ K, ∀ g : ∀ v, d.cover v, ∀ hg : d.IsRestrictedCover g,
      d.LiftsAdelicMatrix (adelicUpper F u * ideleDiagonal F (cuspIdele F w)^k * ω) g →
      (∑' p : RationalPoint F, if p.val.1 = 0 then 0 else ‖d.evaluation (d.coverAction g hg (d.pure Φ hf)) p‖)
        ≤ M*((w.asIdeal.absNorm : ℝ)^(N*k))⁻¹ := by
  let q : ℝ := w.asIdeal.absNorm
  have hq : 0 < q := by dsimp [q]; exact_mod_cast (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w))
  obtain ⟨M,hM,h⟩ := d.weighted_cusp_theta Φ hf w K hK (N+3)
  refine ⟨M,hM,fun u k ω hω g hg hm => ?_⟩
  let f := fun p => ‖d.evaluation (d.coverAction g hg (d.pure Φ hf)) p‖
  let W := fun p : RationalPoint F => if p.val.1 = 0 then 1 else q^k
  let off := fun p : RationalPoint F => if p.val.1 = 0 then 0 else f p
  have le (p) : (q^k)^(N+3)*off p ≤ W p^(N+3)*f p := by
    by_cases hx : p.val.1 = 0 <;> simp [off,W,hx,f]
  have h₀ (p) : 0 ≤ (q^k)^(N+3)*off p := by dsimp [off,f]; split <;> positivity
  obtain ⟨hs,hb⟩ := h u k ω hω g hg hm
  have ht := ((hs.of_nonneg_of_le h₀ le).tsum_le_tsum le hs).trans hb
  rw [tsum_mul_left] at ht
  change (∑' p, off p) ≤ M*(q^(N*k))⁻¹
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hq (N*k))).mpr
  apply (mul_le_mul_iff_left₀ (pow_pos hq (3*k))).mp
  calc
    ((∑' p, off p)*q^(N*k))*q^(3*k) = (q^k)^(N+3)*(∑' p, off p) := by
      rw [← pow_mul,Nat.mul_comm k (N+3),Nat.add_mul,pow_add]; ring
    _ ≤ M*q^(3*k) := ht

end MetaplecticPoisson.Datum
