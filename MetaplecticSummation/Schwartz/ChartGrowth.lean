import MetaplecticSummation.LocalCharacterScaling
import MetaplecticSummation.FiniteGerms
import MetaplecticSummation.ArchimedeanFourierDecay

/-! Local growth bounds for the two Schwartz charts. -/
noncomputable section
namespace MetaplecticPoisson
open NumberField IsDedekindDomain Filter Set
open Classical

/-- The singularity exponent κ = 1 − 1/n. -/
def growthExponent (n : ℕ) : ℝ := ((n-1 : ℕ) : ℝ)/n

theorem growthExponent_nonneg (n : ℕ) : 0 ≤ growthExponent n := by unfold growthExponent; positivity

theorem growthExponent_le_one (n : ℕ) [NeZero n] : growthExponent n ≤ 1 := by
  rw [growthExponent,div_le_one (by exact_mod_cast NeZero.pos n)]
  exact_mod_cast Nat.sub_le n 1

theorem rpow_degree {n : ℕ} [NeZero n] {x : ℝ} (hx : 0 ≤ x) :
    (x^n)^(growthExponent n) = x^(n-1) := by
  rw [← Real.rpow_natCast_mul hx,growthExponent,mul_div_cancel₀ _ (by exact_mod_cast NeZero.ne n),Real.rpow_natCast]

theorem cone_growth {K P : Type} [NontriviallyNormedField K] [ProperSpace K] [TopologicalSpace P]
    {n : ℕ} [NeZero n] {dil : Kˣ → P → P} {f : P → ℂ}
    (i : Kˣ × K → P) (hi : Continuous i) (hd : ∀ u q, dil u (i q) = i (u^n*q.1,u.val^n*q.2))
    (extn : HasFiniteRayExtension n dil f) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a b, ‖b‖ ≤ ‖a.val‖ →
      ‖f (i (a,b))‖ * ‖a.val‖^(growthExponent n) ≤ C := by
  obtain ⟨T,B,hT,hB,hcover⟩ := compact_ray_shell (K := K) (NeZero.ne n)
  obtain ⟨E,hE,hval⟩ := extn
  obtain ⟨S,hS,hout⟩ := (hE.2 (i '' T) (hT.image hi)).2.1
  obtain ⟨M,hM⟩ := ((hT.image hi).prod hS).exists_bound_of_continuousOn hE.1.continuous.continuousOn
  refine ⟨max M 0 * B^(growthExponent n),mul_nonneg (le_max_right ..) (Real.rpow_nonneg hB.le _),?_⟩
  intro a b hab
  obtain ⟨q,u,hq,he,_,hhi⟩ := hcover a b hab
  have hbound : ‖E (i q) u.val‖ ≤ max M 0 := by
    by_cases hu : u.val ∈ S
    · exact (hM (i q,u.val) ⟨⟨q,hq,rfl⟩,hu⟩).trans (le_max_left ..)
    · rw [hout _ ⟨q,hq,rfl⟩ _ hu,norm_zero]
      exact le_max_right ..
  have h := congrArg norm (hval (i q) u)
  rw [hd,he,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)] at h
  calc
    _ ≤ ‖f (i (a,b))‖ * (B*‖u.val‖^n)^(growthExponent n) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hhi (growthExponent_nonneg _)) (norm_nonneg _)
    _ = ‖E (i q) u.val‖ * B^(growthExponent n) := by
      rw [Real.mul_rpow hB.le (pow_nonneg (norm_nonneg _) _),rpow_degree (norm_nonneg _),h]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hB.le _)

/-- If the normalized transform decreases rapidly in the root variable on
compact chart sets, it has the two exponents of (4.2) on the dominant cone. -/
private theorem arch_cone_growth {K : Type} [NontriviallyNormedField K] [ProperSpace K]
    {n : ℕ} [NeZero n] (m N : ℕ) (hN : 1 ≤ N) (g : Kˣ → K → ℂ)
    (h : ∀ T : Set (Kˣ × K), IsCompact T → ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ T, ∀ u : Kˣ,
      ‖g (u^n*q.1) (u.val^n*q.2)‖ * (‖u.val‖^m)^(n-1) * (1+‖u.val‖)^j ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b, ‖b‖ ≤ ‖a.val‖ →
      let r := ‖a.val‖^m
      ‖g a b‖ ≤ C * min (r^(-(growthExponent n))) (r^(-(N:ℝ))) := by
  obtain ⟨T,B,hT,hB,hcover⟩ := compact_ray_shell (K := K) (NeZero.ne n)
  obtain ⟨M,hM,H⟩ := h T hT (m*n*N)
  let U := B^m
  have hU : 0 ≤ U := (pow_pos hB _).le
  let C := max (M*U^(growthExponent n)) (M*U^N)
  have hC : 0 ≤ C := (mul_nonneg hM (Real.rpow_nonneg hU _)).trans (le_max_left ..)
  refine ⟨C,hC,?_⟩
  intro a b hab
  obtain ⟨q,u,hq,he,_,hhi⟩ := hcover a b hab
  let s := ‖u.val‖
  let r := ‖a.val‖^m
  have hs : 0 < s := norm_pos_iff.mpr u.ne_zero
  have hr : 0 < r := pow_pos (norm_pos_iff.mpr a.ne_zero) _
  have hr' : r ≤ U*(s^m)^n := by
    have e := pow_le_pow_left₀ (norm_nonneg _) hhi m
    simpa only [U,r,s,mul_pow,← pow_mul,Nat.mul_comm n m] using e
  have HH := H q hq u
  rw [show g (u^n*q.1) (u.val^n*q.2) = g a b from congrArg (Function.uncurry g) he] at HH
  change ‖g a b‖ * (s^m)^(n-1) * (1+s)^(m*n*N) ≤ M at HH
  have hlow : ‖g a b‖ * (s^m)^(n-1) ≤ M := (le_mul_of_one_le_right (by positivity)
    (one_le_pow₀ (le_add_of_nonneg_right hs.le) : 1 ≤ (1+s)^(m*n*N))).trans HH
  have hfast : ‖g a b‖ * s^(m*n*N) ≤ M := by
    rcases le_total s 1 with h | h
    · apply le_trans (mul_le_mul_of_nonneg_left _ (norm_nonneg _)) hlow
      rw [← pow_mul]
      apply pow_le_pow_of_le_one hs.le h
      exact (Nat.mul_le_mul_left m (Nat.sub_le n 1)).trans (Nat.le_mul_of_pos_right _ hN)
    · apply le_trans _ HH
      rw [mul_assoc ‖g a b‖]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (pow_le_pow_left₀ hs.le (le_add_of_nonneg_left zero_le_one) _).trans
        (le_mul_of_one_le_left (by positivity) (one_le_pow₀ (one_le_pow₀ h)))
  change ‖g a b‖ ≤ C * min (r^(-(growthExponent n))) (r^(-(N:ℝ)))
  rw [mul_min_of_nonneg _ _ hC,Real.rpow_neg hr.le,Real.rpow_neg hr.le,Real.rpow_natCast,
    ← div_eq_mul_inv,← div_eq_mul_inv,le_min_iff,le_div_iff₀ (Real.rpow_pos_of_pos hr _),le_div_iff₀ (pow_pos hr _)]
  constructor
  · have h' := Real.rpow_le_rpow hr.le hr' (growthExponent_nonneg n)
    rw [Real.mul_rpow hU (pow_nonneg (pow_nonneg hs.le _) _),rpow_degree (pow_nonneg hs.le _)] at h'
    calc
      _ ≤ ‖g a b‖ * (U^(growthExponent n)*(s^m)^(n-1)) := mul_le_mul_of_nonneg_left h' (norm_nonneg _)
      _ = (‖g a b‖*(s^m)^(n-1))*U^(growthExponent n) := by ring
      _ ≤ C := (mul_le_mul_of_nonneg_right hlow (Real.rpow_nonneg hU _)).trans (le_max_left ..)
  · have h' := pow_le_pow_left₀ hr.le hr' N
    rw [mul_pow U,← pow_mul s m n,← pow_mul s (m*n) N] at h'
    calc
      _ ≤ ‖g a b‖ * (U^N*s^(m*n*N)) := mul_le_mul_of_nonneg_left h' (norm_nonneg _)
      _ = (‖g a b‖*s^(m*n*N))*U^N := by ring
      _ ≤ C := (mul_le_mul_of_nonneg_right hfast (pow_nonneg hU _)).trans (le_max_right ..)

namespace Datum
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- Uniform growth in an arbitrary vertical slice of the finite X-chart. -/
theorem finite_vertical_growth (p : Prime F) (Φ : d.schwartz (.inr p)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : (LocalField F (.inr p))ˣ) (y : LocalField F (.inr p)),
      ‖Φ.val.1 a y‖ * ‖a.val‖^(growthExponent n) ≤ C := by
  let K := p.adicCompletion F
  letI : NontriviallyNormedField K := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  obtain ⟨ex,ey⟩ := d.finite_schwartz_rayExtensions p Φ
  obtain ⟨A,h₀,hA⟩ := cone_growth (K := K) id continuous_id (fun _ _ => rfl) ex
  obtain ⟨B,_,hB⟩ := cone_growth (K := K) Prod.swap continuous_swap (fun _ _ => rfl) ey
  refine ⟨max A B,h₀.trans (le_max_left ..),?_⟩
  intro a y
  rcases le_total ‖y‖ ‖a.val‖ with h | h
  · exact (hA a y h).trans (le_max_left ..)
  · let b := Units.mk0 y (norm_pos_iff.mp ((norm_pos_iff.mpr a.ne_zero).trans_le h))
    change ‖Φ.val.1 a b.val‖ * _ ≤ _
    rw [d.schwartz_glues _ Φ a b,norm_mul,d.norm_symbol,one_mul]
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) h (growthExponent_nonneg n))
      (norm_nonneg _)).trans ((hB b a.val h).trans (le_max_right ..))

/-- The corresponding slice estimate in the horizontal direction, including
the vertical axis where the X-chart is unavailable. -/
theorem finite_horizontal_growth (p : Prime F) (Φ : d.schwartz (.inr p)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : LocalField F (.inr p)) (b : (LocalField F (.inr p))ˣ),
      ‖Φ.val.2 x b‖ * ‖b.val‖^(growthExponent n) ≤ C := by
  let K := p.adicCompletion F
  letI : NontriviallyNormedField K := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  obtain ⟨A,h₀,hA⟩ := d.finite_vertical_growth p Φ
  obtain ⟨B,_,hB⟩ := cone_growth (K := K) Prod.swap continuous_swap (fun _ _ => rfl)
    (d.finite_schwartz_rayExtensions p Φ).2
  refine ⟨max A B,h₀.trans (le_max_left ..),?_⟩
  intro x b
  rcases le_total ‖x‖ ‖b.val‖ with h | h
  · exact (hB b x h).trans (le_max_right ..)
  · let a := Units.mk0 x (norm_pos_iff.mp ((norm_pos_iff.mpr b.ne_zero).trans_le h))
    have hx := hA a b.val
    rw [d.schwartz_glues _ Φ a b,norm_mul,d.norm_symbol,one_mul] at hx
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) h (growthExponent_nonneg n))
      (norm_nonneg _)).trans (hx.trans (le_max_left ..))

/-- The archimedean chart bound (4.2) at order N. -/
def ArchGrowth (w : InfinitePlace F) (n N : ℕ) (f : Charts w.Completion) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ z : w.Completion × w.Completion, z ≠ 0 →
    let r := max (modulus F (.inl w) z.1) (modulus F (.inl w) z.2)
    let bound := C * min (r^(-(growthExponent n))) (r^(-(N : ℝ)))
    ‖xChart f z‖ ≤ bound ∧ ‖yChart f z‖ ≤ bound

private theorem rapidChart_weight {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {g : E → ℂ} (hg : rapidChart U g) (m N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ U, z ≠ 0 →
      let r := ‖z‖^m
      ‖g z‖ ≤ C * min (r^(-(growthExponent n))) (r^(-(N : ℝ))) := by
  obtain ⟨A,hA⟩ := hg.2 0 0
  obtain ⟨B,hB⟩ := hg.2 0 (m*N)
  let C := max 0 (max A B)
  have hC : 0 ≤ C := le_max_left ..
  refine ⟨C,hC,?_⟩
  intro z hz hn
  let r := ‖z‖^m
  have hr : 0 < r := pow_pos (norm_pos_iff.mpr hn) _
  have ha : ‖g z‖ ≤ A := by simpa using hA z hz
  have hb := hB z hz
  rw [norm_iteratedFDeriv_zero,pow_mul] at hb
  change ‖g z‖ ≤ B * min (r^N) (r^N)⁻¹ at hb
  have hmin : 0 ≤ min (r^N) (r^N)⁻¹ := le_min (pow_nonneg hr.le _) (inv_nonneg.mpr (pow_nonneg hr.le _))
  have hfast : ‖g z‖ ≤ C*r^(-(N : ℝ)) := by
    rw [Real.rpow_neg hr.le,Real.rpow_natCast]
    exact hb.trans ((mul_le_mul_of_nonneg_right ((le_max_right A B).trans (le_max_right ..)) hmin).trans
      (mul_le_mul_of_nonneg_left (min_le_right ..) hC))
  change ‖g z‖ ≤ C * min (r^(-(growthExponent n))) (r^(-(N : ℝ)))
  rw [mul_min_of_nonneg _ _ hC]
  refine le_min ?_ hfast
  rcases le_total r 1 with h | h
  · exact (ha.trans ((le_max_left A B).trans (le_max_right ..))).trans
      (le_mul_of_one_le_right hC (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr h (neg_nonpos.mpr (growthExponent_nonneg n))))
  · apply hfast.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h _) hC)
    exact neg_le_neg ((growthExponent_le_one n).trans (by exact_mod_cast hN))

private theorem archTest_growth {w : InfinitePlace F} {L : Type} [NormedField L] [NormedAlgebra ℝ L]
    (e : w.Completion ≃+* L) (he : Isometry e) {f : Charts w.Completion}
    (hf : archTest e f) (N : ℕ) (hN : 1 ≤ N) : ArchGrowth w n N f := by
  obtain ⟨A,hA,hx⟩ := rapidChart_weight (n := n) hf.1 w.mult N hN
  obtain ⟨B,hB,hy⟩ := rapidChart_weight (n := n) hf.2 w.mult N hN
  refine ⟨max A B,hA.trans (le_max_left ..),?_⟩
  rintro ⟨x,y⟩ hn
  let z : L × L := (e x,e y)
  have hz : z ≠ 0 := by
    intro h
    apply hn
    exact Prod.ext ((map_eq_zero e).mp (congrArg Prod.fst h)) ((map_eq_zero e).mp (congrArg Prod.snd h))
  let r := max (modulus F (.inl w) x) (modulus F (.inl w) y)
  have er : ‖z‖^w.mult = r := by
    change (max ‖e x‖ ‖e y‖)^w.mult = max (‖x‖^w.mult) (‖y‖^w.mult)
    rw [he.norm_map_of_map_zero e.map_zero,he.norm_map_of_map_zero e.map_zero]
    rcases le_total ‖x‖ ‖y‖ with h | h
    · rw [max_eq_right h,max_eq_right (pow_le_pow_left₀ (norm_nonneg _) h _)]
    · rw [max_eq_left h,max_eq_left (pow_le_pow_left₀ (norm_nonneg _) h _)]
  let W := min (r^(-(growthExponent n))) (r^(-(N : ℝ)))
  have hr : 0 ≤ r := er ▸ pow_nonneg (norm_nonneg _) _
  have hW : 0 ≤ W := le_min (Real.rpow_nonneg hr _) (Real.rpow_nonneg hr _)
  change ‖xChart f (x,y)‖ ≤ max A B*W ∧ ‖yChart f (x,y)‖ ≤ max A B*W
  constructor
  · by_cases h : x = 0
    · rw [show xChart f (x,y) = 0 from dif_neg (not_ne_iff.mpr h),norm_zero]
      exact mul_nonneg (hA.trans (le_max_left ..)) hW
    · have hz' := hx z ((map_ne_zero e).mpr h) hz
      dsimp only at hz'
      rw [er] at hz'
      exact (by simpa only [z,RingEquiv.symm_apply_apply] using hz' : ‖xChart f (x,y)‖ ≤ A*W).trans
        (mul_le_mul_of_nonneg_right (le_max_left ..) hW)
  · by_cases h : y = 0
    · rw [show yChart f (x,y) = 0 from dif_neg (not_ne_iff.mpr h),norm_zero]
      exact mul_nonneg (hB.trans (le_max_right ..)) hW
    · have hz' := hy z ((map_ne_zero e).mpr h) hz
      dsimp only at hz'
      rw [er] at hz'
      exact (by simpa only [z,RingEquiv.symm_apply_apply] using hz' : ‖yChart f (x,y)‖ ≤ B*W).trans
        (mul_le_mul_of_nonneg_right (le_max_right ..) hW)

theorem arch_test_growth (w : InfinitePlace F) {f : Charts w.Completion} (hf : f ∈ d.testSet (.inl w))
    (N : ℕ) (hN : 1 ≤ N) : ArchGrowth w n N f := by
  by_cases hw : w.IsReal
  · exact archTest_growth _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw)
      (by simpa only [testSet,dif_pos hw] using hf.2) N hN
  · exact archTest_growth _ (InfinitePlace.Completion.isometry_extensionEmbedding w)
      (by simpa only [testSet,dif_neg hw] using hf.2) N hN

private theorem arch_hat_weight (w : InfinitePlace F) {f : Charts w.Completion} (hf : f ∈ d.testSet (.inl w))
    (T : Set (w.Completionˣ × w.Completion)) (hT : IsCompact T) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ T, ∀ u : w.Completion, ‖d.archRadonHat w f q u‖ * (1+‖u‖)^j ≤ C := by
  obtain ⟨A,hA,ha⟩ := (d.arch_radon_hat_bounded w hf).2 T hT
  obtain ⟨B,_,hb⟩ := d.arch_radon_hat_decay w hf T hT j
  refine ⟨max (A*2^j) B,(mul_nonneg hA (by positivity)).trans (le_max_left ..),?_⟩
  intro q hq u
  rcases le_total ‖u‖ 1 with h | h
  · exact (mul_le_mul (ha q hq u) (pow_le_pow_left₀ (by positivity) (by linarith : 1+‖u‖ ≤ 2) j)
      (by positivity) hA).trans (le_max_left ..)
  · exact (hb q hq u h).trans (le_max_right ..)

set_option maxHeartbeats 800000 in
/-- The archimedean case of the transform decay corollary in §4. -/
theorem arch_transform_growth (w : InfinitePlace F) {f : Charts w.Completion} (hf : f ∈ d.testSet (.inl w))
    (N : ℕ) (hN : 1 ≤ N) : ArchGrowth w n N (d.integralTransform (.inl w) f) := by
  let v : Place F := .inl w
  let K := LocalField F v
  letI : LocallyCompactSpace K := inferInstanceAs (LocallyCompactSpace w.Completion)
  letI : NontriviallyNormedField K := archNontriviallyNormedCompletion w
  letI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  let g := d.integralTransform v f
  let c : ℂ := (Real.sqrt (modulus F v (n : K)))⁻¹
  have weight (T : Set (Kˣ × K)) (hT : IsCompact T) (j : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ T, ∀ u : Kˣ,
        let x := u^n*q.1
        let y := u.val^n*q.2
        let W := (‖u.val‖^w.mult)^(n-1)*(1+‖u.val‖)^j
        ‖g.1 x y‖*W ≤ C ∧ ‖g.2 y x‖*W ≤ C := by
    obtain ⟨M,hM,H⟩ := d.arch_hat_weight w hf T hT j
    refine ⟨‖c‖*M,mul_nonneg (norm_nonneg _) hM,?_⟩
    intro q hq u
    let V := (‖u.val‖^w.mult)^(n-1)
    have hm : 0 ≤ ‖u.val‖^w.mult := pow_nonneg (norm_nonneg _) _
    have bound {a b : ℂ} (e : ((‖u.val‖^w.mult : ℝ) : ℂ)^(n-1)*a = c*b)
        (hb : ‖b‖ ≤ ‖d.archRadonHat w f q u.val‖) : ‖a‖*(V*(1+‖u.val‖)^j) ≤ ‖c‖*M := by
      have hh := congrArg norm e
      rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hm,norm_mul,mul_comm] at hh
      change ‖a‖*V = ‖c‖*‖b‖ at hh
      rw [← mul_assoc,hh,mul_assoc]
      exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hb (by positivity)).trans (H q hq u.val)) (norm_nonneg _)
    exact ⟨bound ((d.transform_pow_ray v f u).1 q.1 q.2) (le_max_left ..),
      bound ((d.transform_pow_ray v f u).2 q.2 q.1) (le_max_right ..)⟩
  obtain ⟨A,hA,ha⟩ := arch_cone_growth (K := K) (n := n) w.mult N hN g.1 (by
    intro T hT j
    obtain ⟨M,hM,H⟩ := weight T hT j
    exact ⟨M,hM,fun q hq u => by simpa only [mul_assoc] using (H q hq u).1⟩)
  obtain ⟨B,hB,hb⟩ := arch_cone_growth (K := K) (n := n) w.mult N hN (fun y x => g.2 x y) (by
    intro T hT j
    obtain ⟨M,hM,H⟩ := weight T hT j
    exact ⟨M,hM,fun q hq u => by simpa only [mul_assoc] using (H q hq u).2⟩)
  let C := max A B
  change ∃ C : ℝ, 0 ≤ C ∧ ∀ z : K × K, z ≠ 0 →
    let r := max (modulus F v z.1) (modulus F v z.2)
    let bound := C * min (r^(-(growthExponent n))) (r^(-(N : ℝ)))
    ‖xChart g z‖ ≤ bound ∧ ‖yChart g z‖ ≤ bound
  refine ⟨C,hA.trans (le_max_left ..),?_⟩
  rintro ⟨x,y⟩ hn
  let r := max (modulus F v x) (modulus F v y)
  let W := min (r^(-(growthExponent n))) (r^(-(N:ℝ)))
  have hr : 0 ≤ r := (pow_nonneg (norm_nonneg x) w.mult).trans (le_max_left ..)
  have hW : 0 ≤ W := le_min (Real.rpow_nonneg hr _) (Real.rpow_nonneg hr _)
  have hC : 0 ≤ C*W := mul_nonneg (hA.trans (le_max_left ..)) hW
  have e (a b : Kˣ) : ‖g.1 a b.val‖ = ‖g.2 a.val b‖ := by
    rw [d.arch_transform_glues w hf.1 a b,norm_mul,d.norm_symbol,one_mul]
  change ‖xChart g (x,y)‖ ≤ C*W ∧ ‖yChart g (x,y)‖ ≤ C*W
  rcases le_total ‖y‖ ‖x‖ with h | h
  · have hx : x ≠ 0 := fun hx => hn (Prod.ext hx (norm_le_zero_iff.mp (by simpa [hx] using h)))
    let a := Units.mk0 x hx
    have er : r = ‖x‖^w.mult := max_eq_left (pow_le_pow_left₀ (norm_nonneg y) h _)
    have hdom : ‖g.1 a y‖ ≤ C*W := le_trans (by simpa only [W,er,a,Units.val_mk0] using! ha a y h : ‖g.1 a y‖ ≤ A*W)
      (mul_le_mul_of_nonneg_right (le_max_left ..) hW)
    refine ⟨by simpa only [xChart,dif_pos hx,a] using hdom,?_⟩
    by_cases hy : y ≠ 0
    · simpa only [yChart,dif_pos hy,a,Units.val_mk0] using! (e a (Units.mk0 y hy)).symm.trans_le hdom
    · simpa only [yChart,dif_neg hy,norm_zero] using hC
  · have hy : y ≠ 0 := fun hy => hn (Prod.ext (norm_le_zero_iff.mp (by simpa [hy] using h)) hy)
    let b := Units.mk0 y hy
    have er : r = ‖y‖^w.mult := max_eq_right (pow_le_pow_left₀ (norm_nonneg x) h _)
    have hdom : ‖g.2 x b‖ ≤ C*W := le_trans (by simpa only [W,er,b,Units.val_mk0] using! hb b x h : ‖g.2 x b‖ ≤ B*W)
      (mul_le_mul_of_nonneg_right (le_max_right ..) hW)
    refine ⟨?_,by simpa only [yChart,dif_pos hy,b] using hdom⟩
    by_cases hx : x ≠ 0
    · simpa only [xChart,dif_pos hx,b,Units.val_mk0] using! (e (Units.mk0 x hx) b).trans_le hdom
    · simpa only [xChart,dif_neg hx,norm_zero] using hC

/-- Every archimedean Schwartz section satisfies (4.2), by the two types of generators. -/
theorem arch_local_growth (w : InfinitePlace F) (f : d.schwartz (.inl w)) (N : ℕ) (hN : 1 ≤ N) :
    ArchGrowth w n N f.val := by
  refine Submodule.span_induction (p := fun g _ => ArchGrowth w n N g) ?_ ?_ ?_ ?_ f.property
  · rintro g (hg | ⟨g,hg,rfl⟩)
    · exact d.arch_test_growth w hg N hN
    · exact d.arch_transform_growth w hg N hN
  · exact ⟨0,le_rfl,fun z _ => by simp [xChart,yChart]⟩
  · rintro g k _ _ ⟨A,hA,ha⟩ ⟨B,hB,hb⟩
    refine ⟨A+B,add_nonneg hA hB,fun z hz => ?_⟩
    have addbound {a b : ℂ} {W : ℝ} (h : ‖a‖ ≤ A*W) (h' : ‖b‖ ≤ B*W) : ‖a+b‖ ≤ (A+B)*W := by
      rw [add_mul]
      exact (norm_add_le ..).trans (add_le_add h h')
    have ex : xChart (g+k) z = xChart g z + xChart k z := by unfold xChart; split <;> simp
    have ey : yChart (g+k) z = yChart g z + yChart k z := by unfold yChart; split <;> simp
    exact ⟨ex ▸ addbound (ha z hz).1 (hb z hz).1,ey ▸ addbound (ha z hz).2 (hb z hz).2⟩
  · rintro c g _ ⟨A,hA,ha⟩
    refine ⟨‖c‖*A,mul_nonneg (norm_nonneg _) hA,fun z hz => ?_⟩
    have sb {a : ℂ} {W : ℝ} (h : ‖a‖ ≤ A*W) : ‖c*a‖ ≤ (‖c‖*A)*W := by
      rw [norm_mul,mul_assoc]
      exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
    have ex : xChart (c • g) z = c*xChart g z := by unfold xChart; split <;> simp
    have ey : yChart (c • g) z = c*yChart g z := by unfold yChart; split <;> simp
    exact ⟨ex ▸ sb (ha z hz).1,ey ▸ sb (ha z hz).2⟩

section Arch
open MeasureTheory
variable (w : InfinitePlace F)
local notation "vi" => (Sum.inl w : Place F)
local notation "K" => LocalField F vi

theorem continuous_arch_schwartz_charts (Φ : d.schwartz vi) :
    Continuous (Function.uncurry Φ.val.1) ∧ Continuous (Function.uncurry Φ.val.2) := by
  refine Submodule.span_induction (p := fun g _ =>
    Continuous (Function.uncurry g.1) ∧ Continuous (Function.uncurry g.2)) ?_ ?_ ?_ ?_ Φ.property
  · rintro g (hg | ⟨f,hf,rfl⟩)
    · obtain ⟨hx,hy⟩ := d.arch_test_lineCharts w hg
      exact ⟨hx.1,hy.1.comp (f := Prod.swap) continuous_swap⟩
    · have hc := (d.arch_radon_hat_bounded w hf).1.comp
        (continuous_id.prodMk (continuous_const (y := (1:K))))
      let s : ℂ := (Real.sqrt (modulus F vi (n : K)) : ℂ)⁻¹
      constructor
      · apply ((continuous_const (y := s)).mul hc.fst).congr
        intro z
        change s * d.hat vi _ 1 = s * _
        simp only [hat,one_mul]
        congr 1
        apply integral_congr_ae
        filter_upwards with t using mul_comm _ _
      · apply ((continuous_const (y := s)).mul (hc.snd.comp continuous_swap)).congr
        intro z
        change s * d.hat vi _ 1 = s * _
        simp only [hat,one_mul]
        congr 1
        apply integral_congr_ae
        filter_upwards with t using mul_comm _ _
  · exact ⟨continuous_const,continuous_const⟩
  · intro f g _ _ hf hg
    exact ⟨hf.1.add hg.1,hf.2.add hg.2⟩
  · intro c g _ hg
    exact ⟨continuous_const.mul hg.1,continuous_const.mul hg.2⟩

end Arch

end Datum
end MetaplecticPoisson
