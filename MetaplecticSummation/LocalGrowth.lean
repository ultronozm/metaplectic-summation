import MetaplecticSummation.ThetaMajorant
import MetaplecticSummation.FiniteGerms

/-! The local growth bounds for the theta estimate. -/
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

private theorem rpow_degree {n : ℕ} [NeZero n] {x : ℝ} (hx : 0 ≤ x) :
    (x^n)^(growthExponent n) = x^(n-1) := by
  rw [← Real.rpow_natCast_mul hx,growthExponent,mul_div_cancel₀ _ (by exact_mod_cast NeZero.ne n),Real.rpow_natCast]

private theorem cone_growth {K P : Type} [NontriviallyNormedField K] [ProperSpace K] [TopologicalSpace P]
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

namespace Datum
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

private theorem norm_localValue_dominant (z : RationalPoint F) (v : Place F) (f : d.schwartz v) :
    let x := diagonal F v z.val.1
    let y := diagonal F v z.val.2
    (∀ a : (LocalField F v)ˣ, a.val = x → ‖y‖ ≤ ‖x‖ → ‖d.localValue z v f‖ = ‖f.val.1 a y‖) ∧
    (∀ b : (LocalField F v)ˣ, b.val = y → ‖x‖ ≤ ‖y‖ → ‖d.localValue z v f‖ = ‖f.val.2 x b‖) := by
  dsimp only
  constructor
  · intro a ha _
    have hx : z.val.1 ≠ 0 := fun e => a.ne_zero (ha.trans (e ▸ map_zero _))
    have h := (map_ne_zero (diagonal F v)).mpr hx
    simp only [localValue,if_pos hx,xChart,diagonalPoint,dif_pos h,show Units.mk0 _ h = a from Units.ext ha.symm]
  · intro b hb _
    have hy := (map_ne_zero (diagonal F v)).mpr (show z.val.2 ≠ 0 from fun e => b.ne_zero (hb.trans (e ▸ map_zero _)))
    by_cases hx : z.val.1 ≠ 0
    · have hn := (map_ne_zero (diagonal F v)).mpr hx
      let a := Units.mk0 _ hn
      change ‖d.localValue z v f‖ = ‖f.val.2 a.val b‖
      rw [show d.localValue z v f = f.val.1 a b.val by simp [localValue,hx,xChart,diagonalPoint,hn,a,hb],
        d.schwartz_glues v f a b,norm_mul,d.norm_symbol,one_mul]
    · simp only [localValue,if_neg hx,yChart,diagonalPoint,dif_pos hy,show Units.mk0 _ hy = b from Units.ext hb.symm]

/-- At each finite place every Schwartz section satisfies the finite part of
(B.1), with one constant controlling the support and the size. -/
theorem finite_local_growth (p : Prime F) (f : d.schwartz (.inr p)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z, ‖d.localValue z (.inr p) f‖ ≤
      localThetaBound (growthExponent n) (.inr p) C (vectorModulus (.inr p) z) := by
  let v : Place F := .inr p
  let K := p.adicCompletion F
  letI : NontriviallyNormedField K := FinitePlace.nontriviallyNormedCompletion p
  letI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  obtain ⟨ex,ey⟩ := d.finite_schwartz_rayExtensions p f
  obtain ⟨A,_,hA⟩ := cone_growth (K := K) id continuous_id (fun _ _ => rfl) ex
  obtain ⟨B,_,hB⟩ := cone_growth (K := K) Prod.swap continuous_swap (fun _ _ => rfl) ey
  obtain ⟨S,hS,hout⟩ := (d.finite_germs p f).2.1
  obtain ⟨R,hR⟩ := hS.isBounded.exists_norm_le
  let C := max (max A B) (max 1 R)
  refine ⟨C,(le_max_left 1 R).trans (le_max_right ..),?_⟩
  intro z
  let x := diagonal F v z.val.1
  let y := diagonal F v z.val.2
  let r := vectorModulus v z
  have hr : 0 < r := vectorModulus_pos _ _
  have hr' : 0 < max ‖x‖ ‖y‖ := hr
  change _ ≤ if r ≤ C then C*r^(-(growthExponent n)) else 0
  by_cases hc : r ≤ C
  · rw [if_pos hc,Real.rpow_neg hr.le,← div_eq_mul_inv,le_div_iff₀ (Real.rpow_pos_of_pos hr _)]
    obtain ⟨h₁,h₂⟩ := d.norm_localValue_dominant z v f
    change _ * (max ‖x‖ ‖y‖)^(growthExponent n) ≤ C
    rcases le_total ‖y‖ ‖x‖ with h | h
    · have hx : x ≠ 0 := norm_pos_iff.mp (by simpa only [max_eq_left h] using hr')
      let a := Units.mk0 x hx
      rw [max_eq_left h,h₁ a rfl h]
      exact (hA a y h).trans ((le_max_left A B).trans (le_max_left ..))
    · have hy : y ≠ 0 := norm_pos_iff.mp (by simpa only [max_eq_right h] using hr')
      let b := Units.mk0 y hy
      rw [max_eq_right h,h₂ b rfl h]
      exact (hB b x h).trans ((le_max_right A B).trans (le_max_left ..))
  · rw [if_neg hc]
    have hh : (x,y) ∉ S := fun h => hc <| (hR _ h).trans ((le_max_right 1 R).trans (le_max_right ..))
    obtain ⟨hx,hy⟩ := hout (x,y) hh
    by_cases h : z.val.1 ≠ 0
    · rw [show d.localValue z v f = xChart f.val (x,y) by simp only [localValue,if_pos h,x,y,diagonalPoint],hx,norm_zero]
    · rw [show d.localValue z v f = yChart f.val (x,y) by simp only [localValue,if_neg h,x,y,diagonalPoint],hy,norm_zero]

private theorem basic_weight_bound (p : Prime F) (r : ℝ) (hr₀ : 0 < r) :
    ‖∑' k : ℕ, if r = ((p.asIdeal.absNorm : ℝ)^(n*k))⁻¹ then
        (p.asIdeal.absNorm : ℂ)^((n-1)*k) else 0‖ ≤
      localThetaBound (growthExponent n) (.inr p) 1 r := by
  let q : ℝ := p.asIdeal.absNorm
  have hq : 1 < q := by dsimp [q]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  let R (k : ℕ) := (q^(n*k))⁻¹
  change ‖∑' k : ℕ, if r = R k then (p.asIdeal.absNorm : ℂ)^((n-1)*k) else 0‖ ≤ _
  by_cases he : ∃ k, r = R k
  · obtain ⟨k,rfl⟩ := he
    have inj : Function.Injective R := by
      intro i j h
      simpa only [R,inv_inj,pow_right_inj₀ (zero_lt_one.trans hq) hq.ne',Nat.mul_right_inj (NeZero.ne n)] using h
    rw [tsum_eq_single k (fun j hj => if_neg (fun h => hj (inj h.symm))),if_pos rfl,norm_pow,Complex.norm_natCast]
    have hr : R k ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hq.le)
    change q^((n-1)*k) ≤ if R k ≤ 1 then 1*(R k)^(-(growthExponent n)) else 0
    rw [if_pos hr,one_mul]
    have hq' := (zero_lt_one.trans hq).le
    dsimp only [R]
    rw [Real.rpow_neg (inv_nonneg.mpr (pow_nonneg hq' _)),Real.inv_rpow (pow_nonneg hq' _),inv_inv,
      Nat.mul_comm n k,pow_mul q k n,rpow_degree (pow_nonneg hq' k),← pow_mul,Nat.mul_comm]
  · have ht (k : ℕ) : r ≠ R k := fun h => he ⟨k,h⟩
    have hzero : (fun k : ℕ => if r = R k then (p.asIdeal.absNorm : ℂ)^((n-1)*k) else 0) = fun _ => 0 :=
      funext fun k => if_neg (ht k)
    rw [hzero,tsum_zero,norm_zero]
    change 0 ≤ if r ≤ 1 then 1*r^(-(growthExponent n)) else 0
    split
    · exact mul_nonneg zero_le_one (Real.rpow_nonneg hr₀.le _)
    · exact le_rfl

/-- The reference section has constant one in the finite local bound. -/
theorem basic_local_growth (p : Prime F) (z : RationalPoint F) :
    ‖d.localValue z (.inr p) (d.basic (.inr p))‖ ≤
      localThetaBound (growthExponent n) (.inr p) 1 (vectorModulus (.inr p) z) := by
  let v : Place F := .inr p
  let x := diagonal F v z.val.1
  let y := diagonal F v z.val.2
  let f := d.basic v
  have hr := vectorModulus_pos v z
  have hr' : 0 < max ‖x‖ ‖y‖ := hr
  by_cases hp : p.asIdeal.absNorm.Coprime n
  · have ef : f.val = d.basicCharts p := by
      change (d.basic (.inr p)).val = d.basicCharts p
      simp only [basic, dif_pos hp]
    obtain ⟨h₁,h₂⟩ := d.norm_localValue_dominant z v f
    rcases le_total ‖y‖ ‖x‖ with h | h
    · have hx : x ≠ 0 := norm_pos_iff.mp (by simpa only [max_eq_left h] using hr')
      let a := Units.mk0 x hx
      rw [h₁ a rfl h,ef]
      change ‖(d.basicCharts p).1 a y‖ ≤ localThetaBound _ _ _ (max ‖x‖ ‖y‖)
      simpa only [basicCharts,a,Units.val_mk0,if_pos h,mul_one,max_eq_left h] using
        basic_weight_bound (n := n) p ‖x‖ (norm_pos_iff.mpr hx)
    · have hy : y ≠ 0 := norm_pos_iff.mp (by simpa only [max_eq_right h] using hr')
      let b := Units.mk0 y hy
      rw [h₂ b rfl h,ef]
      change ‖(d.basicCharts p).2 x b‖ ≤ localThetaBound _ _ _ (max ‖x‖ ‖y‖)
      simpa only [basicCharts,b,Units.val_mk0,if_pos h,mul_one,max_eq_right h] using
        basic_weight_bound (n := n) p ‖y‖ (norm_pos_iff.mpr hy)
  · have hf : (d.basic v).val = 0 := by simp [v,basic,hp]
    have he : d.localValue z v (d.basic v) = 0 := by simp [localValue,xChart,yChart,hf]
    rw [he,norm_zero]
    exact localThetaBound_nonneg _ _ zero_le_one hr

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

/-- The archimedean case of the transform decay corollary in §4. -/
theorem arch_transform_growth (w : InfinitePlace F) {f : Charts w.Completion} (hf : f ∈ d.testSet (.inl w))
    (N : ℕ) (hN : 1 ≤ N) : ArchGrowth w n N (d.integralTransform (.inl w) f) := by sorry

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

theorem theta_local_bounds (f : ∀ v, d.schwartz v) (hf : ∀ᶠ v in cofinite, f v = d.basic v) :
    ∃ C : Place F → ℝ, (∀ v, 0 ≤ C v) ∧ (∀ p : Prime F, 1 ≤ C (.inr p)) ∧
      (∀ᶠ v in cofinite, C v = 1) ∧ ∀ z v, ‖d.localValue z v (f v)‖ ≤
        localThetaBound (growthExponent n) v (C v) (vectorModulus v z) := by
  choose B hB hb using fun p => d.finite_local_growth p (f (.inr p))
  choose A hA ha using fun w => d.arch_local_growth w (f (.inl w)) 4 (by decide)
  let C : Place F → ℝ := fun v => match v with
    | .inr p => if f (.inr p) = d.basic (.inr p) then 1 else B p
    | .inl w => A w
  have hfin (p : Prime F) : 1 ≤ C (.inr p) := by
    dsimp only [C]
    split
    · exact le_rfl
    · exact hB p
  refine ⟨C,fun v => by cases v with
                         | inr p => exact zero_le_one.trans (hfin p)
                         | inl w => exact hA w,hfin,?_,?_⟩
  · filter_upwards [hf,eventually_place_of_finite (P := fun v : Place F => ∃ p : Prime F, v = .inr p)
      (.of_forall fun p => ⟨p,rfl⟩)] with v h ⟨p,hp⟩
    subst v
    exact if_pos h
  · intro z v
    cases v with
    | inr p =>
      by_cases h : f (.inr p) = d.basic (.inr p)
      · simpa only [C,if_pos h,h] using d.basic_local_growth p z
      · simpa only [C,if_neg h] using hb p z
    | inl w =>
      have hn : diagonalPoint z (.inl w) ≠ 0 := by
        intro h
        apply z.property
        exact Prod.ext ((map_eq_zero (diagonal F (.inl w))).mp (congrArg Prod.fst h))
          ((map_eq_zero (diagonal F (.inl w))).mp (congrArg Prod.snd h))
      obtain ⟨hx,hy⟩ := ha w _ hn
      by_cases h : z.val.1 ≠ 0
      · simpa only [C,localValue,if_pos h,localThetaBound,vectorModulus,diagonalPoint,Nat.cast_ofNat] using! hx
      · simpa only [C,localValue,if_neg h,localThetaBound,vectorModulus,diagonalPoint,Nat.cast_ofNat] using! hy

end Datum
end MetaplecticPoisson
