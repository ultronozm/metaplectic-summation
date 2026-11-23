import MetaplecticSummation.ThetaMajorant
import MetaplecticSummation.Schwartz.ChartGrowth

/-! The local growth bounds for the theta estimate. -/
noncomputable section
namespace MetaplecticPoisson
open NumberField IsDedekindDomain Filter Set
open Classical

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
