import GlobalBridge

noncomputable section
open NumberField IsDedekindDomain MetaplecticPoisson Set Filter
open scoped Topology Classical
namespace MetaplecticBridge

variable {F : Type} [Field F] [NumberField F] (n : ℕ+) (w : InfinitePlace F)
local notation "K" => LocalField F (Sum.inl w)

private def signPair (a b : ℝ) : F := if a < 0 ∧ b < 0 then -1 else 1

private theorem signPair_symm (a b : ℝ) : signPair (F := F) a b = signPair b a := by
  simp only [signPair,and_comm]

private theorem signPair_mul (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    signPair (F := F) (a*b) c = signPair a c * signPair b c := by
  by_cases hc : c < 0
  · rcases lt_or_gt_of_ne ha with ha|ha <;> rcases lt_or_gt_of_ne hb with hb|hb <;>
      simp [signPair,hc,ha,hb,mul_neg_iff, not_lt_of_gt, *]
  · simp [signPair,hc]

private theorem infiniteValue_coe (a b : Kˣ) :
    ((infiniteValue n w a b).val : F) = if (n : ℕ) = 2 then
      if hw : w.IsReal then signPair
        (InfinitePlace.Completion.ringEquivRealOfIsReal hw a.val)
        (InfinitePlace.Completion.ringEquivRealOfIsReal hw b.val) else 1
      else 1 := by
  classical
  unfold infiniteValue
  split_ifs <;> simp_all [signPair]

theorem infiniteValue_mul_left (a b c : Kˣ) :
    infiniteValue n w (a*b) c = infiniteValue n w a c * infiniteValue n w b c := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul,Units.val_mul,infiniteValue_coe]
  split_ifs <;> try simp
  rename_i hn hw
  rw [show (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (a.val*b.val) = _ from map_mul (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (a.val : w.Completion) b.val]
  exact signPair_mul _ _ _ ((map_ne_zero _).mpr a.ne_zero) ((map_ne_zero _).mpr b.ne_zero)

theorem infiniteValue_symm (a b : Kˣ) : infiniteValue n w a b = infiniteValue n w b a := by
  apply Subtype.ext
  apply Units.ext
  simp only [infiniteValue_coe]
  split_ifs <;> first | rfl | apply signPair_symm

theorem infiniteValue_skew (a b : Kˣ) : infiniteValue n w a b * infiniteValue n w b a = 1 := by
  rw [infiniteValue_symm n w b a]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul,Units.val_mul,infiniteValue_coe,Subgroup.coe_one,Units.val_one,signPair]
  split_ifs <;> simp

theorem infiniteValue_neg_self (a : Kˣ) : infiniteValue n w a (-a) = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp only [infiniteValue_coe,Subgroup.coe_one,Units.val_one,signPair,Units.val_neg,map_neg]
  split_ifs <;> first | rfl | exfalso; obtain ⟨h,h'⟩ := ‹_ ∧ _›; rw [show (InfinitePlace.Completion.ringEquivRealOfIsReal _) (-a.val) = _ from map_neg (InfinitePlace.Completion.ringEquivRealOfIsReal _) (a.val : w.Completion)] at h'; exact (not_lt_of_ge (neg_nonneg.mpr h.le)) h'

private theorem negative_locallyConstant (hw : w.IsReal) :
    IsLocallyConstant (fun a : Kˣ => decide (InfinitePlace.Completion.ringEquivRealOfIsReal hw a.val < 0)) := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have he : Continuous (fun a : Kˣ => e a.val) :=
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous.comp Units.continuous_val
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro a
  have hne : e a.val ≠ 0 := (map_ne_zero _).mpr a.ne_zero
  rcases lt_or_gt_of_ne hne with ha|ha
  · filter_upwards [he.continuousAt.eventually (gt_mem_nhds ha)] with b hb
    exact (decide_eq_true hb).trans (decide_eq_true ha).symm
  · filter_upwards [he.continuousAt.eventually (lt_mem_nhds ha)] with b hb
    exact (decide_eq_false hb.not_gt).trans (decide_eq_false ha.not_gt).symm

theorem infiniteValue_continuous :
    Continuous (fun z : Kˣ × Kˣ => diagonal F (.inl w) ((infiniteValue n w z.1 z.2).val : F)) := by
  classical
  apply IsLocallyConstant.continuous
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro z
  by_cases hn : (n : ℕ) = 2
  · by_cases hw : w.IsReal
    · have h := negative_locallyConstant w hw
      filter_upwards [continuous_fst.continuousAt.eventually (h.eventually_eq z.1),
        continuous_snd.continuousAt.eventually (h.eventually_eq z.2)] with y hy hy'
      simp only [infiniteValue_coe,if_pos hn,dif_pos hw,signPair]
      exact congrArg (diagonal F (.inl w)) (if_congr (and_congr (decide_eq_decide.mp hy) (decide_eq_decide.mp hy')) rfl rfl)
    · simp [infiniteValue_coe,hn,hw]
  · simp [infiniteValue_coe,hn]

end MetaplecticBridge
