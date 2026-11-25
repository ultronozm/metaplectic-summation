import MetaplecticSummation.BasicShears
import MetaplecticSummation.RayFourier

/-! The primitive layer of the explicit basic vector in §6. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain Filter Set
open scoped Topology
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (p : HeightOneSpectrum (𝓞 F))
local notation "v" => (Sum.inr p : Place F)
local notation "K" => LocalField F v
local notation "q" => (p.asIdeal.absNorm : ℝ)
private def shellRadius (k : ℕ) := (q^(n*k))⁻¹
private def shellValue (k : ℕ) := (p.asIdeal.absNorm : ℂ)^((n-1)*k)
private def basicWeight (r : ℝ) := ∑' k, if r = shellRadius (n := n) p k then shellValue (n := n) p k else 0
local notation "R" => shellRadius (n := n) p
local notation "W" => shellValue (n := n) p
local notation "w" => basicWeight (n := n) p

private def basicPhase (x : Kˣ) (y : K) : ℂ := if ‖y‖ ≤ ‖x.val‖ then 1 else if hy : y ≠ 0 then d.symbol v x (Units.mk0 y hy) else 0

private theorem basic_X_weight (x : Kˣ) (y : K) :
    (d.basicCharts p).1 x y = w (max ‖x.val‖ ‖y‖) * d.basicPhase p x y := by
  rfl

private theorem weighted_chart_lc {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
    (H : Lˣ → Lˣ → ℂ) (hsym : IsLocallyConstant (fun z : Lˣ × Lˣ => H z.1 z.2)) (V : ℝ → ℂ) :
    IsLocallyConstant (fun z : Lˣ × L => V (max ‖z.1.val‖ ‖z.2‖) *
      (if ‖z.2‖ ≤ ‖z.1.val‖ then 1 else if hy : z.2 ≠ 0 then H z.1 (Units.mk0 z.2 hy) else 0)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z
  have hx := continuous_fst.continuousAt.eventually (locallyConstant_norm_units.eventually_eq z.1)
  by_cases hz : z.2 = 0
  · have hy : ∀ᶠ a : Lˣ × L in 𝓝 z, ‖a.2‖ < ‖z.1.val‖ :=
      (continuous_norm.comp continuous_snd).continuousAt.eventually_lt continuousAt_const (by simp [hz])
    filter_upwards [hx,hy] with a ha hb
    change ‖a.1.val‖ = ‖z.1.val‖ at ha
    simp [ha,hb.le,hz]
  · have hcont := (liftUnit_continuousAt hz).comp (continuous_snd (X := Lˣ)).continuousAt
    have hnorm := hcont.eventually (locallyConstant_norm_units.eventually_eq (liftUnit z.2))
    have hs := (continuous_fst.continuousAt.prodMk hcont).eventually (hsym.eventually_eq (z.1,liftUnit z.2))
    filter_upwards [hx,hnorm,hs,continuous_snd.continuousAt.eventually (eventually_ne_nhds hz)] with a ha hb hs hn
    change ‖a.1.val‖ = ‖z.1.val‖ at ha
    change ‖(liftUnit a.2).val‖ = ‖(liftUnit z.2).val‖ at hb
    change H a.1 (liftUnit a.2) = H z.1 (liftUnit z.2) at hs
    change a.2 ≠ 0 at hn
    simp only [liftUnit_val hn,liftUnit_val hz] at hb
    simp only [liftUnit,dif_pos hn,dif_pos hz] at hs
    simp only [ha,hb,dif_pos hn,dif_pos hz,hs]

private theorem weighted_chart_locallyConstant (V : ℝ → ℂ) :
    IsLocallyConstant (fun z : Kˣ × K => V (max ‖z.1.val‖ ‖z.2‖) * d.basicPhase p z.1 z.2) := by
  letI := FinitePlace.nontriviallyNormedCompletion p
  exact weighted_chart_lc (L := p.adicCompletion F) (d.symbol v) ((d.locallyConstant_unitPairing v).comp Units.val) V

theorem basicCharts_locallyConstant :
    IsLocallyConstant (fun z : Kˣ × K => (d.basicCharts p).1 z.1 z.2) ∧
      IsLocallyConstant (fun z : K × Kˣ => (d.basicCharts p).2 z.1 z.2) := by
  have h : IsLocallyConstant (fun z : Kˣ × K => (d.basicCharts p).1 z.1 z.2) := d.weighted_chart_locallyConstant p w
  refine ⟨h,?_⟩
  have he : (fun z : K × Kˣ => (d.basicCharts p).2 z.1 z.2) =
      (fun z : Kˣ × K => (d.basicCharts p).1 z.1 z.2) ∘ Prod.swap :=
    funext fun z => d.basic_swap p z.2 z.1
  rw [he]
  exact h.comp_continuous continuous_swap

/-- The restriction of the basic vector to the primitive vectors of the local integers. -/
def primitiveCharts : Charts K :=
  (fun x y => if max ‖x.val‖ ‖y‖ = 1 then d.basicPhase p x y else 0,
    fun x y => if max ‖y.val‖ ‖x‖ = 1 then d.basicPhase p y x else 0)

private theorem weight_eq_one : w 1 = 1 := by
  have hq : 1 < q := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  have hzero (k : ℕ) (hk : k ≠ 0) : (1 : ℝ) ≠ R k :=
    ne_of_gt (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (Nat.mul_ne_zero (NeZero.ne n) hk)))
  rw [basicWeight,tsum_eq_single 0 (fun k hk => if_neg (hzero k hk))]
  simp [shellRadius,shellValue]

theorem primitive_test (hp : p.asIdeal.absNorm.Coprime n) : d.primitiveCharts p ∈ d.testSet v := by
  let V (r : ℝ) : ℂ := if r = 1 then 1 else 0
  have hX (x : Kˣ) (y : K) : (d.primitiveCharts p).1 x y =
      V (max ‖x.val‖ ‖y‖) * (d.basicCharts p).1 x y := by
    rw [d.basic_X_weight p x y]
    by_cases h : max ‖x.val‖ ‖y‖ = 1 <;> simp [V,primitiveCharts,h,weight_eq_one]
  have hY (x : K) (y : Kˣ) : (d.primitiveCharts p).2 x y =
      V (max ‖x‖ ‖y.val‖) * (d.basicCharts p).2 x y := by
    rw [d.basic_swap p y x,max_comm ‖x‖ ‖y.val‖]
    exact hX y x
  have hl := d.weighted_chart_locallyConstant p V
  have h₁ : IsLocallyConstant (fun z : Kˣ × K => (d.primitiveCharts p).1 z.1 z.2) := by
    simpa only [V,ite_mul,one_mul,zero_mul,primitiveCharts] using hl
  have h₂ : IsLocallyConstant (fun z : K × Kˣ => (d.primitiveCharts p).2 z.1 z.2) :=
    show IsLocallyConstant ((fun z : Kˣ × K => (d.primitiveCharts p).1 z.1 z.2) ∘ Prod.swap) from
      h₁.comp_continuous (continuous_swap (X := K) (Y := Kˣ))
  refine ⟨?_,?_⟩
  · intro x y
    rw [hX,hY,d.basicCharts_glues p hp x y,mul_left_comm]
  · letI : ProperSpace K := by
      letI := FinitePlace.nontriviallyNormedCompletion p
      exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (p.adicCompletion F)
    change finiteTest (d.primitiveCharts p)
    refine ⟨h₁,h₂,Metric.sphere (0 : K × K) 1,isCompact_sphere (0 : K × K) 1,by simp,?_⟩
    rintro ⟨x,y⟩ hout
    have h : max ‖x‖ ‖y‖ ≠ 1 := fun he => hout (by simpa [Metric.mem_sphere,Prod.norm_def] using he)
    constructor
    · by_cases hx : x ≠ 0 <;> simp [xChart,primitiveCharts,hx,h]
    · by_cases hy : y ≠ 0 <;> simp [yChart,primitiveCharts,hy,max_comm ‖y‖ ‖x‖,h]

private theorem weight_recursion (r : ℝ) :
    w r - (p.asIdeal.absNorm : ℂ)^(n-1) * w (q^n*r) = if r = 1 then 1 else 0 := by
  let Q : ℂ := (p.asIdeal.absNorm : ℂ)^(n-1)
  let term (k : ℕ) : ℂ := if r = R k then W k else 0
  have hq : 1 < q := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  have hq₀ := (zero_lt_one.trans hq).ne'
  have hanti : StrictAnti R := by
    intro i j h
    exact (inv_lt_inv₀ (pow_pos (zero_lt_one.trans hq) _) (pow_pos (zero_lt_one.trans hq) _)).mpr
      (pow_lt_pow_right₀ hq (Nat.mul_lt_mul_of_pos_left h (NeZero.pos n)))
  have ht : Summable term := by
    by_cases h : ∃ k, r = R k
    · obtain ⟨k,hk⟩ := h
      exact summable_of_ne_finset_zero (s := {k}) (fun j hj => if_neg
        (fun h => hj (Finset.mem_singleton.mpr (hanti.injective (h.symm.trans hk)))))
    · exact summable_of_ne_finset_zero (s := ∅) (fun j _ => if_neg (not_exists.mp h j))
  have hr (k : ℕ) : q^n*r = R k ↔ r = R (k+1) := by
    rw [shellRadius,shellRadius,Nat.mul_succ,pow_add,mul_inv_rev]
    constructor <;> intro h <;> field_simp at h ⊢ <;> linear_combination h
  have hs (k : ℕ) : Q * (if q^n*r = R k then W k else 0) = term (k+1) := by
    simp only [term,if_congr (hr k) rfl rfl,mul_ite,mul_zero]
    congr 1
    rw [show W (k+1) = W k * Q by simp only [Q,shellValue,Nat.mul_succ,pow_add],mul_comm]
  change (∑' k, term k) - Q * (∑' k, if q^n*r = R k then W k else 0) = _
  rw [← tsum_mul_left]
  simp_rw [hs]
  rw [← ht.sum_add_tsum_nat_add 1,Finset.sum_range_one,add_sub_cancel_right]
  simp [term,shellRadius,shellValue]

private theorem phase_dilate (a x : Kˣ) (y : K) : d.basicPhase p (a^n*x) (a.val^n*y) = d.basicPhase p x y := by
  let H := d.unitPairing v
  have ht (r s : Kˣ) : (H r s)^n = 1 := d.unitPairing_pow _ _ _
  have he : ‖a.val^n*y‖ ≤ ‖(a^n*x).val‖ ↔ ‖y‖ ≤ ‖x.val‖ := by
    simp only [Units.val_mul,Units.val_pow_eq_pow_val,norm_mul,norm_pow,mul_le_mul_iff_right₀ (pow_pos (norm_pos_iff.mpr a.ne_zero) n)]
  unfold basicPhase
  rw [if_congr he rfl rfl]
  by_cases h : ‖y‖ ≤ ‖x.val‖
  · simp [h]
  · have hy : y ≠ 0 := by rintro rfl; exact h (by simp)
    let Y := Units.mk0 y hy
    have hay := mul_ne_zero (pow_ne_zero n a.ne_zero) hy
    rw [if_neg h,dif_pos hay,dif_pos hy,show Units.mk0 (a.val^n*y) hay = a^n*Y from Units.ext rfl]
    rw [if_neg h]
    change (H (a^n*x) (a^n*Y)).val = (H x Y).val
    simp only [map_mul,map_pow,MonoidHom.mul_apply,MonoidHom.pow_apply,ht,one_mul]

/-- Equation (6.1): removal of the dilated interior leaves precisely the primitive layer. -/
theorem primitive_eq_basic_sub_dilate (π : Kˣ) (hπ : ‖π.val‖ = q⁻¹) :
    d.primitiveCharts p = d.basicCharts p - (p.asIdeal.absNorm : ℂ)^(n-1) •
      dilateCharts (π⁻¹^n) (d.basicCharts p) := by
  have hx (x : Kˣ) (y : K) : (d.primitiveCharts p).1 x y =
      (d.basicCharts p).1 x y - (p.asIdeal.absNorm : ℂ)^(n-1) *
        (d.basicCharts p).1 (π⁻¹^n*x) (π⁻¹.val^n*y) := by
    rw [d.basic_X_weight p x y,d.basic_X_weight p (π⁻¹^n*x),d.phase_dilate]
    simp only [Units.val_mul,Units.val_pow_eq_pow_val,Units.val_inv_eq_inv_val,norm_mul,norm_pow,norm_inv,hπ,inv_inv]
    rw [← mul_max_of_nonneg _ _ (pow_nonneg (Nat.cast_nonneg _) _),← mul_assoc,← sub_mul,weight_recursion]
    simp only [primitiveCharts,ite_mul,one_mul,zero_mul]
  apply Prod.ext
  · exact funext fun x => funext (hx x)
  · funext x y
    change (d.primitiveCharts p).1 y x = (d.basicCharts p).2 x y -
      _ * (d.basicCharts p).2 (π⁻¹.val^n*x) (π⁻¹^n*y)
    simp only [d.basic_swap]
    exact hx y x

end MetaplecticPoisson.Datum
