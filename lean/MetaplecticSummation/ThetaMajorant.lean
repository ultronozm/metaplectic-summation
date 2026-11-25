import MetaplecticSummation.ThetaEstimate

/-! The theta bound of Lemma B.1, including the idele norm and the singularity at zero. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField Filter
open Classical
variable {F : Type} [Field F] [NumberField F]

theorem vectorModulus_pos (v : Place F) (z : RationalPoint F) : 0 < vectorModulus v z := by
  have hn (x : F) (h : x ≠ 0) : 0 < modulus F v (diagonal F v x) := by
    have he := (map_ne_zero (diagonal F v)).mpr h
    cases v with
    | inl w => exact pow_pos (norm_pos_iff.mpr he) _
    | inr p => exact norm_pos_iff.mpr he
  by_cases h : z.val.1 = 0
  · exact (hn _ (fun hy => z.property (Prod.ext h hy))).trans_le (le_max_right ..)
  · exact (hn _ h).trans_le (le_max_left ..)

theorem vectorModulus_cofinite (z : RationalPoint F) : ∀ᶠ v in cofinite, vectorModulus v z = 1 := by
  apply eventually_place_of_finite
  by_cases h : z.val.1 = 0
  · have hy : z.val.2 ≠ 0 := fun e => z.property (Prod.ext h e)
    filter_upwards [eventually_diagonal_norm_one hy] with p hp
    simp [vectorModulus,modulus,h,hp]
  · filter_upwards [eventually_diagonal_norm_one h,eventually_diagonal_integral z.val.2] with p hp hp'
    simp only [vectorModulus,modulus,hp,max_eq_left hp']

private theorem norm_product_ge_one (z : RationalPoint F) : 1 ≤ ∏ᶠ v, vectorModulus v z := by
  by_cases h : z.val.1 = 0
  · exact one_le_box_volume _ (vectorModulus_cofinite z) (fun e => z.property (Prod.ext h e)) (fun v => le_max_right ..)
  · exact one_le_box_volume _ (vectorModulus_cofinite z) h (fun v => le_max_left ..)

private theorem finprod_pos_real {ι : Type*} {f : ι → ℝ} (hf : ∀ᶠ i in cofinite, f i = 1)
    (h : ∀ i, 0 < f i) : 0 < ∏ᶠ i, f i := by
  have H := eventually_cofinite.mp hf
  rw [finprod_eq_prod_of_mulSupport_toFinset_subset f H (Finset.Subset.refl _)]
  exact Finset.prod_pos (fun i _ => h i)

private theorem finprod_rpow {ι : Type*} {f : ι → ℝ} (hf : ∀ᶠ i in cofinite, f i = 1)
    (h : ∀ i, 0 ≤ f i) (t : ℝ) : ∏ᶠ i, (f i)^t = (∏ᶠ i, f i)^t := by
  have H : Function.HasFiniteMulSupport f := eventually_cofinite.mp hf
  rw [finprod_eq_prod_of_mulSupport_subset (fun i => f i ^ t) (s := H.toFinset) (by
    intro i hi
    exact H.mem_toFinset.mpr (fun he => hi (by simp [he]))),
    finprod_eq_prod_of_mulSupport_toFinset_subset f H (Finset.Subset.refl _)]
  exact Real.finsetProd_rpow _ f (fun i _ => h i) t

/-- The local factor β at decay order four in (B.1). The argument s is the
normalized maximum of the two coordinates after idele scaling. -/
def localThetaBound (κ : ℝ) (v : Place F) (C s : ℝ) : ℝ :=
  match v with
  | .inl _ => C * min (s^(-κ)) (s^(-4 : ℝ))
  | .inr _ => if s ≤ C then C * s^(-κ) else 0

def thetaMajorant (κ : ℝ) (C a : Place F → ℝ) (z : RationalPoint F) : ℝ :=
  ∏ᶠ v, localThetaBound κ v (C v) (a v*vectorModulus v z)

private theorem arch_decay {κ s : ℝ} (hk : κ ≤ 1) (hs : 0 < s) :
    min (s^(-κ)) (s^(-4:ℝ)) ≤ s^(-κ) * (max 1 s)⁻¹^3 := by
  rcases le_total s 1 with h | h
  · simpa only [max_eq_left h,inv_one,one_pow,mul_one] using min_le_left (s^(-κ)) (s^(-4:ℝ))
  · rw [max_eq_right h,inv_pow,← Real.rpow_natCast,← Real.rpow_neg hs.le,← Real.rpow_add hs]
    exact (min_le_right ..).trans (Real.rpow_le_rpow_of_exponent_le h (by push_cast; linarith))

private def archDecay (s : Place F → ℝ) : Place F → ℝ
  | .inl w => (max 1 (s (.inl w)))⁻¹^3
  | .inr _ => 1

private theorem archDecay_prod (s : Place F → ℝ) :
    ∏ᶠ v, archDecay s v = ∏ w : InfinitePlace F, (max 1 (s (.inl w)))⁻¹^3 := by
  let e : InfinitePlace F ↪ Place F := Function.Embedding.inl
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := Finset.univ.map e) (by
    rintro (w|p) hw
    · exact Finset.mem_map.mpr ⟨w,Finset.mem_univ _,rfl⟩
    · exact (hw rfl).elim),Finset.prod_map]
  rfl

private def cutoff (C : Place F → ℝ) : Place F → ℝ
  | .inl _ => 1
  | .inr p => C (.inr p)

theorem localThetaBound_cofinite (κ : ℝ) {C a : Place F → ℝ}
    (hC : ∀ᶠ v in cofinite, C v = 1) (ha : ∀ᶠ v in cofinite, a v = 1) (z : RationalPoint F) :
    ∀ᶠ v in cofinite, localThetaBound κ v (C v) (a v*vectorModulus v z) = 1 := by
  filter_upwards [hC,ha,vectorModulus_cofinite z] with v hc ha hz
  cases v <;> simp [hc,ha,hz,localThetaBound]

omit [NumberField F] in
theorem localThetaBound_nonneg (κ : ℝ) (v : Place F) {C s : ℝ} (hc : 0 ≤ C) (hs : 0 < s) :
    0 ≤ localThetaBound κ v C s := by
  cases v with
  | inl _ => exact mul_nonneg hc (le_min (Real.rpow_nonneg hs.le _) (Real.rpow_nonneg hs.le _))
  | inr _ =>
    change 0 ≤ if s ≤ C then C*s^(-κ) else 0
    split
    · exact mul_nonneg hc (Real.rpow_nonneg hs.le _)
    · exact le_rfl

/-- Equation (B.2) after absorbing the finite cutoff constants into the box radii. -/
private theorem thetaMajorant_le {κ : ℝ} (hκ : 0 ≤ κ) (hk : κ ≤ 1) (C a : Place F → ℝ)
    (hC : ∀ v, 0 ≤ C v) (hc : ∀ᶠ v in cofinite, C v = 1)
    (ha : ∀ v, 0 < a v) (h₁ : ∀ᶠ v in cofinite, a v = 1) (z : RationalPoint F) :
    thetaMajorant κ C a z ≤ ((∏ᶠ v, C v)*(∏ᶠ v, a v)^(-κ)) * boxWeight (fun v => cutoff C v/a v) z := by
  let s (v : Place F) := a v*vectorModulus v z
  have hs (v) : 0 < s v := mul_pos (ha v) (vectorModulus_pos _ _)
  have hs' : ∀ᶠ v in cofinite, s v = 1 := by
    filter_upwards [h₁,vectorModulus_cofinite z] with v h h'; simp [s,h,h']
  have hr : ∀ᶠ v in cofinite, (s v)^(-κ) = 1 := hs'.mono fun v h => by simp [h]
  have hf := localThetaBound_cofinite κ hc h₁ z
  let r v := cutoff C v/a v
  by_cases hg : ∀ p : Prime F, vectorModulus (.inr p) z ≤ r (.inr p)
  · have hd : ∀ᶠ v in cofinite, archDecay s v = 1 := eventually_place_of_finite (.of_forall fun _ => rfl)
    have H : ∀ᶠ v in cofinite, C v*(s v)^(-κ) = 1 := by filter_upwards [hc,hr] with v h h'; rw [h,h',mul_one]
    have H' : ∀ᶠ v in cofinite, C v*(s v)^(-κ)*archDecay s v = 1 := by filter_upwards [H,hd] with v h h'; rw [h,h',mul_one]
    have hloc (v) : localThetaBound κ v (C v) (s v) ≤ C v*(s v)^(-κ)*archDecay s v := by
      cases v with
      | inr p =>
        have h : s (.inr p) ≤ C (.inr p) :=
          (mul_comm (a (.inr p)) _).trans_le ((le_div_iff₀ (ha _)).mp (hg p))
        simp [archDecay,localThetaBound,h]
      | inl w => simpa only [localThetaBound,archDecay,mul_assoc] using
          mul_le_mul_of_nonneg_left (arch_decay hk (hs (.inl w))) (hC (.inl w))
    have h := finprod_mono_real hf H' (fun v => localThetaBound_nonneg _ _ (hC _) (hs _)) hloc
    rw [finprod_mul_distrib (eventually_cofinite.mp H) (eventually_cofinite.mp hd),
      finprod_mul_distrib (eventually_cofinite.mp hc) (eventually_cofinite.mp hr),
      finprod_rpow hs' (fun v => (hs v).le)] at h
    have hmax : ∏ᶠ v, a v ≤ ∏ᶠ v, s v := by
      rw [show (∏ᶠ v, s v) = _ from finprod_mul_distrib (eventually_cofinite.mp h₁) (eventually_cofinite.mp (vectorModulus_cofinite z))]
      exact le_mul_of_one_le_right (finprod_pos_real h₁ ha).le (norm_product_ge_one z)
    have hdec : (∏ᶠ v, archDecay s v) = boxWeight r z := by
      rw [archDecay_prod,boxWeight,if_pos hg]
      apply Finset.prod_congr rfl
      intro w _
      simp [r,cutoff,s,mul_comm]
    have hCprod : 0 ≤ ∏ᶠ v, C v := by classical exact finprod_nonneg hC
    have hdec₀ : 0 ≤ ∏ᶠ v, archDecay s v := by
      rw [archDecay_prod]
      exact Finset.prod_nonneg (fun w _ => pow_nonneg (inv_nonneg.mpr (zero_le_one.trans (le_max_left ..))) _)
    rw [← hdec]
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (finprod_pos_real h₁ ha) hmax (neg_nonpos.mpr hκ)) hCprod) hdec₀)
  · obtain ⟨p,hp⟩ := not_forall.mp hg
    have ht : ¬ s (.inr p) ≤ C (.inr p) := fun h => hp ((le_div_iff₀ (ha _)).mpr ((mul_comm ..).trans_le h))
    rw [thetaMajorant,finprod_eq_zero _ (.inr p) (if_neg ht) (eventually_cofinite.mp hf),boxWeight,if_neg hg,mul_zero]

/-- Lemma B.1 for the normalized moduli a of an idele. The bound is uniform
in a and its exponent is −2−κ. -/
theorem theta_majorant_bound {κ : ℝ} (hκ : 0 ≤ κ) (hk : κ ≤ 1) (C : Place F → ℝ)
    (hC : ∀ v, 0 ≤ C v) (hfin : ∀ p : Prime F, 1 ≤ C (.inr p)) (hc : ∀ᶠ v in cofinite, C v = 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : Place F → ℝ, (∀ v, 0 < a v) → (∀ᶠ v in cofinite, a v = 1) →
      Summable (thetaMajorant κ C a) ∧ (∑' z, thetaMajorant κ C a z) ≤ M*(∏ᶠ v, a v)^(-2-κ) := by
  obtain ⟨B,hB,hbox⟩ := theta_box_estimate (F := F)
  let V := ∏ᶠ v, C v
  let U := ∏ᶠ v, cutoff C v
  have hcut (v) : 0 < cutoff C v := by
    cases v with
    | inl w => exact zero_lt_one
    | inr p => exact zero_lt_one.trans_le (hfin p)
  have hcf : ∀ᶠ v in cofinite, cutoff C v = 1 := hc.mono (fun v h => by cases v <;> simp [cutoff,h])
  have hV : 0 ≤ V := finprod_nonneg hC
  refine ⟨V*B*U^2,by positivity,?_⟩
  intro a ha h₁
  let A := ∏ᶠ v, a v
  let r (v : Place F) := cutoff C v/a v
  have hA := finprod_pos_real h₁ ha
  have hr : ∀ᶠ v in cofinite, r v = 1 := by filter_upwards [hcf,h₁] with v h h'; simp [r,h,h']
  obtain ⟨hs,hb⟩ := hbox r (fun v => div_pos (hcut _) (ha _)) hr
  have hR : (∏ᶠ v, r v) = U/A := finprod_div_distrib (eventually_cofinite.mp hcf) (eventually_cofinite.mp h₁)
  have hnonneg (z : RationalPoint F) : 0 ≤ thetaMajorant κ C a z :=
    finprod_nonneg fun v => localThetaBound_nonneg _ _ (hC _) (mul_pos (ha _) (vectorModulus_pos _ _))
  have hle := thetaMajorant_le hκ hk C a hC hc ha h₁
  have hS := hs.mul_left (V*A^(-κ))
  have h := Summable.of_nonneg_of_le hnonneg hle hS
  refine ⟨h,?_⟩
  apply (h.tsum_le_tsum hle hS).trans
  rw [tsum_mul_left]
  have hscale : 0 ≤ V*A^(-κ) := mul_nonneg hV (Real.rpow_nonneg hA.le _)
  apply (mul_le_mul_of_nonneg_left hb hscale).trans_eq
  rw [hR]
  change V*A^(-κ)*(B*(U/A)^2) = V*B*U^2*A^(-2-κ)
  have eqn : A^(-2-κ) = (A^2)⁻¹*A^(-κ) := by
    rw [sub_eq_add_neg,Real.rpow_add hA,Real.rpow_neg hA.le 2,Real.rpow_two]
  rw [eqn,div_pow,div_eq_mul_inv]
  ring

/-- The family of normalized local absolute values of an idele. -/
def ideleModulus (a : (Adeles F)ˣ) (v : Place F) : ℝ := modulus F v (component a.val v)

/-- Lemma B.1, with the uniform bound quantified over the idele group. -/
theorem theta_idele_bound {κ : ℝ} (hκ : 0 ≤ κ) (hk : κ ≤ 1) (C : Place F → ℝ)
    (hC : ∀ v, 0 ≤ C v) (hfin : ∀ p : Prime F, 1 ≤ C (.inr p)) (hc : ∀ᶠ v in cofinite, C v = 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : (Adeles F)ˣ, Summable (thetaMajorant κ C (ideleModulus a)) ∧
      (∑' z, thetaMajorant κ C (ideleModulus a) z) ≤ M*(∏ᶠ v, ideleModulus a v)^(-2-κ) := by
  obtain ⟨M,hM,h⟩ := theta_majorant_bound hκ hk C hC hfin hc
  refine ⟨M,hM,fun a => h _ (fun v => ?_) (eventually_place_of_finite (eventually_unit_component a))⟩
  have hu := (Units.map (componentHom v).toMonoidHom a).ne_zero
  cases v with
  | inl w => exact pow_pos (norm_pos_iff.mpr hu) _
  | inr p => exact norm_pos_iff.mpr hu

end MetaplecticPoisson.Datum
