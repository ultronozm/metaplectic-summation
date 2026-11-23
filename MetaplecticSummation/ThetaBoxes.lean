import MetaplecticSummation.RationalEvaluation

/-! Counting rational points in adelic boxes for the theta estimate in Lemma B.1. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField IsDedekindDomain Set MeasureTheory Filter
open scoped Pointwise
open Classical
variable {F : Type} [Field F] [NumberField F]
local notation "K" p => HeightOneSpectrum.adicCompletion F p

private theorem local_packing (p : HeightOneSpectrum (𝓞 F)) {J : Type*} [Fintype J]
    (x : J → K p) (a b : (K p)ˣ) (hab : ‖a.val‖ ≤ ‖b.val‖)
    (hB : ∀ i, ‖x i‖ ≤ ‖b.val‖) (hsep : ∀ i j, i ≠ j → ‖a.val‖ < ‖x i-x j‖) :
    (Fintype.card J : ℝ) * ‖a.val‖ ≤ ‖b.val‖ := by
  letI := borel (K p)
  letI : BorelSpace (K p) := ⟨rfl⟩
  let μ := (MeasureTheory.Measure.addHaar : Measure (K p))
  let O : Set (K p) := p.adicCompletionIntegers F
  have ho : IsOpen O := FinitePlace.isOpen_adicCompletionIntegers p
  have hc : IsCompact O := FinitePlace.isCompact_adicCompletionIntegers p
  have hm (u : K p) : u ∈ O ↔ ‖u‖ ≤ 1 := mem_localIntegers_iff p u
  have hball (t : (K p)ˣ) (u : K p) : u ∈ t • O ↔ ‖u‖ ≤ ‖t.val‖ := by
    rw [mem_smul_set_iff_inv_smul_mem,hm,Units.smul_def,smul_eq_mul,Units.val_inv_eq_inv_val,
      ← div_eq_inv_mul,norm_div,div_le_one (norm_pos_iff.mpr t.ne_zero)]
  have vol (t : (K p)ˣ) : μ.real (t • O) = ‖t.val‖ * μ.real O := by
    rw [measureReal_def,← distribHaarChar_mul,FinitePlace.haarChar_eq_nnnorm,ENNReal.toReal_mul]
    rfl
  have pos : 0 < μ.real O := ENNReal.toReal_pos (ho.measure_pos μ ⟨0,(hm 0).mpr (by simp)⟩).ne' hc.measure_ne_top
  let balls (i : J) := x i +ᵥ (a • O)
  have hd : Pairwise (Function.onFun Disjoint balls) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨u,hu,rfl⟩ ⟨v,hv,he⟩
    change x j + v = x i + u at he
    have he' : x i - x j = v - u := by linear_combination -he
    have h : ‖v-u‖ ≤ max ‖v‖ ‖u‖ := by
      simpa only [sub_eq_add_neg,norm_neg] using IsUltrametricDist.norm_add_le_max v (-u)
    exact (hsep i j hij).not_ge (he' ▸ h.trans (max_le ((hball a v).mp hv) ((hball a u).mp hu)))
  have hsub : (⋃ i, balls i) ⊆ b • O := by
    rintro z hz
    obtain ⟨i,u,hu,rfl⟩ := Set.mem_iUnion.mp hz
    exact (hball _ _).mpr <| (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (hB i) (((hball a u).mp hu).trans hab))
  have h := measureReal_mono (μ := μ) hsub (hc.smul b).measure_ne_top
  rw [measureReal_iUnion_fintype hd (fun i => ((ho.smul a).vadd (x i)).measurableSet)
      (fun i => ((hc.smul a).vadd (x i)).measure_ne_top)] at h
  have hvol (i : J) : μ.real (balls i) = ‖a.val‖ * μ.real O := by
    simpa only [balls,measureReal_def,measure_vadd] using vol a
  simp only [hvol,vol,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_assoc] at h
  exact (mul_le_mul_iff_left₀ pos).mp h

theorem finprod_mono_real {ι : Type*} {a b : ι → ℝ}
    (ha : ∀ᶠ i in cofinite, a i = 1) (hb : ∀ᶠ i in cofinite, b i = 1)
    (h₀ : ∀ i, 0 ≤ a i) (hle : ∀ i, a i ≤ b i) : ∏ᶠ i, a i ≤ ∏ᶠ i, b i := by
  have A : Function.HasFiniteMulSupport a := eventually_cofinite.mp ha
  have B : Function.HasFiniteMulSupport b := eventually_cofinite.mp hb
  rw [finprod_eq_prod_of_mulSupport_toFinset_subset a A (Finset.subset_union_left (s₂ := B.toFinset)),
    finprod_eq_prod_of_mulSupport_toFinset_subset b B (Finset.subset_union_right (s₁ := A.toFinset))]
  exact Finset.prod_le_prod₀ (fun i _ => h₀ i) (fun i _ => hle i)

theorem modulus_eventually_one {x : F} (hx : x ≠ 0) :
    ∀ᶠ v in cofinite, modulus F v (diagonal F v x) = 1 :=
  eventually_place_of_finite (eventually_diagonal_norm_one hx)

private theorem modulus_nonneg (v : Place F) (x : LocalField F v) : 0 ≤ modulus F v x := by
  cases v <;> simp [modulus]

/-- If the product of the radii is less than one, the box contains no
nonzero field element. -/
theorem one_le_box_volume (r : Place F → ℝ) (hr : ∀ᶠ v in cofinite, r v = 1)
    {x : F} (hx : x ≠ 0) (hbox : ∀ v, modulus F v (diagonal F v x) ≤ r v) :
    1 ≤ ∏ᶠ v, r v := by
  rw [← diagonal_modulus_product hx]
  exact finprod_mono_real (modulus_eventually_one hx) hr (fun _ => modulus_nonneg _ _) hbox

private def archFactor : Place F → ℝ
  | .inl w => 2^w.mult
  | .inr _ => 1

private theorem archFactor_cofinite : ∀ᶠ v : Place F in cofinite, archFactor v = 1 :=
  eventually_place_of_finite (.of_forall fun _ => rfl)

omit [NumberField F] in
private theorem archFactor_ge_one (v : Place F) : 1 ≤ archFactor v := by
  cases v with
  | inl w => exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  | inr _ => exact le_rfl

private theorem modulus_sub_le (v : Place F) (x y : LocalField F v) (r : ℝ)
    (hx : modulus F v x ≤ r) (hy : modulus F v y ≤ r) :
    modulus F v (x-y) ≤ archFactor v * r := by
  cases v with
  | inl w =>
    change ‖x-y‖^w.mult ≤ 2^w.mult*r
    have h := (norm_sub_le x y).trans (add_le_add (le_max_left ‖x‖ ‖y‖) (le_max_right ‖x‖ ‖y‖))
    rw [← two_mul] at h
    apply (pow_le_pow_left₀ (norm_nonneg _) h _).trans
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (by rcases max_choice ‖x‖ ‖y‖ with h | h <;> rwa [h]) (by positivity)
  | inr p =>
    letI : IsUltrametricDist (LocalField F (.inr p)) := inferInstanceAs (IsUltrametricDist (p.adicCompletion F))
    change ‖x‖ ≤ r at hx
    change ‖y‖ ≤ r at hy
    change ‖x-y‖ ≤ 1*r
    rw [one_mul,sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max (x : p.adicCompletion F) (-y)).trans (max_le hx (by simpa using hy))

private theorem box_separation (r : Place F → ℝ) (hr : ∀ᶠ v in cofinite, r v = 1)
    (hp : ∀ v, 0 < r v) (p : HeightOneSpectrum (𝓞 F)) {x y : F} (hxy : x ≠ y)
    (hx : ∀ v, modulus F v (diagonal F v x) ≤ r v) (hy : ∀ v, modulus F v (diagonal F v y) ≤ r v) :
    1 ≤ ((∏ᶠ v : Place F, archFactor v) * ∏ᶠ v, r v) *
      (‖diagonal F (.inr p) x - diagonal F (.inr p) y‖ / r (.inr p)) := by
  let w : Place F := .inr p
  let t := ‖diagonal F w x - diagonal F w y‖ / r w
  let c (v : Place F) := if v = w then t else 1
  have h₁ := archFactor_cofinite (F := F)
  have hc : ∀ᶠ v in cofinite, c v = 1 := (eventually_cofinite_ne w).mono fun v h => if_neg h
  have ha : ∀ᶠ v in cofinite, archFactor v * r v = 1 := by filter_upwards [h₁,hr] with v h h'; rw [h,h',mul_one]
  have ht : ∀ᶠ v in cofinite, archFactor v * r v * c v = 1 := by filter_upwards [ha,hc] with v h h'; rw [h,h',mul_one]
  have h := one_le_box_volume (fun v => archFactor v*r v*c v) ht (sub_ne_zero.mpr hxy) (by
    intro v
    rw [map_sub]
    by_cases he : v = w
    · subst v
      change _ ≤ 1*r w*(if w = w then t else 1)
      rw [if_pos rfl,one_mul]
      change ‖diagonal F w x-diagonal F w y‖ ≤ r w * (‖diagonal F w x-diagonal F w y‖/r w)
      rw [mul_comm,div_mul_cancel₀ _ (hp w).ne']
    · rw [show c v = 1 from if_neg he,mul_one]
      exact modulus_sub_le v _ _ _ (hx v) (hy v))
  have hc' : ∏ᶠ v, c v = t := by
    rw [finprod_eq_prod_of_mulSupport_subset c (s := {w}) (fun v hv => by
      by_contra hn
      exact hv (if_neg (by simpa using hn)))]
    simp [c]
  rwa [finprod_mul_distrib (eventually_cofinite.mp ha) (eventually_cofinite.mp hc),
    finprod_mul_distrib (eventually_cofinite.mp h₁) (eventually_cofinite.mp hr),hc'] at h

private theorem bracket_norm (p : HeightOneSpectrum (𝓞 F)) {r : ℝ} (hr : 0 < r) :
    ∃ a b : (K p)ˣ, ‖a.val‖ < r ∧ r ≤ ‖b.val‖ ∧ ‖b.val‖ = (p.asIdeal.absNorm : ℝ) * ‖a.val‖ := by
  let q : ℝ := p.asIdeal.absNorm
  have hq : 1 < q := by dsimp [q]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  obtain ⟨k,hk,hk'⟩ := exists_mem_Ioc_zpow hr hq
  obtain ⟨π,hπ⟩ : ∃ π : (K p)ˣ, ‖π.val‖ = q⁻¹ := FinitePlace.exists_norm_uniformizer p
  have h (j : ℤ) : ‖(π⁻¹^j).val‖ = q^j := by simp [Units.val_zpow_eq_zpow_val,Units.val_inv_eq_inv_val,hπ]
  refine ⟨π⁻¹^k,π⁻¹^(k+1),h k ▸ hk,h (k+1) ▸ hk',?_⟩
  rw [h,h,zpow_add_one₀ (zero_lt_one.trans hq).ne',mul_comm]

/-- The number of nonzero field elements in a box of radii r is bounded by a
field-dependent constant times the product of the radii (Lemma B.1). -/
theorem rational_box_count : ∃ C : ℝ, 0 < C ∧ ∀ (r : Place F → ℝ),
    (∀ v, 0 < r v) → (∀ᶠ v in cofinite, r v = 1) →
    ∀ S : Finset F, (∀ x ∈ S, x ≠ 0 ∧ ∀ v, modulus F v (diagonal F v x) ≤ r v) →
      (S.card : ℝ) ≤ C * ∏ᶠ v, r v := by
  obtain ⟨I,hI,hi⟩ := Ring.not_isField_iff_exists_prime.mp (NumberField.RingOfIntegers.not_isField F)
  let p : HeightOneSpectrum (𝓞 F) := ⟨I,hi,hI⟩
  let w : Place F := .inr p
  let q : ℝ := p.asIdeal.absNorm
  let H := ∏ᶠ v : Place F, archFactor v
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm p)
  have hH : 1 ≤ H := by
    have h := finprod_mono_real (b := (archFactor : Place F → ℝ)) (.of_forall fun _ => rfl) archFactor_cofinite
      (fun _ => zero_le_one) archFactor_ge_one
    simpa only [finprod_one] using h
  refine ⟨q^2*H,mul_pos (sq_pos_of_pos hq) (zero_lt_one.trans_le hH),?_⟩
  intro r hp hr S hs
  let R := ∏ᶠ v, r v
  have hR : 0 ≤ R := by
    have hr' : Function.HasFiniteMulSupport r := eventually_cofinite.mp hr
    rw [show R = _ from finprod_eq_prod_of_mulSupport_toFinset_subset r hr' (Finset.Subset.refl _)]
    exact Finset.prod_nonneg (fun i _ => (hp i).le)
  obtain hS | hS := S.eq_empty_or_nonempty
  · subst S
    exact (Nat.cast_zero (R := ℝ)) ▸ mul_nonneg (mul_nonneg (sq_nonneg _) (zero_le_one.trans hH)) hR
  obtain ⟨x,hx⟩ := hS
  have h₁ := one_le_box_volume r hr (hs x hx).1 (hs x hx).2
  have hHR : 1 ≤ H*R := one_le_mul_of_one_le_of_one_le hH h₁
  have hpos := zero_lt_one.trans_le hHR
  obtain ⟨a,b,ha,hb,hab⟩ := bracket_norm p (hp w)
  obtain ⟨u,t,hu,ht,hut⟩ := bracket_norm p (div_pos (hp w) hpos)
  have hδ : r w/(H*R) ≤ r w := div_le_self (hp w).le hHR
  have hpack := local_packing p (J := S) (fun j => diagonal F w j.val) u b
    (hu.le.trans (hδ.trans hb)) (fun j => ((hs _ j.property).2 w).trans hb) (by
      intro i j hij
      apply hu.trans_le
      have h := box_separation r hr hp p (fun he => hij (Subtype.ext he)) (hs _ i.property).2 (hs _ j.property).2
      apply (div_le_iff₀ hpos).mpr
      change 1 ≤ (H*R) * (‖diagonal F w i.val-diagonal F w j.val‖/r w) at h
      rw [← mul_div_assoc,le_div_iff₀ (hp w),one_mul,mul_comm (H*R)] at h
      exact h)
  rw [Fintype.card_coe] at hpack
  have hu' : r w ≤ (q*‖u.val‖)*(H*R) := (div_le_iff₀ hpos).mp (hut ▸ ht)
  have hb' : ‖b.val‖ ≤ q*r w := hab ▸ mul_le_mul_of_nonneg_left ha.le hq.le
  apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr u.ne_zero)).mp
  calc
    (S.card : ℝ)*‖u.val‖ ≤ q*r w := hpack.trans hb'
    _ ≤ q*((q*‖u.val‖)*(H*R)) := mul_le_mul_of_nonneg_left hu' hq.le
    _ = (q^2*H*R)*‖u.val‖ := by ring

/-- The two-coordinate box estimate in Lemma B.1, including vectors on either axis. -/
theorem rational_vector_box_count : ∃ C : ℝ, 0 < C ∧ ∀ (r : Place F → ℝ),
    (∀ v, 0 < r v) → (∀ᶠ v in cofinite, r v = 1) →
    ∀ S : Finset (RationalPoint F), (∀ z ∈ S, ∀ v,
      max (modulus F v (diagonal F v z.val.1)) (modulus F v (diagonal F v z.val.2)) ≤ r v) →
      (S.card : ℝ) ≤ C * (∏ᶠ v, r v)^2 := by
  obtain ⟨C,hC,hcount⟩ := rational_box_count (F := F)
  refine ⟨(C+1)^2,by positivity,?_⟩
  intro r hp hr S hs
  let R := ∏ᶠ v, r v
  let A := S.image (fun z => z.val.1) ∪ S.image (fun z => z.val.2)
  have mem (z : RationalPoint F) (hz : z ∈ S) : z.val.1 ∈ A ∧ z.val.2 ∈ A :=
    ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hz), Finset.mem_union_right _ (Finset.mem_image_of_mem _ hz)⟩
  have hA (x : F) (hx : x ∈ A) (v : Place F) : modulus F v (diagonal F v x) ≤ r v := by
    rcases Finset.mem_union.mp hx with h | h <;> obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
    · exact (le_max_left ..).trans (hs z hz v)
    · exact (le_max_right ..).trans (hs z hz v)
  obtain hS | ⟨z,hz⟩ := S.eq_empty_or_nonempty
  · subst S; simp; positivity
  have hR : 1 ≤ R := by
    by_cases hx : z.val.1 = 0
    · exact one_le_box_volume r hr (fun hy => z.property (Prod.ext hx hy)) (hA _ (mem z hz).2)
    · exact one_le_box_volume r hr hx (hA _ (mem z hz).1)
  have he := hcount r hp hr (A.erase 0) (fun x hx =>
    ⟨Finset.ne_of_mem_erase hx,hA x (Finset.mem_of_mem_erase hx)⟩)
  have hcard : (A.card : ℝ) ≤ (C+1)*R := calc
    (A.card : ℝ) ≤ ((A.erase 0).card : ℝ) + 1 := by
      exact_mod_cast Finset.card_le_card (show A ⊆ insert 0 (A.erase 0) from
        fun x hx => by by_cases h : x = 0 <;> simp [h,hx]) |>.trans (Finset.card_insert_le ..)
    _ ≤ C*R + R := add_le_add he hR
    _ = _ := by ring
  have hpair : S.card ≤ A.card*A.card := by
    rw [← Finset.card_product]
    exact Finset.card_le_card_of_injOn Subtype.val (fun z hz => Finset.mem_product.mpr (mem z hz))
      (fun _ _ _ _ h => Subtype.ext h)
  calc
    (S.card : ℝ) ≤ (A.card : ℝ)^2 := by exact_mod_cast (sq A.card ▸ hpair)
    _ ≤ ((C+1)*R)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard _
    _ = (C+1)^2*R^2 := mul_pow ..

end MetaplecticPoisson.Datum
