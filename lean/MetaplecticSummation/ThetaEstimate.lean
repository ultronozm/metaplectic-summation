import MetaplecticSummation.ThetaBoxes

/-! Dyadic summation of the rational box estimate in Lemma B.1. -/

noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField Filter
open Classical
variable {F : Type} [Field F] [NumberField F]

def vectorModulus (v : Place F) (z : RationalPoint F) : ℝ :=
  max (modulus F v (diagonal F v z.val.1)) (modulus F v (diagonal F v z.val.2))

/-- The finite cutoff and archimedean decay factor on the right of (B.2),
with the placewise scale absorbed into r. -/
def boxWeight (r : Place F → ℝ) (z : RationalPoint F) : ℝ :=
  if ∀ p : Prime F, vectorModulus (.inr p) z ≤ r (.inr p) then
    ∏ w : InfinitePlace F, (max 1 (vectorModulus (.inl w) z / r (.inl w)))⁻¹^3 else 0

private theorem dyadic_level (s : ℝ) :
    ∃ k : ℕ, s ≤ (2:ℝ)^k ∧ (2:ℝ)^k ≤ 2*max 1 s := by
  have hex : ∃ k : ℕ, s ≤ (2:ℝ)^k := by
    obtain ⟨k,h⟩ := pow_unbounded_of_one_lt s (by norm_num : (1:ℝ) < 2)
    exact ⟨k,h.le⟩
  refine ⟨Nat.find hex,Nat.find_spec hex,?_⟩
  generalize he : Nat.find hex = k
  cases k with
  | zero => rw [pow_zero]; linarith [le_max_left (1:ℝ) s]
  | succ k =>
    have h := Nat.find_min hex (show k < Nat.find hex by omega)
    rw [pow_succ]
    linarith [le_max_right (1:ℝ) s,lt_of_not_ge h]

private theorem sum_levels_le {I : Type*} [Fintype I] (J : Finset (I → ℕ)) :
    ∑ j ∈ J, (∏ i, (2:ℝ)^j i)⁻¹ ≤ 2^(Fintype.card I) := by
  let T (i : I) := J.image (fun j => j i)
  have hsub : J ⊆ Fintype.piFinset T := fun j hj => Fintype.mem_piFinset.mpr (fun i => Finset.mem_image_of_mem _ hj)
  have hT (i : I) : ∑ k ∈ T i, ((1:ℝ)/2)^k ≤ 2 :=
    (summable_geometric_two.sum_le_tsum _ (fun _ _ => by positivity)).trans_eq tsum_geometric_two
  have eqn (j : I → ℕ) : (∏ i, (2:ℝ)^j i)⁻¹ = ∏ i, ((1:ℝ)/2)^j i := by
    simp only [one_div,inv_pow,Finset.prod_inv_distrib]
  simp_rw [eqn]
  calc
    _ ≤ ∑ j ∈ Fintype.piFinset T, ∏ i, ((1:ℝ)/2)^j i := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => Finset.prod_nonneg (fun _ _ => by positivity))
    _ = ∏ i, ∑ k ∈ T i, ((1:ℝ)/2)^k := (Finset.prod_univ_sum T _).symm
    _ ≤ ∏ _ : I, (2:ℝ) := Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun _ _ => by positivity)) (fun i _ => hT i)
    _ = (2:ℝ)^(Fintype.card I) := by simp

private def archScale (j : InfinitePlace F → ℕ) : Place F → ℝ
  | .inl w => 2^j w
  | .inr _ => 1

private theorem archScale_prod (j : InfinitePlace F → ℕ) : ∏ᶠ v, archScale j v = ∏ w, (2:ℝ)^j w := by
  let e : InfinitePlace F ↪ Place F := Function.Embedding.inl
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := Finset.univ.map e) (by
    rintro (w|p) hw
    · exact Finset.mem_map.mpr ⟨w,Finset.mem_univ _,rfl⟩
    · exact (hw rfl).elim),Finset.prod_map]
  rfl

/-- The dyadic bound following (B.2), uniform in the radii. -/
theorem theta_box_estimate : ∃ C : ℝ, 0 < C ∧ ∀ r : Place F → ℝ,
    (∀ v, 0 < r v) → (∀ᶠ v in cofinite, r v = 1) →
    Summable (boxWeight r) ∧ (∑' z, boxWeight r z) ≤ C*(∏ᶠ v, r v)^2 := by
  obtain ⟨C,hC,hcount⟩ := rational_vector_box_count (F := F)
  let m := Fintype.card (InfinitePlace F)
  refine ⟨C*8^m*2^m,by positivity,?_⟩
  intro r hp hr
  let R := ∏ᶠ v, r v
  let level (z : RationalPoint F) (w : InfinitePlace F) := (dyadic_level (vectorModulus (.inl w) z / r (.inl w))).choose
  let volume (j : InfinitePlace F → ℕ) := ∏ w, (2:ℝ)^j w
  have hv (j) : 0 < volume j := Finset.prod_pos (fun _ _ => by positivity)
  let good (z : RationalPoint F) := ∀ p : Prime F, vectorModulus (.inr p) z ≤ r (.inr p)
  have h₀ (z) : 0 ≤ boxWeight r z := by
    unfold boxWeight
    split
    · exact Finset.prod_nonneg (fun w _ => pow_nonneg (inv_nonneg.mpr (le_trans zero_le_one (le_max_left ..))) _)
    · exact le_rfl
  have weight (z : RationalPoint F) (hz : good z) : boxWeight r z ≤ 8^m * (volume (level z))⁻¹^3 := by
    rw [boxWeight,if_pos hz]
    have hw (w : InfinitePlace F) : let s := vectorModulus (.inl w) z / r (.inl w)
        (max 1 s)⁻¹^3 ≤ 8 * ((2:ℝ)^level z w)⁻¹^3 := by
      dsimp only
      have h := (dyadic_level (vectorModulus (.inl w) z / r (.inl w))).choose_spec.2
      let M := max 1 (vectorModulus (.inl w) z / r (.inl w))
      have hM : 0 < M := zero_lt_one.trans_le (le_max_left ..)
      have h' : M⁻¹ ≤ 2/((2:ℝ)^level z w) := by
        rw [inv_eq_one_div,div_le_div_iff₀ hM (by positivity),one_mul]
        exact h
      calc
        M⁻¹^3 ≤ (2/((2:ℝ)^level z w))^3 := pow_le_pow_left₀ (inv_pos.mpr hM).le h' _
        _ = _ := by rw [div_eq_mul_inv,mul_pow]; norm_num
    apply (Finset.prod_le_prod₀ (fun w _ => by positivity [le_max_left (1:ℝ) (vectorModulus (.inl w) z/r (.inl w))]) (fun w _ => hw w)).trans_eq
    simp [volume,Finset.prod_mul_distrib,Finset.prod_pow,Finset.prod_inv_distrib,m]
  have hsum (S : Finset (RationalPoint F)) : ∑ z ∈ S, boxWeight r z ≤ C*8^m*2^m*R^2 := by
    let P := S.filter good
    let J := P.image level
    have es : ∑ z ∈ S, boxWeight r z = ∑ z ∈ P, boxWeight r z := by
      apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro z hz h
      exact if_neg (fun he => h (Finset.mem_filter.mpr ⟨hz,he⟩))
    rw [es,← Finset.sum_fiberwise_of_maps_to (t := J) (fun z hz => Finset.mem_image_of_mem level hz)]
    have fiber (j : InfinitePlace F → ℕ) : let U := P.filter (fun z => level z = j)
        ∑ z ∈ U, boxWeight r z ≤ (C*8^m*R^2)*(volume j)⁻¹ := by
      dsimp only
      let U := P.filter (fun z => level z = j)
      let r' (v : Place F) := r v*archScale j v
      have he : ∀ᶠ v in cofinite, archScale j v = 1 := eventually_place_of_finite (.of_forall fun _ => rfl)
      have ha : ∀ᶠ v in cofinite, r' v = 1 := by filter_upwards [hr,he] with v h h'; simp [r',h,h']
      have hh := hcount r' (fun v => mul_pos (hp _) (by cases v <;> simp [archScale])) ha U (by
        intro z hz v
        obtain ⟨hz,hj⟩ := Finset.mem_filter.mp hz
        cases v with
        | inr p => simpa only [r',archScale,mul_one,vectorModulus] using (Finset.mem_filter.mp hz).2 p
        | inl w =>
          have h := (dyadic_level (vectorModulus (.inl w) z / r (.inl w))).choose_spec.1
          change _ ≤ (2:ℝ)^level z w at h
          rw [hj, div_le_iff₀ (hp _),mul_comm] at h
          exact h)
      rw [show (∏ᶠ v, r' v) = R*volume j from (finprod_mul_distrib (eventually_cofinite.mp hr)
        (eventually_cofinite.mp he)).trans (congrArg (R * ·) (archScale_prod j))] at hh
      calc
        ∑ z ∈ U, boxWeight r z ≤ ∑ _z ∈ U, 8^m*(volume j)⁻¹^3 := Finset.sum_le_sum fun z hz => by
          obtain ⟨hz,hj⟩ := Finset.mem_filter.mp hz
          simpa only [hj] using weight z (Finset.mem_filter.mp hz).2
        _ = (U.card : ℝ)*(8^m*(volume j)⁻¹^3) := by simp
        _ ≤ C*(R*volume j)^2*(8^m*(volume j)⁻¹^3) := mul_le_mul_of_nonneg_right hh (by positivity [hv j])
        _ = _ := by field_simp [(hv j).ne']
    calc
      _ ≤ ∑ j ∈ J, (C*8^m*R^2)*(volume j)⁻¹ := Finset.sum_le_sum (fun j _ => fiber j)
      _ = _ := (Finset.mul_sum ..).symm
      _ ≤ (C*8^m*R^2)*2^m := mul_le_mul_of_nonneg_left (sum_levels_le J) (by positivity)
      _ = _ := by ring
  exact ⟨summable_of_sum_le h₀ hsum,Real.tsum_le_of_sum_le h₀ hsum⟩

end MetaplecticPoisson.Datum
