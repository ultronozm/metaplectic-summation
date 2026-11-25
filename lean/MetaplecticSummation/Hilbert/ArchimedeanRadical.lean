import MetaplecticSummation.LocalSymbols
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField
open scoped Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- The real sign pairing detects every negative unit when the cover has degree two. -/
theorem real_symbol_power (w : InfinitePlace F) (hw : w.IsReal) (a : (LocalField F (.inl w))ˣ)
    (ha : ∀ u, d.symbol (.inl w) u a = 1) : ∃ b, b^n = a := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hn : n ≤ 2 := by
    by_contra! h
    have hz := InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt h d.primitive
    have pos : 0 < InfinitePlace.nrRealPlaces F := Fintype.card_pos_iff.mpr ⟨⟨w,hw⟩⟩
    omega
  rcases (show n = 1 ∨ n = 2 by have := NeZero.pos n; omega) with hn|hn
  · exact ⟨a, by rw [hn,pow_one]⟩
  have hp : 0 ≤ e a.val := by
    by_contra! hneg
    let m : ℕ+ := ⟨n, NeZero.pos n⟩
    have he : d.family = Hilbert.family m d.primitive :=
      IsHilbertFamily.unique d.primitive d.family_spec (Hilbert.family_spec m d.primitive)
    have h : d.family (.inl w) (-1) a = 1 :=
      d.injective ((Units.ext (ha (-1))).trans d.embedding.map_one.symm)
    rw [he] at h
    change Hilbert.infiniteValue m w (-1) a = 1 at h
    have hval := congrArg (fun z : Mu F m => (z.val : F)) h
    have hs : e ((-1 : (LocalField F (.inl w))ˣ).val) < 0 := by
      change e (-1) < 0
      rw [map_neg,map_one]
      norm_num
    have hdeg : (m : ℕ) = 2 := hn
    simp [Hilbert.infiniteValue, hdeg, hw, hneg, e] at hval
    exact (not_le_of_gt hs) hval
  let z := (e a.val) ^ (n : ℝ)⁻¹
  have hz : z^n = e a.val := Real.rpow_inv_natCast_pow hp (NeZero.ne n)
  have hne : z ≠ 0 := by
    rintro h
    exact ((map_ne_zero e).mpr a.ne_zero) (hz.symm.trans (by rw [h,zero_pow (NeZero.ne n)]))
  refine ⟨Units.mk0 (e.symm z) ((map_ne_zero _).mpr hne), Units.ext (e.injective ?_)⟩
  change e ((e.symm z)^n) = e a.val
  rw [map_pow,e.apply_symm_apply,hz]

/-- Every nonzero complex number is an n-th power in the completion. -/
theorem complex_unit_power (w : InfinitePlace F) (hw : w.IsComplex) (a : (LocalField F (.inl w))ˣ) :
    ∃ b : (LocalField F (.inl w))ˣ, b^n = a := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (e a.val) (NeZero.pos n)
  have hne : z ≠ 0 := by
    rintro rfl
    exact ((map_ne_zero e).mpr a.ne_zero) (hz.symm.trans (zero_pow (NeZero.ne n)))
  let b : (LocalField F (.inl w))ˣ := Units.mk0 (e.symm z) ((map_ne_zero _).mpr hne)
  have hb : b^n = a := by
    apply Units.ext
    apply e.injective
    change e ((e.symm z)^n) = e a.val
    rw [map_pow,e.apply_symm_apply,hz]
  exact ⟨b,hb⟩

end MetaplecticPoisson.Datum
