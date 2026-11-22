import MetaplecticSummation.UnramifiedGauss

/-! Uniform bounds and support for the transforms of all unit characters. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField MeasureTheory Set
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n) (p : Prime F)
local notation "v" => (Sum.inr p : Place F)
local notation "K" => LocalField F v
local notation "q" => (p.asIdeal.absNorm : ℝ)
local notation "dx" => selfDual F d.character v
local notation "ψ" => d.character.localValue F v

/-- Every unit character of exponent dividing n at a tame place is the
restriction of a Hilbert character. -/
theorem exists_hilbertUnitChar (hp : p.asIdeal.absNorm.Coprime n) (χ : UnitChar p) (hχ : χ^n = 1) :
    ∃ a : Kˣ, d.hilbertUnitChar p a = χ := by
  obtain ⟨π,hπ⟩ : ∃ π : Kˣ, ‖π.val‖ = q⁻¹ := FinitePlace.exists_norm_uniformizer p
  obtain ⟨U,hU,ho,gen⟩ := d.tame_unit_generator p hp π hπ
  let g : integralUnits p := ⟨U,hU⟩
  let ζ := d.unitPairing v π U
  have hζ : IsPrimitiveRoot ζ.val n := IsPrimitiveRoot.coe_units_iff.mpr (ho ▸ IsPrimitiveRoot.orderOf ζ)
  have tors (u : integralUnits p) : χ u ^ n = 1 := congrArg (fun θ : UnitChar p => θ u) hχ
  have hg : (χ g : ℂ)^n = 1 := by rw [← Circle.coe_pow,tors,Circle.coe_one]
  obtain ⟨k,_,hk⟩ := hζ.eq_pow_of_pow_eq_one hg
  let θ := d.hilbertUnitChar p (π^k)
  have he : θ g = χ g := by
    apply Subtype.ext
    change (d.unitPairing v (π^k) U).val = _
    rw [map_pow,MonoidHom.pow_apply,Units.val_pow_eq_pow_val]
    exact hk
  refine ⟨π^k, MonoidHom.ext fun u => ?_⟩
  obtain ⟨l,z,hz,hu⟩ := gen u.val u.property
  let Z : integralUnits p := ⟨z,hz⟩
  have hs : u = g^l*Z^n := Subtype.ext hu
  have ht : θ Z ^ n = 1 := congrArg (fun h : UnitChar p => h Z) (d.hilbertUnitChar_pow p (π^k))
  change θ u = χ u
  rw [hs,map_mul,map_mul,map_zpow,map_zpow,map_pow,map_pow,he,ht,tors]

omit [NeZero n] in
/-- Additive-character integral over a valuation ball with the unramified normalization. -/
theorem phase_ball (hψ : d.UnramifiedAt v) (b : Kˣ) :
    (∫ x in {x : K | ‖x‖ ≤ ‖b.val‖}, ψ x ∂dx) = if ‖b.val‖ ≤ 1 then (‖b.val‖ : ℂ) else 0 := by
  let A := {x : K | ‖x‖ ≤ ‖b.val‖}
  have hA : MeasurableSet A := (isClosed_le continuous_norm continuous_const).measurableSet
  rw [← integral_indicator hA]
  have hh := d.ball_character_integral p hψ b 1
  simp only [A,indicator,mem_setOf_eq,ballValue,ite_mul,one_mul,zero_mul] at hh ⊢
  exact hh

omit [NeZero n] in
/-- The three possible additive-character integrals over a valuation sphere. -/
theorem phase_sphere (hψ : d.UnramifiedAt v) (t : Kˣ) :
    (∫ y in {y : K | ‖y‖ = ‖t.val‖}, ψ y ∂dx) =
      if ‖t.val‖ ≤ 1 then (‖t.val‖ : ℂ)*(1-(q : ℂ)⁻¹) else if ‖t.val‖ = q then -1 else 0 := by
  let A := {x : K | ‖x‖ = ‖t.val‖}
  have hA : MeasurableSet A := (isClosed_eq continuous_norm continuous_const).measurableSet
  have hs (x : K) : A.indicator (ψ) (t.val*x) = if ‖x‖ = 1 then ψ (t.val*x) else 0 := by
    simp only [A,indicator,mem_setOf_eq,norm_mul,mul_eq_left₀ (norm_ne_zero_iff.mpr t.ne_zero)]
  have hg : d.unitGauss p (fun _ => 1) t.val =
      ∫ x, (if ‖x‖ = 1 then ψ (t.val*x) else 0) ∂dx := by
    rw [d.unitGauss_additive]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x = 0 <;> simp [hx]
  have hh := d.integral_local_mul v t (A.indicator (ψ))
  dsimp only at hh
  simp_rw [hs] at hh
  rw [← hg,d.unitGauss_trivial p hψ,integral_indicator hA] at hh
  have hn : (‖t.val‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr t.ne_zero)
  change _ = _ / (‖t.val‖ : ℂ) at hh
  rw [← (eq_div_iff hn).mp hh]
  have hq : 1 < q := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
  by_cases hi : ‖t.val‖ ≤ 1
  · simp [hi,(hi.trans_lt hq).ne,mul_comm]
  · by_cases he : ‖t.val‖ = q
    · rw [if_neg hi,if_pos he,if_neg hi,if_pos he,zero_sub,he,neg_mul,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hq).ne')]
    · simp [hi,he]

omit [NeZero n] in
private theorem phase_shell_bounds (hψ : d.UnramifiedAt v) (t : Kˣ) :
    let I := ∫ y in {y : K | ‖y‖ = ‖t.val‖}, ψ y ∂dx
    ‖I‖ ≤ 1 ∧ (q < ‖t.val‖ → I = 0) := by
  dsimp only
  rw [d.phase_sphere p hψ t]
  have hq : 1 < q := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
  have hcoef : ‖1-(q : ℂ)⁻¹‖ ≤ 1 := by
    rw [← Complex.ofReal_inv,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,
      Real.norm_of_nonneg (sub_nonneg.mpr (inv_lt_one_of_one_lt₀ hq).le)]
    linarith [inv_pos.mpr (zero_lt_one.trans hq)]
  by_cases ht : ‖t.val‖ ≤ 1
  · rw [if_pos ht,norm_mul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
    exact ⟨mul_le_one₀ ht (norm_nonneg _) hcoef,fun h => (h.not_ge (ht.trans hq.le)).elim⟩
  · rw [if_neg ht]
    by_cases he : ‖t.val‖ = q
    · rw [if_pos he]; simp [he]
    · rw [if_neg he]; simp

omit [NeZero n] in
theorem norm_unitGauss_le_one (hψ : d.UnramifiedAt v) (θ : Weight v)
    (hθ : ∀ u : Kˣ, ‖u.val‖ = 1 → ‖θ u‖ ≤ 1) (α : K) : ‖d.unitGauss p θ α‖ ≤ 1 := by
  let B := {x : K | ‖x‖ ≤ 1}
  have hB : MeasurableSet B := (isClosed_le continuous_norm continuous_const).measurableSet
  have hi : Integrable (B.indicator (fun _ => (1:ℝ))) dx := by
    apply (d.ball_integrable p 1).norm.congr
    filter_upwards with x
    by_cases hx : ‖x‖ ≤ 1 <;> simp [B,indicator,ballValue,hx]
  have vol : (∫ x, B.indicator (fun _ => (1:ℝ)) x ∂dx) = 1 := by
    rw [integral_indicator hB,integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_one]
    exact d.selfDual_volume_unramified p hψ
  rw [d.unitGauss_additive]
  apply le_trans _ vol.le
  apply norm_integral_le_of_norm_le hi
  filter_upwards with x
  by_cases hn : x = 0
  · simp [hn,B,indicator]
  · by_cases hx : ‖x‖ = 1
    · simpa only [dif_pos hn,if_pos hx,norm_mul,d.character.norm_localValue, mul_one,
        indicator_of_mem (show x ∈ B from hx.le)] using hθ (Units.mk0 x hn) hx
    · by_cases h : ‖x‖ ≤ 1 <;> simp [hn,hx,B,indicator,h]

private theorem pow_ball_bounds (hψ : d.UnramifiedAt v) (c : Kˣ) :
    let I := ∫ y in {y : K | ‖y‖^n ≤ ‖c.val‖}, ψ y ∂dx
    ‖I‖ ≤ 1 ∧ (q^(n-1) < ‖c.val‖ → I = 0) := by
  obtain ⟨m,hm⟩ : ∃ m : ℤ, ‖c.val‖ = q^m := norm_zpow_residue_card p c
  obtain ⟨π,hπ⟩ : ∃ π : Kˣ, ‖π.val‖ = q⁻¹ := FinitePlace.exists_norm_uniformizer p
  let b : Kˣ := π^(-(m/(n : ℤ)))
  have hb : ‖b.val‖ = q^(m/(n : ℤ)) := by simp [b,Units.val_zpow_eq_zpow_val,hπ]
  have hq : 1 < q := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
  have hn : 0 < (n : ℤ) := by exact_mod_cast NeZero.pos n
  have hset : {y : K | ‖y‖^n ≤ ‖c.val‖} = {y : K | ‖y‖ ≤ ‖b.val‖} := by
    ext y
    simp only [mem_setOf_eq]
    by_cases hy : y = 0
    · simp [hy,zero_pow (NeZero.ne n)]
    obtain ⟨l,hl⟩ : ∃ l : ℤ, ‖y‖ = q^l := norm_zpow_residue_card p (Units.mk0 y hy)
    rw [hl,hb,hm,← zpow_natCast,← zpow_mul,zpow_le_zpow_iff_right₀ hq,
      zpow_le_zpow_iff_right₀ hq,Int.le_ediv_iff_mul_le hn]
  dsimp only
  rw [hset,d.phase_ball p hψ b]
  by_cases hi : ‖b.val‖ ≤ 1
  · rw [if_pos hi,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
    refine ⟨hi, fun h => False.elim ?_⟩
    rw [hb,← zpow_zero q,zpow_le_zpow_iff_right₀ hq] at hi
    rw [hm,← zpow_natCast,zpow_lt_zpow_iff_right₀ hq] at h
    have hnle : (n : ℤ) ≤ m := by omega
    have h₁ : (1 : ℤ) ≤ m/n := (Int.le_ediv_iff_mul_le hn).mpr (by simpa using hnle)
    omega
  · simp [hi]

private theorem pow_sphere_bounds (hψ : d.UnramifiedAt v) (c : Kˣ) :
    let I := ∫ y in {y : K | ‖y‖^n = q*‖c.val‖}, ψ y ∂dx
    ‖I‖ ≤ 1 ∧ (q^(n-1) < ‖c.val‖ → I = 0) := by
  let B := {y : K | ‖y‖^n = q*‖c.val‖}
  have hq : 1 < q := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
  have hq₀ := zero_lt_one.trans hq
  change ‖∫ y in B, ψ y ∂dx‖ ≤ 1 ∧ _
  by_cases h : B.Nonempty
  · obtain ⟨x,hx⟩ := h
    change ‖x‖^n = q*‖c.val‖ at hx
    have hn : x ≠ 0 := by
      intro hz
      rw [hz,norm_zero,zero_pow (NeZero.ne n)] at hx
      exact (mul_pos hq₀ (norm_pos_iff.mpr c.ne_zero)).ne' hx.symm
    let t := Units.mk0 x hn
    have hB : B = {y : K | ‖y‖ = ‖t.val‖} := by
      ext y
      change ‖y‖^n = q*‖c.val‖ ↔ ‖y‖ = ‖x‖
      rw [← hx,pow_left_inj₀ (norm_nonneg y) (norm_nonneg x) (NeZero.ne n)]
    change ‖∫ y in B, ψ y ∂dx‖ ≤ 1 ∧ (q^(n-1) < ‖c.val‖ → (∫ y in B, ψ y ∂dx) = 0)
    rw [hB]
    have shell := d.phase_shell_bounds p hψ t
    refine ⟨shell.1,fun h => shell.2 ?_⟩
    have hh := mul_lt_mul_of_pos_left h hq₀
    rw [← pow_succ',Nat.sub_add_cancel (NeZero.pos n),← hx] at hh
    exact (pow_lt_pow_iff_left₀ hq₀.le (norm_nonneg x) (NeZero.ne n)).mp hh
  · have hB := Set.not_nonempty_iff_eq_empty.mp h
    change ‖∫ y in B, ψ y ∂dx‖ ≤ 1 ∧ (q^(n-1) < ‖c.val‖ → (∫ y in B, ψ y ∂dx) = 0)
    simp [hB]

private theorem hilbert_transform_bounds (hp : p.asIdeal.absNorm.Coprime n) (hψ : d.UnramifiedAt v)
    (a c : Kˣ) :
    let W : Weight v := fun x => if ‖x.val‖ = 1 then d.symbol v a x else 0
    ‖d.dualWeight v W c‖ ≤ 1 ∧ (q^(n-1) < ‖c.val‖ → d.dualWeight v W c = 0) := by
  obtain ⟨s,hs⟩ : ∃ s : ℤ, ‖a.val‖ = q^s := norm_zpow_residue_card p a
  obtain ⟨l,hl⟩ : ∃ l : ℤ, ‖c.val‖ = q^l := norm_zpow_residue_card p c
  let i := -s
  let j := -l
  have ha : ‖a.val‖ = q^(-i) := by simpa only [i,neg_neg] using hs
  have hc : ‖c.val‖ = q^(-j) := by simpa only [j,neg_neg] using hl
  obtain ⟨same,other⟩ := d.untwistedVector p hp hψ a c i j ha hc
  let W : Weight v := fun x => if ‖x.val‖ = 1 then d.symbol v a x else 0
  let V := d.dualWeight v W c
  change ‖V‖ ≤ 1 ∧ (_ → V = 0)
  have hq : 1 < q := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
  have hq₀ := zero_lt_one.trans hq
  by_cases h : i ≡ j [ZMOD n]
  · let A := ∫ y in {y : K | ‖y‖^n ≤ ‖c.val‖}, ψ y ∂dx
    let B := ∫ y in {y : K | ‖y‖^n = q*‖c.val‖}, ψ y ∂dx
    have hV : V = (1-(q : ℂ)⁻¹)*A - (q : ℂ)⁻¹*B := same h
    have hA := d.pow_ball_bounds p hψ c
    have hB := d.pow_sphere_bounds p hψ c
    rw [hV]
    constructor
    · apply (norm_sub_le ..).trans
      rw [norm_mul,norm_mul,← Complex.ofReal_inv,← Complex.ofReal_one,← Complex.ofReal_sub,
        Complex.norm_real,Real.norm_of_nonneg (sub_nonneg.mpr (inv_lt_one_of_one_lt₀ hq).le),
        Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hq₀.le)]
      calc _ ≤ (1-q⁻¹)*1 + q⁻¹*1 := add_le_add
              (mul_le_mul_of_nonneg_left hA.1 (sub_nonneg.mpr (inv_lt_one_of_one_lt₀ hq).le))
              (mul_le_mul_of_nonneg_left hB.1 (inv_nonneg.mpr hq₀.le))
           _ = _ := by ring
    · intro hoff
      rw [show A = 0 from hA.2 hoff,show B = 0 from hB.2 hoff,mul_zero,mul_zero,sub_zero]
  · obtain ⟨hzero,heq⟩ := other h
    by_cases hd : (n : ℤ) ∣ j-1
    · obtain ⟨k,hk⟩ := hd
      have hj : j = n*k+1 := by omega
      obtain ⟨π,hπ⟩ : ∃ π : Kˣ, ‖π.val‖ = q⁻¹ := FinitePlace.exists_norm_uniformizer p
      let t := π^k
      have ht : ‖t.val‖ = q^(-k) := by simp [t,Units.val_zpow_eq_zpow_val,hπ]
      let I := ∫ y in {y : K | ‖y‖ = ‖t.val‖}, ψ y ∂dx
      let G := d.unitGauss p (fun x => d.symbol v (c/a) x) (-t.val^n/c.val)
      have hV : V = G * I := by simpa only [G,I,ht] using heq k hj t ht
      have hi := d.phase_shell_bounds p hψ t
      have hg : ‖G‖ ≤ 1 := d.norm_unitGauss_le_one p hψ _ (fun x _ => (d.norm_symbol v (c/a) x).le) _
      rw [hV,norm_mul]
      refine ⟨mul_le_one₀ hg (norm_nonneg _) hi.1,fun hoff => ?_⟩
      have hn : ‖t.val‖^n = q*‖c.val‖ := by
        rw [ht,hc,← zpow_natCast,← zpow_mul,show q*q^(-j) = q^(1-j) by rw [sub_eq_add_neg,zpow_add₀ hq₀.ne',zpow_one]]
        congr 1
        linear_combination hj
      have hb := mul_lt_mul_of_pos_left hoff hq₀
      rw [← pow_succ',Nat.sub_add_cancel (NeZero.pos n),← hn] at hb
      rw [show I = 0 from hi.2 ((pow_lt_pow_iff_left₀ hq₀.le (norm_nonneg _) (NeZero.ne n)).mp hb),mul_zero]
    · simp [show V = 0 from hzero hd]

omit [NeZero n] in
/-- A continuous unit character is trivial on a principal-unit subgroup.
For a nontrivial character the least such level is positive. -/
theorem exists_unitChar_conductor (χ : UnitChar p) (hc : Continuous χ) (hn : χ ≠ 1) :
    ∃ e : ℕ, 0 < e ∧ IsLeast {k | trivialAtLevel χ k} e := by
  let f := fun u : integralUnits p => u.val.val
  have emb : Topology.IsEmbedding f := Units.isEmbedding_val₀.comp Topology.IsEmbedding.subtypeVal
  have h1 : (1 : Circle) ∈ Circle.centeredArc (Real.pi/2) := by
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  have near : χ ⁻¹' Circle.centeredArc (Real.pi/2) ∈ nhds (1 : integralUnits p) :=
    hc.continuousAt.preimage_mem_nhds ((Circle.isOpen_centeredArc _).mem_nhds (by simpa using h1))
  rw [emb.nhds_eq_comap] at near
  obtain ⟨U,hU,hu⟩ := Filter.mem_comap.mp near
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hU
  have hq : 1 < q := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one hr (inv_lt_one_of_one_lt₀ hq)
  have hk' : (q^(k+1))⁻¹ < r := by
    have h := pow_le_pow_of_le_one (inv_nonneg.mpr (zero_lt_one.trans hq).le)
      (inv_lt_one_of_one_lt₀ hq).le (Nat.le_succ k)
    simpa only [inv_pow] using h.trans_lt hk
  have hex : ∃ k : ℕ, trivialAtLevel χ k := by
    refine ⟨k+1,fun u h => ?_⟩
    have hd := h.resolve_left (Nat.succ_ne_zero k)
    have bound (m : ℕ) : ‖u.val.val^m-1‖ ≤ ‖u.val.val-1‖ := by
      letI : IsUltrametricDist K := inferInstanceAs (IsUltrametricDist (p.adicCompletion F))
      induction m with
      | zero => simp
      | succ m ih =>
        rw [show u.val.val^(m+1)-1 = (u.val.val^m-1)*u.val.val+(u.val.val-1) by ring]
        apply (IsUltrametricDist.norm_add_le_max _ _).trans
        rw [norm_mul,show ‖u.val.val‖ = 1 from u.property,mul_one]
        exact max_le ih le_rfl
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro m _
    rw [← map_pow]
    apply hu
    apply hball
    change dist (u.val.val^m) 1 < r
    rw [dist_eq_norm]
    exact ((bound m).trans hd).trans_lt hk'
  let e := Nat.find hex
  have least : IsLeast {k | trivialAtLevel χ k} e := ⟨Nat.find_spec hex,fun _ h => Nat.find_min' hex h⟩
  refine ⟨e, Nat.pos_of_ne_zero ?_,least⟩
  intro h
  have hzero : trivialAtLevel χ 0 := h ▸ least.1
  exact hn (MonoidHom.ext fun u => hzero u (Or.inl rfl))

/-- The support and unit bound of the twisted-bounds corollary. If the n-th
power is trivial the paper takes e = 1. Otherwise e is its conductor exponent. -/
theorem unit_transform_bounds (hp : p.asIdeal.absNorm.Coprime n) (hψ : d.UnramifiedAt v)
    (χ : UnitChar p) (hχ : Continuous χ) (e : ℕ)
    (he : (χ^n = 1 ∧ e = 1) ∨ (0 < e ∧ IsLeast {k | trivialAtLevel (χ^n) k} e)) (c : Kˣ) :
    ‖d.dualWeight v (charWeight χ) c‖ ≤ 1 ∧
      (q^((n-1)*e) < ‖c.val‖ → d.dualWeight v (charWeight χ) c = 0) := by
  rcases he with ⟨hpow,rfl⟩ | ⟨he,hcond⟩
  · obtain ⟨a,rfl⟩ := d.exists_hilbertUnitChar p hp χ hpow
    have hW : charWeight (d.hilbertUnitChar p a) = fun x : Kˣ =>
        if ‖x.val‖ = 1 then d.symbol v a x else 0 := by
      funext x
      by_cases hu : x ∈ integralUnits p
      · rw [charWeight,dif_pos hu,if_pos (show ‖x.val‖ = 1 from hu)]
        rfl
      · rw [charWeight,dif_neg hu,if_neg (show ‖x.val‖ ≠ 1 from hu)]
    simpa only [hW,Nat.mul_one] using d.hilbert_transform_bounds p hp hψ a c
  · obtain ⟨off,on⟩ := d.twistedVector p hp hψ χ hχ e he hcond c
    refine ⟨?_,fun h => off h.ne'⟩
    by_cases hit : ‖c.val‖ = q^((n-1)*e)
    · exact ((on hit).1).le
    · rw [off hit,norm_zero]; exact zero_le_one

/-- For every continuous unit character the prescribed exponent exists,
and the same support and norm bounds hold at every nonzero argument. -/
theorem exists_unit_transform_bounds (hp : p.asIdeal.absNorm.Coprime n) (hψ : d.UnramifiedAt v)
    (χ : UnitChar p) (hχ : Continuous χ) :
    ∃ e : ℕ, ((χ^n = 1 ∧ e = 1) ∨ (0 < e ∧ IsLeast {k | trivialAtLevel (χ^n) k} e)) ∧
      ∀ c : Kˣ, ‖d.dualWeight v (charWeight χ) c‖ ≤ 1 ∧
        (q^((n-1)*e) < ‖c.val‖ → d.dualWeight v (charWeight χ) c = 0) := by
  by_cases ht : χ^n = 1
  · exact ⟨1,Or.inl ⟨ht,rfl⟩,d.unit_transform_bounds p hp hψ χ hχ 1 (Or.inl ⟨ht,rfl⟩)⟩
  · obtain ⟨e,he,hc⟩ := exists_unitChar_conductor p (χ^n) (hχ.pow n) ht
    exact ⟨e,Or.inr ⟨he,hc⟩,d.unit_transform_bounds p hp hψ χ hχ e (Or.inr ⟨he,hc⟩)⟩

end MetaplecticPoisson.Datum
