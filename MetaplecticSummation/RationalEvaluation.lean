import MetaplecticSummation.Schwartz
import MetaplecticSummation.Schwartz.Basic
import MetaplecticSummation.AdelicCharacters

noncomputable section
namespace MetaplecticPoisson
namespace Datum
open Filter NumberField IsDedekindDomain
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- Algebraic adelic Schwartz space of §9.2. -/
abbrev Schwartz := restrictedTensor d.basic

def pure (f : ∀ v, d.schwartz v) (hf : ∀ᶠ v in cofinite, f v = d.basic v) : d.Schwartz :=
  ⟨PiTensorProduct.tprod ℂ f, Submodule.subset_span ⟨f, hf, rfl⟩⟩

def diagonalPoint (p : RationalPoint F) (v : Place F) : LocalField F v × LocalField F v :=
  (diagonal F v p.val.1, diagonal F v p.val.2)

private theorem xChart_unit {K : Type} [Field K] (f : Charts K) (u : Kˣ) (y : K) :
    xChart f (u.val,y) = f.1 u y := by simp [xChart,u.ne_zero]

private theorem yChart_unit {K : Type} [Field K] (f : Charts K) (x : K) (u : Kˣ) :
    yChart f (x,u.val) = f.2 x u := by simp [yChart,u.ne_zero]

/-- The chart choice is made once at the rational point. -/
def localValue (p : RationalPoint F) (v : Place F) (f : d.schwartz v) : ℂ := by
  classical exact if p.val.1 ≠ 0 then xChart f (diagonalPoint p v) else yChart f (diagonalPoint p v)

theorem eventually_diagonal_norm_one {a : F} (ha : a ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in cofinite, ‖diagonal F (.inr w) a‖ = 1 :=
  NumberField.FinitePlace.equivHeightOneSpectrum.symm.injective.tendsto_cofinite.eventually
    (eventually_cofinite.mpr (NumberField.FinitePlace.hasFiniteMulSupport ha))

/-- The product formula in the modulus normalization used by the local integrals. -/
theorem diagonal_modulus_product {a : F} (ha : a ≠ 0) :
    ∏ᶠ v, modulus F v (diagonal F v a) = 1 := by
  let m (v : Place F) := modulus F v (diagonal F v a)
  have hfin : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in cofinite, m (.inr w) = 1 := eventually_diagonal_norm_one ha
  have hm : Function.HasFiniteMulSupport m := eventually_cofinite.mp (eventually_place_of_finite hfin)
  have hinf (w : InfinitePlace F) : m (.inl w) = (w a)^w.mult := by
    change ‖algebraMap F w.Completion a‖ ^ w.mult = _
    exact congrArg (· ^ w.mult) (InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm a))
  have hr : Function.HasFiniteMulSupport (m ∘ Sum.inr) := eventually_cofinite.mp hfin
  have hp (w : HeightOneSpectrum (𝓞 F)) :
      m (.inr w) = NumberField.FinitePlace.equivHeightOneSpectrum.symm w a := rfl
  change finprod m = 1
  rw [← tprod_eq_finprod (L := SummationFilter.unconditional _) hm, Multipliable.tprod_sum (f := m) (hasProd_fintype _).multipliable
    (multipliable_of_hasFiniteMulSupport hr), tprod_fintype, tprod_eq_finprod (f := fun w => m (.inr w)) hr]
  simp_rw [hinf,hp]
  rw [finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm (f := fun w : NumberField.FinitePlace F => w a)]
  exact NumberField.prod_abs_eq_one ha

/-- The normalizing constants in the adelic Fourier transform have product one. -/
theorem transform_normalization_product :
    (∏ᶠ v : Place F, (Real.sqrt (modulus F v (n : LocalField F v)) : ℂ)⁻¹) = 1 := by
  let m (v : Place F) := modulus F v (diagonal F v (n : F))
  have hn : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hm : Function.HasFiniteMulSupport m := eventually_cofinite.mp
    (eventually_place_of_finite (P := fun v => m v = 1) (eventually_diagonal_norm_one hn))
  let S := hm.toFinset
  have hS (v : Place F) (hv : v ∉ S) : m v = 1 := Classical.byContradiction (fun h => hv (hm.mem_toFinset.mpr h))
  have hprod : ∏ v ∈ S, m v = 1 := by
    rw [← finprod_eq_prod _ hm]
    exact diagonal_modulus_product hn
  have hpos (v : Place F) : 0 ≤ m v := by cases v <;> simp [m,modulus]
  have he : (∏ v ∈ S, Real.sqrt (m v)) = 1 := by rw [← Real.sqrt_prod S (fun v _ => hpos v),hprod,Real.sqrt_one]
  have hm' (v : Place F) : modulus F v (n : LocalField F v) = m v := by simp [m]
  simp_rw [hm']
  rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (by
    intro v hv
    by_contra h
    simpa [Function.mem_mulSupport,hS v h] using hv),Finset.prod_inv_distrib,← Complex.ofReal_prod,he]
  simp

private theorem basic_weight_one (w : HeightOneSpectrum (𝓞 F)) :
    (∑' k : ℕ, if (1 : ℝ) = ((w.asIdeal.absNorm : ℝ)^(n*k))⁻¹ then
      (w.asIdeal.absNorm : ℂ)^((n-1)*k) else 0) = 1 := by
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    have hq : 1 < (w.asIdeal.absNorm : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
    have h := one_lt_pow₀ hq (Nat.mul_ne_zero (NeZero.ne n) hk)
    simp [ne_of_gt h]

theorem basic_xChart_unit (w : HeightOneSpectrum (𝓞 F)) (ht : w.asIdeal.absNorm.Coprime n)
    (x y : LocalField F (.inr w)) (hx : ‖x‖ = 1) (hy : ‖y‖ ≤ 1) :
    xChart (d.basic (.inr w)) (x,y) = 1 := by
  have hx₀ : x ≠ 0 := norm_ne_zero_iff.mp (hx ▸ one_ne_zero)
  rw [basic,dif_pos ht]
  simpa [xChart,basicCharts,hx₀,hx,hy] using basic_weight_one (n := n) w

theorem basic_yChart_unit (w : HeightOneSpectrum (𝓞 F)) (ht : w.asIdeal.absNorm.Coprime n)
    (x y : LocalField F (.inr w)) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ = 1) :
    yChart (d.basic (.inr w)) (x,y) = 1 := by
  have hy₀ : y ≠ 0 := norm_ne_zero_iff.mp (hy ▸ one_ne_zero)
  rw [basic,dif_pos ht]
  simpa [yChart,basicCharts,hy₀,hx,hy] using basic_weight_one (n := n) w

theorem eventually_tame :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in cofinite, w.asIdeal.absNorm.Coprime n :=
  (FinitePlace.finite_places_over_degree (K := F) n).eventually_cofinite_notMem.mono
    (fun w hw => FinitePlace.tame_of_degree_not_mem n w hw)

theorem eventually_diagonal_integral (a : F) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in cofinite, ‖diagonal F (.inr w) a‖ ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · exact (eventually_diagonal_norm_one ha).mono fun _ h => h.le

theorem eventually_basic_value (p : RationalPoint F) :
    ∀ᶠ v in cofinite, d.localValue p v (d.basic v) = 1 := by
  apply eventually_place_of_finite
  by_cases hx : p.val.1 ≠ 0
  · filter_upwards [eventually_tame (F := F) (n := n),eventually_diagonal_norm_one hx,
      eventually_diagonal_integral p.val.2] with w ht ha hb
    simpa only [localValue,if_pos hx,diagonalPoint] using d.basic_xChart_unit w ht _ _ ha hb
  · have hy : p.val.2 ≠ 0 := fun h => p.property (Prod.ext (not_ne_iff.mp hx) h)
    filter_upwards [eventually_tame (F := F) (n := n),eventually_diagonal_integral p.val.1,
      eventually_diagonal_norm_one hy] with w ht ha hb
    simpa only [localValue,if_neg hx,diagonalPoint] using d.basic_yChart_unit w ht _ _ ha hb

/-- Product of a scalar family, extended by zero off the families that are one
almost everywhere. This extension is multilinear even on the unrestricted product. -/
private def scalarProduct {ι : Type*} : MultilinearMap ℂ (fun _ : ι => ℂ) ℂ := by
  let prod (f : ι → ℂ) := if ∀ᶠ i in cofinite, f i = 1 then ∏ᶠ i, f i else 0
  have split (f : ι → ℂ) (i : ι) (a : ℂ) :
      prod (Function.update f i a) = a * prod (Function.update f i 1) := by
    have hfin (b : ℂ) : (∀ᶠ j in cofinite, Function.update f i b j = 1) ↔ ∀ᶠ j in cofinite, f j = 1 :=
      eventually_congr ((eventually_cofinite_ne i).mono fun j hj => by rw [Function.update_of_ne hj])
    by_cases hf : ∀ᶠ j in cofinite, f j = 1
    · simp only [prod,(hfin _).2 hf,if_true]
      let s := (eventually_cofinite.mp hf).toFinset.erase i
      have hi : i ∉ s := Finset.notMem_erase i _
      have hprod (b : ℂ) : (∏ᶠ j, Function.update f i b j) = b * ∏ j ∈ s, f j := by
        rw [finprod_eq_prod_of_mulSupport_subset (s := insert i s) _ ?_, Finset.prod_insert hi,
          Function.update_self]
        · congr 1
          exact Finset.prod_congr rfl fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
        · intro j hj
          by_cases e : j = i
          · simp [e]
          · have hj' : f j ≠ 1 := by simpa [Function.mem_mulSupport,Function.update_of_ne e] using hj
            simp [s,e,hj']
      rw [hprod,hprod,one_mul]
    · simp only [prod,if_neg (hf ∘ (hfin _).mp),mul_zero]
  exact MultilinearMap.mk' prod
    (fun f i a b => by rw [split f i (a+b),split f i a,split f i b,add_mul])
    (fun f i c a => by rw [split f i (c • a),split f i a,smul_eq_mul,smul_eq_mul,mul_assoc])

private theorem scalarProduct_apply {ι : Type*} (f : ι → ℂ) (hf : ∀ᶠ i in cofinite, f i = 1) :
    scalarProduct f = ∏ᶠ i, f i := if_pos hf

private def localValueLinear (p : RationalPoint F) (v : Place F) : d.schwartz v →ₗ[ℂ] ℂ where
  toFun := d.localValue p v
  map_add' _ _ := by
    simp only [localValue,xChart,yChart]
    split <;> split <;> first | rfl | simp
  map_smul' _ _ := by
    simp only [localValue,xChart,yChart]
    split <;> split <;> first | rfl | simp

private def productEvaluation (e : ∀ v, d.schwartz v →ₗ[ℂ] ℂ) : d.Schwartz →ₗ[ℂ] ℂ :=
  (PiTensorProduct.lift (scalarProduct.compLinearMap e)).comp d.Schwartz.subtype

private theorem productEvaluation_pure (e : ∀ v, d.schwartz v →ₗ[ℂ] ℂ)
    (f : ∀ v, d.schwartz v) (hf) (he : ∀ᶠ v in cofinite, e v (d.basic v) = 1) :
    d.productEvaluation e (d.pure f hf) = ∏ᶠ v, e v (f v) := by
  change PiTensorProduct.lift _ (PiTensorProduct.tprod ℂ f) = _
  rw [PiTensorProduct.lift.tprod]
  apply scalarProduct_apply
  filter_upwards [hf,he] with v hv hb
  exact hv ▸ hb

/-- Rational evaluation as a linear map on adelic Schwartz sections (§9.2). -/
def evaluation : d.Schwartz →ₗ[ℂ] (RationalPoint F → ℂ) :=
  LinearMap.pi (fun p => d.productEvaluation (d.localValueLinear p))

theorem evaluation_pure (f : ∀ v, d.schwartz v) (hf) (p : RationalPoint F) :
    d.evaluation (d.pure f hf) p = ∏ᶠ v, d.localValue p v (f v) :=
  d.productEvaluation_pure _ f hf (d.eventually_basic_value p)

/-- Extension from restricted pure tensors by multilinearity. -/
theorem exists_evaluation :
    ∃ ev : d.Schwartz →ₗ[ℂ] (RationalPoint F → ℂ),
      ∀ f hf p, ev (d.pure f hf) p = ∏ᶠ v, d.localValue p v (f v) :=
  ⟨d.evaluation,d.evaluation_pure⟩

theorem symbol_reciprocity (x y : Fˣ) :
    (∀ᶠ v in cofinite, d.symbol v (atPlace v x) (atPlace v y) = 1) ∧
    ∏ᶠ v, d.symbol v (atPlace v x) (atPlace v y) = 1 := by
  let H := (existsUnique_hilbert F n d.primitive).exists.choose
  have hH : IsHilbertFamily F n H := (existsUnique_hilbert F n d.primitive).exists.choose_spec
  let e := (Units.coeHom ℂ).comp d.embedding
  have h := hH.unramified x y
  constructor
  · filter_upwards [h] with v hv
    exact (congrArg e hv).trans e.map_one
  · change (∏ᶠ v, e (H v (atPlace v x) (atPlace v y))) = 1
    rw [← e.map_finprod (eventually_cofinite.mp h),hH.reciprocity x y,e.map_one]

/-- Reciprocity gives the same product in the Y chart whenever that chart is available. -/
theorem evaluation_pure_y (f : ∀ v, d.schwartz v) (hf) (p : RationalPoint F) (hy : p.val.2 ≠ 0) :
    d.evaluation (d.pure f hf) p = ∏ᶠ v, yChart (f v) (diagonalPoint p v) := by
  rw [d.evaluation_pure]
  by_cases hx : p.val.1 ≠ 0
  · let a := Units.mk0 p.val.1 hx
    let b := Units.mk0 p.val.2 hy
    let χ (v : Place F) := d.symbol v (atPlace v a) (atPlace v b)
    let Y (v : Place F) := yChart (f v) (diagonalPoint p v)
    have hxy (v : Place F) : d.localValue p v (f v) = χ v * Y v := by
      rw [localValue,if_pos hx]
      exact (xChart_unit (f v).val (atPlace v a) _).trans
        ((d.schwartz_glues v (f v) (atPlace v a) (atPlace v b)).trans
          (congrArg (χ v * ·) (yChart_unit (f v).val _ (atPlace v b)).symm))
    obtain ⟨hs,hp⟩ := d.symbol_reciprocity a b
    have hY : ∀ᶠ v in cofinite, Y v = 1 := by
      filter_upwards [hs,hf,d.eventually_basic_value p] with v hχ hv h1
      have he := hxy v
      rw [hv,h1,show χ v = 1 from hχ,one_mul] at he
      exact he.symm
    simp_rw [hxy]
    rw [finprod_mul_distrib (eventually_cofinite.mp hs) (eventually_cofinite.mp hY),show (∏ᶠ v, χ v) = 1 from hp,one_mul]
  · simp [localValue,hx]

theorem eventually_integral_component (u : Adeles F) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in cofinite, ‖component u (.inr w)‖ ≤ 1 :=
  u.2.property.mono fun w hw => (Valued.toNormedField.norm_le_one_iff (x := u.2 w)).mpr
    ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F w).mp hw)

theorem eventually_unit_component (a : (Adeles F)ˣ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in cofinite, ‖component a.val (.inr w)‖ = 1 := by
  filter_upwards [eventually_integral_component a.val,eventually_integral_component a⁻¹.val] with w h₁ h₂
  let b := Units.map (componentHom (.inr w)).toMonoidHom a
  change ‖b.val‖ = 1
  change ‖(b⁻¹).val‖ ≤ 1 at h₂
  rw [Units.val_inv_eq_inv_val,norm_inv,inv_le_one₀ (norm_pos_iff.mpr b.ne_zero)] at h₂
  exact le_antisymm h₁ h₂

private def xValueLinear (v : Place F) (x : (LocalField F v)ˣ) (y : LocalField F v) :
    d.schwartz v →ₗ[ℂ] ℂ where
  toFun f := f.val.1 x y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def yValueLinear (v : Place F) (x : LocalField F v) (y : (LocalField F v)ˣ) :
    d.schwartz v →ₗ[ℂ] ℂ where
  toFun f := f.val.2 x y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The X chart of an adelic section at an idele and an adele (§9.2). -/
def adelicX (x : (Adeles F)ˣ) (y : Adeles F) : d.Schwartz →ₗ[ℂ] ℂ :=
  d.productEvaluation fun v => d.xValueLinear v (Units.map (componentHom v) x) (component y v)

/-- The Y chart of an adelic section at an adele and an idele (§9.2). -/
def adelicY (x : Adeles F) (y : (Adeles F)ˣ) : d.Schwartz →ₗ[ℂ] ℂ :=
  d.productEvaluation fun v => d.yValueLinear v (component x v) (Units.map (componentHom v) y)

theorem adelicX_pure (x : (Adeles F)ˣ) (y : Adeles F) (f : ∀ v, d.schwartz v) (hf) :
    d.adelicX x y (d.pure f hf) = ∏ᶠ v, (f v).val.1 (Units.map (componentHom v) x) (component y v) := by
  apply d.productEvaluation_pure
  apply eventually_place_of_finite
  filter_upwards [eventually_tame (F := F) (n := n),eventually_unit_component x,eventually_integral_component y]
    with w hw hx hy
  let a := Units.map (componentHom (.inr w)).toMonoidHom x
  have he := d.basic_xChart_unit w hw a.val (component y (.inr w)) hx hy
  change (d.basic (.inr w)).val.1 a (component y (.inr w)) = 1
  simpa only [xChart,dif_pos a.ne_zero,Units.mk0_val] using he

theorem adelicY_pure (x : Adeles F) (y : (Adeles F)ˣ) (f : ∀ v, d.schwartz v) (hf) :
    d.adelicY x y (d.pure f hf) = ∏ᶠ v, (f v).val.2 (component x v) (Units.map (componentHom v) y) := by
  apply d.productEvaluation_pure
  apply eventually_place_of_finite
  filter_upwards [eventually_tame (F := F) (n := n),eventually_integral_component x,eventually_unit_component y]
    with w hw hx hy
  let b := Units.map (componentHom (.inr w)).toMonoidHom y
  have he := d.basic_yChart_unit w hw (component x (.inr w)) b.val hx hy
  change (d.basic (.inr w)).val.2 (component x (.inr w)) b = 1
  simpa only [yChart,dif_pos b.ne_zero,Units.mk0_val] using he


/-- Equality on restricted pure tensors determines a linear functional on the adelic space. -/
theorem ext_pure {L M : d.Schwartz →ₗ[ℂ] ℂ} (h : ∀ f hf, L (d.pure f hf) = M (d.pure f hf)) : L = M := by
  apply LinearMap.ext
  rintro ⟨z,hz⟩
  refine Submodule.span_induction (p := fun x (hx : x ∈ d.Schwartz) => L ⟨x,hx⟩ = M ⟨x,hx⟩) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨f,hf,rfl⟩
    exact h f hf
  · exact (map_zero L).trans (map_zero M).symm
  · intro x y hx hy ex ey
    change L ((⟨x,hx⟩ : d.Schwartz) + ⟨y,hy⟩) = M ((⟨x,hx⟩ : d.Schwartz) + ⟨y,hy⟩)
    rw [map_add,map_add,ex,ey]
  · intro c x hx ex
    change L (c • (⟨x,hx⟩ : d.Schwartz)) = M (c • (⟨x,hx⟩ : d.Schwartz))
    rw [map_smul,map_smul,ex]

theorem evaluation_eq_adelicX (p : RationalPoint F) (hx : p.val.1 ≠ 0) (Φ : d.Schwartz) :
    d.evaluation Φ p = d.adelicX (Units.map (algebraMap F (Adeles F)) (Units.mk0 _ hx))
      (algebraMap F (Adeles F) p.val.2) Φ := by
  let x := Units.map (algebraMap F (Adeles F)).toMonoidHom (Units.mk0 _ hx)
  let y := algebraMap F (Adeles F) p.val.2
  suffices ((LinearMap.proj p).comp d.evaluation) = d.adelicX x y from DFunLike.congr_fun this Φ
  apply d.ext_pure
  intro f hf
  change d.evaluation (d.pure f hf) p = _
  rw [d.evaluation_pure,d.adelicX_pure]
  apply finprod_congr
  intro v
  have hn : diagonal F v p.val.1 ≠ 0 := (map_ne_zero (diagonal F v)).mpr hx
  rw [localValue,if_pos hx]
  refine (xChart_unit (f v).val (Units.mk0 _ hn) _).trans ?_
  have hu : Units.mk0 _ hn = Units.map (componentHom v).toMonoidHom x := by
    apply Units.ext
    cases v <;> rfl
  rw [hu]
  cases v <;> rfl

theorem evaluation_eq_adelicY (p : RationalPoint F) (hy : p.val.2 ≠ 0) (Φ : d.Schwartz) :
    d.evaluation Φ p = d.adelicY (algebraMap F (Adeles F) p.val.1)
      (Units.map (algebraMap F (Adeles F)) (Units.mk0 _ hy)) Φ := by
  let x := algebraMap F (Adeles F) p.val.1
  let y := Units.map (algebraMap F (Adeles F)).toMonoidHom (Units.mk0 _ hy)
  suffices ((LinearMap.proj p).comp d.evaluation) = d.adelicY x y from DFunLike.congr_fun this Φ
  apply d.ext_pure
  intro f hf
  change d.evaluation (d.pure f hf) p = _
  rw [d.evaluation_pure_y _ _ _ hy,d.adelicY_pure]
  apply finprod_congr
  intro v
  have hn : diagonal F v p.val.2 ≠ 0 := (map_ne_zero (diagonal F v)).mpr hy
  refine (yChart_unit (f v).val _ (Units.mk0 _ hn)).trans ?_
  have hu : Units.mk0 _ hn = Units.map (componentHom v).toMonoidHom y := by
    apply Units.ext
    cases v <;> rfl
  rw [hu]
  cases v <;> rfl

end Datum
end MetaplecticPoisson
