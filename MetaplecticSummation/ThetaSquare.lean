import MetaplecticSummation.AdelicFourier
import MetaplecticSummation.Inversion

/-! Rational reindexing of the theta series under the square of the adelic Fourier transform. -/
noncomputable section
namespace MetaplecticPoisson.Datum
open NumberField Filter
open Classical
variable {F : Type} [Field F] [NumberField F] {n : ℕ} [NeZero n] (d : Datum F n)

/-- Action of the rational diagonal matrix on nonzero rational vectors. -/
def torusPoint (a : Fˣ) (z : RationalPoint F) : RationalPoint F :=
  ⟨(a.val*z.val.1,z.val.2/a.val),fun h => z.property (Prod.ext
    ((mul_eq_zero.mp (congrArg Prod.fst h)).resolve_left a.ne_zero)
    ((div_eq_zero_iff.mp (congrArg Prod.snd h)).resolve_right a.ne_zero))⟩

private def torusPointEquiv (a : Fˣ) : Equiv.Perm (RationalPoint F) where
  toFun := torusPoint a
  invFun := torusPoint a⁻¹
  left_inv z := by apply Subtype.ext; ext <;> simp [torusPoint,Units.val_inv_eq_inv_val]
  right_inv z := by apply Subtype.ext; ext <;> simp [torusPoint,Units.val_inv_eq_inv_val]

omit [NeZero n] in
private theorem mapped_sign (v : Place F) :
    atPlace v ((-1:Fˣ)^(n+1)) = (-1:(LocalField F v)ˣ)^(n+1) := by
  apply Units.ext
  simp [atPlace,Units.val_pow_eq_pow_val]

private theorem evaluation_square_pure (f : ∀ v, d.schwartz v) (hf) (z : RationalPoint F) :
    d.evaluation (d.adelicFourier (d.adelicFourier (d.pure f hf))) z =
      d.evaluation (d.pure f hf) (torusPoint ((-1:Fˣ)^(n+1)) z) := by
  let a := (-1:Fˣ)^(n+1)
  let b := torusPoint a z
  let T (v : Place F) := d.fourier v (d.fourier v (f v))
  have hT (v : Place F) : (T v).val = d.torusCharts v (atPlace v a) (f v).val := by
    rw [show atPlace v a = _ from mapped_sign (n := n) v]
    exact d.schwartz_fourier_square v _
  rw [d.adelicFourier_pure,d.adelicFourier_pure,d.evaluation_pure,d.evaluation_pure]
  change (∏ᶠ v, d.localValue z v (T v)) = ∏ᶠ v, d.localValue b v (f v)
  have hb : ∀ᶠ v in cofinite, d.localValue b v (f v) = 1 := by
    filter_upwards [hf,d.eventually_basic_value b] with v h h'
    exact h ▸ h'
  by_cases hx : z.val.1 ≠ 0
  · let x := Units.mk0 z.val.1 hx
    have hb₁ : b.val.1 ≠ 0 := mul_ne_zero a.ne_zero hx
    let χ (v : Place F) := d.symbol v (atPlace v (-x)) (atPlace v a)
    have he (v : Place F) : d.localValue z v (T v) = χ v * d.localValue b v (f v) := by
      let A := atPlace v a
      let X := atPlace v x
      have hn : diagonal F v z.val.1 ≠ 0 := (map_ne_zero _).mpr hx
      have hm : diagonal F v b.val.1 ≠ 0 := (map_ne_zero _).mpr hb₁
      have hh : Units.mk0 _ hm = A*X := Units.ext (map_mul _ _ _)
      have hs : χ v = d.symbol v X A * d.symbol v (-1) A := by
        have hu : atPlace v (-x) = X*(-1) := Units.ext (by simp [X,atPlace])
        change (d.unitPairing v (atPlace v (-x)) A).val = _
        rw [hu,map_mul,MonoidHom.mul_apply,Units.val_mul]
        rfl
      simp only [localValue,if_pos hx,if_pos hb₁,diagonalPoint,xChart,dif_pos hn,dif_pos hm,hT,torusCharts,hh]
      rw [hs,show Units.mk0 _ hn = X from Units.ext rfl]
      change _ * (f v).val.1 _ (_ / _) = _ * (f v).val.1 _ (diagonal F v (z.val.2/a.val))
      rw [map_div₀]
      rfl
    simp_rw [he,← show ∀ v, d.symbol v (atPlace v (-x)) (atPlace v a) = χ v from fun _ => rfl]
    obtain ⟨hχ,eχ⟩ := d.symbol_reciprocity (-x) a
    rw [finprod_mul_distrib (eventually_cofinite.mp hχ) (eventually_cofinite.mp hb),eχ,one_mul]
  · have hy : z.val.2 ≠ 0 := fun h => z.property (Prod.ext (not_ne_iff.mp hx) h)
    let y := Units.mk0 z.val.2 hy
    have hb₁ : b.val.1 = 0 := by simp [b,torusPoint,not_ne_iff.mp hx]
    have hb₂ : b.val.2 ≠ 0 := div_ne_zero hy a.ne_zero
    have he (v : Place F) : d.localValue z v (T v) =
        d.symbol v (atPlace v a) (atPlace v y) * d.localValue b v (f v) := by
      let A := atPlace v a
      let Y := atPlace v y
      have hn : diagonal F v z.val.2 ≠ 0 := (map_ne_zero _).mpr hy
      have hm : diagonal F v b.val.2 ≠ 0 := (map_ne_zero _).mpr hb₂
      have hh : Units.mk0 _ hm = Y/A := by
        apply Units.ext
        rw [Units.val_div_eq_div_val]
        exact map_div₀ (diagonal F v) z.val.2 a.val
      simp only [localValue,if_neg hx,if_neg (not_not.mpr hb₁),diagonalPoint,yChart,dif_pos hn,dif_pos hm,hT,torusCharts,hh]
      rw [show Units.mk0 _ hn = Y from Units.ext rfl]
      change _ * (f v).val.2 (_ * _) _ = _ * (f v).val.2 (diagonal F v (a.val*z.val.1)) _
      rw [map_mul]
      rfl
    simp_rw [he]
    obtain ⟨hχ,eχ⟩ := d.symbol_reciprocity a y
    rw [finprod_mul_distrib (eventually_cofinite.mp hχ) (eventually_cofinite.mp hb),eχ,one_mul]

/-- The square acts on rational arguments by the rational diagonal matrix
with entries ε and ε⁻¹, where ε = (−1)^(n+1). -/
theorem evaluation_fourier_square (Φ : d.Schwartz) (z : RationalPoint F) :
    d.evaluation (d.adelicFourier (d.adelicFourier Φ)) z =
      d.evaluation Φ (torusPoint ((-1:Fˣ)^(n+1)) z) := by
  let ev (x : RationalPoint F) := (LinearMap.proj x).comp d.evaluation
  have h : ((ev z).comp d.adelicFourier).comp d.adelicFourier = ev (torusPoint ((-1:Fˣ)^(n+1)) z) :=
    d.ext_pure fun f hf => d.evaluation_square_pure f hf z
  exact LinearMap.congr_fun h Φ

theorem theta_fourier_square (Φ : d.Schwartz) :
    (∑' z, d.evaluation (d.adelicFourier (d.adelicFourier Φ)) z) = ∑' z, d.evaluation Φ z := by
  simp_rw [d.evaluation_fourier_square]
  exact (torusPointEquiv ((-1:Fˣ)^(n+1))).tsum_eq _

end MetaplecticPoisson.Datum
