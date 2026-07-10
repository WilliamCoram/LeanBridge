import LeanBridge.NonSlop.det_ne_zero
import LeanBridge.NonSlop.j_surj

/-!
  In this file we attatch an elliptic curve to a period lattice and state the uniformisation map.
-/

open PeriodPair Complex UpperHalfPlane EisensteinSeries ModularForm

/-- The (short) **Weierstrass curve** `y² = x³ - (g₂/4) x - (g₃/4)` attached to a period pair `L`.
It is the image of the Weierstrass equation `℘'² = 4℘³ - g₂℘ - g₃` under `(x, y) = (℘, ½ ℘')`. -/
noncomputable
def PeriodPair.weierstrassCurve (L : PeriodPair) : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -L.g₂ / 4
  a₆ := -L.g₃ / 4

lemma PeriodPair.weierstrassCurve_Δ (L : PeriodPair) :
    L.weierstrassCurve.Δ = weierstrassDiscriminant L := by
  grind [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, PeriodPair.weierstrassCurve]

instance (L : PeriodPair) : L.weierstrassCurve.IsElliptic where
  isUnit := by simpa [PeriodPair.weierstrassCurve_Δ] using
    isUnit_iff_ne_zero.mpr (weierstrassDiscriminant_ne_zero L)

lemma PeriodPair.coe_weierstrassCurve_Δ' (L : PeriodPair) :
    L.weierstrassCurve.Δ' = weierstrassDiscriminant L := by
  rw [WeierstrassCurve.coe_Δ', PeriodPair.weierstrassCurve_Δ]

lemma PeriodPair.weierstrassCurve_c₄ (L : PeriodPair) : L.weierstrassCurve.c₄ = 12 * L.g₂ := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    PeriodPair.weierstrassCurve]
  ring

lemma PeriodPair.weierstrassCurve_c₆ (L : PeriodPair) : L.weierstrassCurve.c₆ = 216 * L.g₃ := by
  simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    PeriodPair.weierstrassCurve]
  ring

theorem PeriodPair.weierstrassCurve_j (L : PeriodPair) :
    L.weierstrassCurve.j = 1728 * L.g₂ ^ 3 / weierstrassDiscriminant L := by
  grind [WeierstrassCurve.j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul, WeierstrassCurve.coe_Δ',
    PeriodPair.weierstrassCurve_Δ, PeriodPair.weierstrassCurve_c₄]

noncomputable
def periodPair_j := fun τ => (periodPair τ).weierstrassCurve.j

lemma periodPair_j_eq_j (τ : ℍ) : periodPair_j τ = j τ := by
  have : (riemannZeta 4 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have : (120 * riemannZeta 4 : ℂ) ≠ 0 := mul_ne_zero (by norm_num) this
  have : (120 * riemannZeta 4 : ℂ) ^ 3 ≠ 0 := pow_ne_zero _ this
  have : (E₄ τ : ℂ) ^ 3 - E₆ τ ^ 2 ≠ 0 := E₄_cube_sub_E₆_sq_ne_zero τ
  simp only [j, periodPair_j, PeriodPair.weierstrassCurve_j, weierstrassDiscriminant_periodPair,
    g₂_periodPair, mul_pow, CuspForm.coe_discriminant, discriminant_eq_E₄_cube_sub_E₆_sq]
  field_simp

open WeierstrassCurve.Affine in
lemma PeriodPair.weierstrassCurve_equation (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    L.weierstrassCurve.toAffine.Equation (℘[L] z) (℘'[L] z / 2) := by
  rw [WeierstrassCurve.Affine.equation_iff, PeriodPair.weierstrassCurve]
  linear_combination (L.derivWeierstrassP_sq z hz) / 4

open Classical in
noncomputable
def PeriodPair.toPoint (L : PeriodPair) (z : ℂ) : L.weierstrassCurve.toAffine.Point :=
  if hz : z ∈ L.lattice then 0
  else .some (℘[L] z) (℘'[L] z / 2)
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp (L.weierstrassCurve_equation hz))

lemma PeriodPair.toPoint_add_mem (L : PeriodPair) (z : ℂ) (l : L.lattice) :
    L.toPoint (z + l) = L.toPoint z := by
  by_cases hz : z ∈ L.lattice
  · simp only [PeriodPair.toPoint, dif_pos (add_mem hz l.2), dif_pos hz]
  · have : z + (l : ℂ) ∉ L.lattice := fun h ↦ hz (by simpa using sub_mem h l.2)
    simp only [PeriodPair.toPoint, dif_neg this, dif_neg hz]
    congr 1
    · exact L.weierstrassP_add_coe z l
    · rw [L.derivWeierstrassP_add_coe z l]

lemma PeriodPair.toPoint_neg (L : PeriodPair) (z : ℂ) : L.toPoint (-z) = - L.toPoint z := by
  by_cases hz : z ∈ L.lattice
  · simp only [PeriodPair.toPoint, dif_pos (neg_mem hz), dif_pos hz, neg_zero]
  · have : -z ∉ L.lattice := fun h => hz (by simpa using neg_mem h)
    simp only [PeriodPair.toPoint, dif_neg this, dif_neg hz, WeierstrassCurve.Affine.Point.neg_some]
    congr 1
    · exact L.weierstrassP_neg z
    · rw [WeierstrassCurve.Affine.negY, L.derivWeierstrassP_neg z, PeriodPair.weierstrassCurve]
      ring

/-- The uniformization map `φ : ℂ/Λ → E(ℂ)`. -/
noncomputable
def PeriodPair.uniformization (L : PeriodPair) :
    (ℂ ⧸ L.lattice.toAddSubgroup) → L.weierstrassCurve.toAffine.Point := by
  refine fun q ↦ Quotient.liftOn' q L.toPoint ?_
  intro a b hab
  rw [QuotientAddGroup.leftRel_apply, Submodule.mem_toAddSubgroup] at hab
  have h := L.toPoint_add_mem a ⟨b - a, by simpa [sub_eq_neg_add] using hab⟩
  simpa [add_sub_cancel] using h.symm

@[simp] lemma PeriodPair.uniformization_mk (L : PeriodPair) (z : ℂ) :
    L.uniformization (QuotientAddGroup.mk z) = L.toPoint z := rfl

/-- `φ(O) = O`: the identity `0 ∈ ℂ/Λ` maps to the point at infinity. -/
@[simp] lemma PeriodPair.uniformization_zero (L : PeriodPair) :
    L.uniformization 0 = 0 := by
  show L.toPoint 0 = _
  simp only [PeriodPair.toPoint, dif_pos (zero_mem _)]

lemma PeriodPair.uniformization_neg (L : PeriodPair) (q : ℂ ⧸ L.lattice.toAddSubgroup) :
    L.uniformization (- q) = - L.uniformization q := by
  induction q using QuotientAddGroup.induction_on with
  | _ z =>
    have : (- (QuotientAddGroup.mk z) : ℂ ⧸ L.lattice.toAddSubgroup)
        = QuotientAddGroup.mk (- z) := (map_neg (QuotientAddGroup.mk' _) z).symm
    rw [this, uniformization_mk, uniformization_mk, L.toPoint_neg]

/- The uniformization map is a ring hom. -/
noncomputable
def uniformizationHom (L : PeriodPair) :
    (ℂ ⧸ L.lattice.toAddSubgroup) →+ L.weierstrassCurve.toAffine.Point where
  toFun := L.uniformization
  map_zero' := L.uniformization_zero
  map_add' := sorry -- done in the work folder (but 100% slop)
