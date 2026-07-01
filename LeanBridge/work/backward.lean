import LeanBridge.work.forward
import LeanBridge.work.sams_work

/-!
# Corollary 4.3: the uniformization theorem (existence of the period lattice)

`forward.lean` builds, from a period pair `L` (a lattice `ℤω₁ + ℤω₂`), the elliptic curve
`y² = x³ - (g₂/4) x - (g₃/4)` and shows it is genuinely elliptic (`weierstrassDiscriminant_ne_zero`,
`PeriodPair.weierstrassCurve`).  This file proves the *backward* direction, the lattice-existence
content of

> **Corollary 4.3 (Uniformization).**  For `A, B ∈ ℂ` with `4A³ + 27B² ≠ 0` there is a (unique)
> lattice `Λ` with `g₂(Λ) = -4A` and `g₃(Λ) = -4B`.

i.e. *every* short Weierstrass curve `y² = x³ + A x + B` over `ℂ` arises from a lattice.

## Strategy (following Silverman/Lang)
1. The target curve `E : y² = x³ + A x + B` has `c₄ = -48A`, `Δ = -16(4A³+27B²) ≠ 0`, hence has a
   `j`-invariant `j(E)`.
2. **Theorem 4.1 (surjectivity of `j`)** — provided by `sams_work.lean` as `j_surjective`
   (`Function.Surjective j`, for the modular `j`-function `j = E₄³/Δ`).  It yields `τ ∈ ℍ` with
   `j(τ) = j(E)`; the bridge `weierstrassCurve_j_eq_j` identifies `j(τ)` with `j(ℤ+ℤτ)`.
3. Equating the two `j`-invariants gives the algebraic identity `B² g₂(τ)³ = -4 A³ g₃(τ)²` (`key`).
4. The lattice `ℤ + ℤτ` is then *scaled* by a suitable `α` (`scaledPair`); since `g₂`, `g₃` are
   homogeneous of degrees `-4`, `-6`, the scaling solves `g₂(αΛ) = -4A`, `g₃(αΛ) = -4B`.  The choice
   of `α` splits into the three cases `A = 0`, `B = 0`, `AB ≠ 0` of the textbook proof.

-/

open Complex UpperHalfPlane EisensteinSeries ModularForm PeriodPair
open scoped UpperHalfPlane CongruenceSubgroup MatrixGroups

noncomputable section

/-! ### Theorem 4.1: surjectivity of the `j`-invariant (from `sams_work.lean`) -/

/-- **Bridge to the modular `j`-function.**  The `j`-invariant of the elliptic curve attached to
the lattice `ℤ + ℤτ` agrees with the modular `j`-function `j = E₄³/Δ` of `sams_work.lean`.  Indeed
`(periodPair τ).weierstrassCurve.j = 1728 E₄³/(E₄³ - E₆²)` (`f_eq_j`) and `Δ = (E₄³ - E₆²)/1728`
(`ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`). -/
lemma weierstrassCurve_j_eq_j (τ : ℍ) : (periodPair τ).weierstrassCurve.j = _root_.j τ := by
  have hE : (E₄ τ : ℂ) ^ 3 - E₆ τ ^ 2 ≠ 0 := E₄_cube_sub_E₆_sq_ne_zero τ
  have h1 : (periodPair τ).weierstrassCurve.j
      = 1728 * (E₄ τ : ℂ) ^ 3 / (E₄ τ ^ 3 - E₆ τ ^ 2) := f_eq_j τ
  have h2 : _root_.j τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := by
    show ModularForm.E₄ τ ^ 3 / (CuspForm.discriminant τ) = _
    rw [congrFun CuspForm.coe_discriminant τ]
  rw [h1, h2, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  field_simp

/-! ### Two elementary facts about Weierstrass curves -/

/-- For an elliptic curve over `ℂ`, `j · Δ = c₄³` (clearing the unit `Δ'` from `j = Δ'⁻¹ c₄³`). -/
lemma WeierstrassCurve.j_mul_Δ (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    W.j * W.Δ = W.c₄ ^ 3 := by
  have h := W.Δ'.inv_mul
  rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ']
  linear_combination W.c₄ ^ 3 * h

/-! ### The scaled lattice `α·(ℤ + ℤτ)` -/

/-- `α` and `α τ` are `ℝ`-linearly independent whenever `α ≠ 0` (scaling the basis `1, τ`). -/
lemma linearIndependent_scaled (τ : ℍ) {α : ℂ} (hα : α ≠ 0) :
    LinearIndependent ℝ ![α, α * (τ : ℂ)] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Complex.real_smul, Complex.real_smul] at hst
  have h1 : (s : ℂ) + (t : ℂ) * (τ : ℂ) = 0 := by
    rcases mul_eq_zero.mp (show α * ((s : ℂ) + (t : ℂ) * (τ : ℂ)) = 0 by linear_combination hst)
      with h | h
    · exact absurd h hα
    · exact h
  exact (LinearIndependent.pair_iff.mp (linearIndependent_one_coe τ)) s t (by
    rw [Complex.real_smul, Complex.real_smul]; linear_combination h1)

/-- The period pair `(α, α τ)`, whose lattice is `α·(ℤ + ℤτ)`. -/
def scaledPair (τ : ℍ) {α : ℂ} (hα : α ≠ 0) : PeriodPair where
  ω₁ := α
  ω₂ := α * (τ : ℂ)
  indep := linearIndependent_scaled τ hα

@[simp] lemma scaledPair_ω₁ (τ : ℍ) {α : ℂ} (hα : α ≠ 0) : (scaledPair τ hα).ω₁ = α := rfl

@[simp] lemma scaledPair_ω₂ (τ : ℍ) {α : ℂ} (hα : α ≠ 0) :
    (scaledPair τ hα).ω₂ = α * (τ : ℂ) := rfl

/-- **Homogeneity of `G`.** Scaling the lattice by `α` scales `Gₙ` by `α⁻ⁿ`. -/
lemma G_scaledPair (τ : ℍ) {α : ℂ} (hα : α ≠ 0) (n : ℕ) :
    (scaledPair τ hα).G n = (α ^ n)⁻¹ * (periodPair τ).G n := by
  obtain ⟨e, he⟩ := exists_scalingEquiv_aux (scaledPair τ hα) τ (Equiv.refl (ℤ × ℤ)) (by
    intro a b
    simp only [scaledPair_ω₁, scaledPair_ω₂, periodPair_ω₁, periodPair_ω₂, Equiv.refl_apply]
    field_simp)
  have hsmul := G_eq_smul_of_latticeEquiv e he n
  rw [scaledPair_ω₁, inv_pow, inv_inv] at hsmul
  rw [hsmul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hα), one_mul]

/-- `g₂` is homogeneous of degree `-4`: `g₂(α·Λ) = α⁻⁴ g₂(Λ)`. -/
lemma g₂_scaledPair (τ : ℍ) {α : ℂ} (hα : α ≠ 0) :
    (scaledPair τ hα).g₂ = (α ^ 4)⁻¹ * (periodPair τ).g₂ := by
  rw [PeriodPair.g₂, G_scaledPair τ hα 4, PeriodPair.g₂]; ring

/-- `g₃` is homogeneous of degree `-6`: `g₃(α·Λ) = α⁻⁶ g₃(Λ)`. -/
lemma g₃_scaledPair (τ : ℍ) {α : ℂ} (hα : α ≠ 0) :
    (scaledPair τ hα).g₃ = (α ^ 6)⁻¹ * (periodPair τ).g₃ := by
  rw [PeriodPair.g₃, G_scaledPair τ hα 6, PeriodPair.g₃]; ring

/-! ### The target curve `y² = x³ + A x + B` -/

/-- The short Weierstrass curve `y² = x³ + A x + B`. -/
def targetCurve (A B : ℂ) : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := A
  a₆ := B

lemma targetCurve_Δ (A B : ℂ) : (targetCurve A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  simp only [targetCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma targetCurve_c₄ (A B : ℂ) : (targetCurve A B).c₄ = -48 * A := by
  simp only [targetCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

/-! ### Corollary 4.3 (existence of the period lattice) -/

/-- **Corollary 4.3 (existence part).**  For `A, B ∈ ℂ` with `4A³ + 27B² ≠ 0`, there is a period
lattice `Λ` (i.e. a `PeriodPair`) whose Weierstrass invariants are `g₂(Λ) = -4A` and
`g₃(Λ) = -4B`.  Equivalently, the period-pair curve of `Λ` is exactly `y² = x³ + A x + B`. -/
theorem exists_periodPair_g₂_g₃ {A B : ℂ} (h : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    ∃ L : PeriodPair, L.g₂ = -4 * A ∧ L.g₃ = -4 * B := by
  -- The target curve is elliptic, so it has a `j`-invariant.
  have hΔ : (targetCurve A B).Δ ≠ 0 := by
    rw [targetCurve_Δ]; exact mul_ne_zero (by norm_num) h
  haveI : (targetCurve A B).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  -- Theorem 4.1 (`sams_work.lean`): pick `τ` with `j(τ) = j(E)`, then bridge to `j(ℤ+ℤτ)`.
  obtain ⟨τ, hτ0⟩ := j_surjective (targetCurve A B).j
  have hτ : (periodPair τ).weierstrassCurve.j = (targetCurve A B).j := by
    rw [weierstrassCurve_j_eq_j, hτ0]
  -- The lattice `ℤ + ℤτ` has nonzero discriminant.
  have hΔτ : (periodPair τ).g₂ ^ 3 - 27 * (periodPair τ).g₃ ^ 2 ≠ 0 := by
    have := weierstrassDiscriminant_periodPair_ne_zero τ
    rwa [weierstrassDiscriminant] at this
  -- The algebraic identity coming from `j(ℤ+ℤτ) = j(E)`.
  have key : B ^ 2 * (periodPair τ).g₂ ^ 3 + 4 * A ^ 3 * (periodPair τ).g₃ ^ 2 = 0 := by
    have hjpp : (periodPair τ).weierstrassCurve.j *
        ((periodPair τ).g₂ ^ 3 - 27 * (periodPair τ).g₃ ^ 2) = (12 * (periodPair τ).g₂) ^ 3 := by
      have hh := (periodPair τ).weierstrassCurve.j_mul_Δ
      rwa [PeriodPair.weierstrassCurve_Δ, weierstrassDiscriminant, weierstrassCurve_c₄] at hh
    have hjE : (targetCurve A B).j * (-16 * (4 * A ^ 3 + 27 * B ^ 2)) = (-48 * A) ^ 3 := by
      have hh := (targetCurve A B).j_mul_Δ
      rwa [targetCurve_Δ, targetCurve_c₄] at hh
    have hmaster : (12 * (periodPair τ).g₂) ^ 3 * (-16 * (4 * A ^ 3 + 27 * B ^ 2))
        = (-48 * A) ^ 3 * ((periodPair τ).g₂ ^ 3 - 27 * (periodPair τ).g₃ ^ 2) := by
      rw [← hjpp, ← hjE, hτ]; ring
    linear_combination hmaster / (-746496)
  -- Case analysis on `A`, `B`, exactly as in the textbook proof.
  rcases eq_or_ne A 0 with hA | hA
  · -- `A = 0`: then `j = 0`, so `g₂(τ) = 0`; scale to fix `g₃`.
    subst hA
    have hB : B ≠ 0 := by rintro rfl; norm_num at h
    have hb : (-4 * B : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hB
    have hg₂0 : (periodPair τ).g₂ = 0 := by
      have h2 : B ^ 2 * (periodPair τ).g₂ ^ 3 = 0 := by linear_combination key
      rcases mul_eq_zero.mp h2 with hh | hh
      · exact absurd ((pow_eq_zero_iff (by norm_num)).mp hh) hB
      · exact (pow_eq_zero_iff (by norm_num)).mp hh
    have hg₃ne : (periodPair τ).g₃ ≠ 0 := by
      intro hh; apply hΔτ; rw [hg₂0, hh]; ring
    obtain ⟨α, hα6⟩ :=
      IsAlgClosed.exists_pow_nat_eq ((periodPair τ).g₃ / (-4 * B)) (n := 6) (by norm_num)
    have hα : α ≠ 0 := by
      rintro rfl; rw [zero_pow (by norm_num)] at hα6; exact (div_ne_zero hg₃ne hb) hα6.symm
    have hP6 : α ^ 6 * (-4 * B) = (periodPair τ).g₃ := by rw [hα6, div_mul_cancel₀ _ hb]
    refine ⟨scaledPair τ hα, ?_, ?_⟩
    · rw [g₂_scaledPair τ hα, hg₂0, mul_zero]; ring
    · rw [g₃_scaledPair τ hα, ← hP6, inv_mul_cancel_left₀ (pow_ne_zero 6 hα)]
  · rcases eq_or_ne B 0 with hB | hB
    · -- `B = 0`: then `j = 1728`, so `g₃(τ) = 0`; scale to fix `g₂`.
      subst hB
      have ha : (-4 * A : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hA
      have hg₃0 : (periodPair τ).g₃ = 0 := by
        have h2 : 4 * A ^ 3 * (periodPair τ).g₃ ^ 2 = 0 := by linear_combination key
        rcases mul_eq_zero.mp h2 with hh | hh
        · exact absurd hh (mul_ne_zero (by norm_num) (pow_ne_zero 3 hA))
        · exact (pow_eq_zero_iff (by norm_num)).mp hh
      have hg₂ne : (periodPair τ).g₂ ≠ 0 := by
        intro hh; apply hΔτ; rw [hh, hg₃0]; ring
      obtain ⟨α, hα4⟩ :=
        IsAlgClosed.exists_pow_nat_eq ((periodPair τ).g₂ / (-4 * A)) (n := 4) (by norm_num)
      have hα : α ≠ 0 := by
        rintro rfl; rw [zero_pow (by norm_num)] at hα4; exact (div_ne_zero hg₂ne ha) hα4.symm
      have hP4 : α ^ 4 * (-4 * A) = (periodPair τ).g₂ := by rw [hα4, div_mul_cancel₀ _ ha]
      refine ⟨scaledPair τ hα, ?_, ?_⟩
      · rw [g₂_scaledPair τ hα, ← hP4, inv_mul_cancel_left₀ (pow_ne_zero 4 hα)]
      · rw [g₃_scaledPair τ hα, hg₃0, mul_zero]; ring
    · -- `A ≠ 0`, `B ≠ 0`: both `g₂(τ)` and `g₃(τ)` are nonzero; scale by `α² = A g₃ / (B g₂)`.
      have hg₂ne : (periodPair τ).g₂ ≠ 0 := by
        intro hh
        have h2 : 4 * A ^ 3 * (periodPair τ).g₃ ^ 2 = 0 := by rw [hh] at key; linear_combination key
        have hg3 : (periodPair τ).g₃ = 0 := by
          rcases mul_eq_zero.mp h2 with h' | h'
          · exact absurd h' (mul_ne_zero (by norm_num) (pow_ne_zero 3 hA))
          · exact (pow_eq_zero_iff (by norm_num)).mp h'
        apply hΔτ; rw [hh, hg3]; ring
      have hg₃ne : (periodPair τ).g₃ ≠ 0 := by
        intro hh
        have h2 : B ^ 2 * (periodPair τ).g₂ ^ 3 = 0 := by rw [hh] at key; linear_combination key
        have hg2 : (periodPair τ).g₂ = 0 := by
          rcases mul_eq_zero.mp h2 with h' | h'
          · exact absurd ((pow_eq_zero_iff (by norm_num)).mp h') hB
          · exact (pow_eq_zero_iff (by norm_num)).mp h'
        exact hg₂ne hg2
      set β := A * (periodPair τ).g₃ / (B * (periodPair τ).g₂) with hβ
      have hβne : β ≠ 0 := by
        rw [hβ]; exact div_ne_zero (mul_ne_zero hA hg₃ne) (mul_ne_zero hB hg₂ne)
      obtain ⟨α, hα2⟩ := IsAlgClosed.exists_pow_nat_eq β (n := 2) (by norm_num)
      have hα : α ≠ 0 := fun h0 => hβne (by rw [← hα2, h0]; ring)
      have hP4 : α ^ 4 * (-4 * A) = (periodPair τ).g₂ := by
        have h4 : α ^ 4 = β ^ 2 := by rw [← hα2]; ring
        rw [h4, hβ]; field_simp; linear_combination -key
      have hP6 : α ^ 6 * (-4 * B) = (periodPair τ).g₃ := by
        have h6 : α ^ 6 = β ^ 3 := by rw [← hα2]; ring
        rw [h6, hβ]; field_simp; linear_combination -key
      refine ⟨scaledPair τ hα, ?_, ?_⟩
      · rw [g₂_scaledPair τ hα, ← hP4, inv_mul_cancel_left₀ (pow_ne_zero 4 hα)]
      · rw [g₃_scaledPair τ hα, ← hP6, inv_mul_cancel_left₀ (pow_ne_zero 6 hα)]
