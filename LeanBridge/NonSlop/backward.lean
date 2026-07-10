import LeanBridge.NonSlop.uniformisation
import LeanBridge.NonSlop.j_surj
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
  In this file we do the backwards of what is in the uniformisation file. That is given a short
  Weierstrass equation we compute a lattice associated to it.
-/

open Complex UpperHalfPlane EisensteinSeries ModularForm PeriodPair

lemma WeierstrassCurve.j_mul_Δ (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    W.j * W.Δ = W.c₄ ^ 3 := by
  rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ']
  linear_combination W.c₄ ^ 3 * W.Δ'.inv_mul

/-- If `x * y ^ n = 0` with `x ≠ 0` and `n ≠ 0`, then `y = 0`. -/
lemma eq_zero_of_mul_pow_eq_zero (x : ℂ) {y : ℂ} (n : ℕ) (hn : n ≠ 0) (hx : x ≠ 0)
    (h : x * y ^ n = 0) : y = 0 :=
  (pow_eq_zero_iff hn).mp ((mul_eq_zero.mp h).resolve_left hx)

/-- In `ℂ` the equation `α ^ n * d = c` has a nonzero solution `α`, for any `c, d ≠ 0` and
`n ≠ 0`. -/
lemma exists_pow_mul_eq (n : ℕ) (hn : n ≠ 0) (d : ℂ) {c : ℂ} (hc : c ≠ 0) (hd : d ≠ 0) :
    ∃ α : ℂ, α ≠ 0 ∧ α ^ n * d = c := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (c / d) (Nat.pos_of_ne_zero hn)
  refine ⟨α, fun h0 ↦ hc ?_, by rw [hα, div_mul_cancel₀ _ hd]⟩
  rw [h0, zero_pow hn] at hα
  exact (div_eq_zero_iff.mp hα.symm).resolve_right hd

/-- The identity `j ⬝ Δ = c₄ ^ 3` for the curve attached to a period pair, in terms of `g₂`
and `g₃`. -/
lemma PeriodPair.weierstrassCurve_j_mul_Δ (L : PeriodPair) :
    L.weierstrassCurve.j * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = (12 * L.g₂) ^ 3 := by
  have h := L.weierstrassCurve.j_mul_Δ
  rwa [PeriodPair.weierstrassCurve_Δ, weierstrassDiscriminant, weierstrassCurve_c₄] at h

/-- `g₂` and `g₃` of a period pair cannot vanish simultaneously, since the discriminant is
nonzero. -/
lemma PeriodPair.g₃_ne_zero_of_g₂_eq_zero (L : PeriodPair) (h₂ : L.g₂ = 0) : L.g₃ ≠ 0 :=
  fun h₃ ↦ weierstrassDiscriminant_ne_zero L (by rw [weierstrassDiscriminant, h₂, h₃]; ring)

/-- `g₂` and `g₃` of a period pair cannot vanish simultaneously, since the discriminant is
nonzero. -/
lemma PeriodPair.g₂_ne_zero_of_g₃_eq_zero (L : PeriodPair) (h₃ : L.g₃ = 0) : L.g₂ ≠ 0 :=
  fun h₂ ↦ weierstrassDiscriminant_ne_zero L (by rw [weierstrassDiscriminant, h₂, h₃]; ring)

lemma linearIndependent_scaled (τ : ℍ) {α : ℂ} (hα : α ≠ 0) :
    LinearIndependent ℝ ![α, α * (τ : ℂ)] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Complex.real_smul, Complex.real_smul] at hst
  have : (s : ℂ) + (t : ℂ) * (τ : ℂ) = 0 := by
    rcases mul_eq_zero.mp (show α * (s + t * τ) = 0 by grind) with h | h
    · exact absurd h hα
    · exact h
  refine (LinearIndependent.pair_iff.mp (linearIndependent_one_coe τ)) s t ?_
  rw [Complex.real_smul, Complex.real_smul]; grind

-- maybe should be uniformised with the smul inside L_L_bar_real?
-- this is Sayebs code which I have not maintained

/-- The period pair `(α, α τ)`, whose lattice is `α·(ℤ + ℤτ)`. -/
def scaledPair (τ : ℍ) {α : ℂ} (hα : α ≠ 0) : PeriodPair where
  ω₁ := α
  ω₂ := α * (τ : ℂ)
  indep := linearIndependent_scaled τ hα

lemma scaledPair_ω₁ (τ : ℍ) {α : ℂ} (hα : α ≠ 0) : (scaledPair τ hα).ω₁ = α := rfl

lemma scaledPair_ω₂ (τ : ℍ) {α : ℂ} (hα : α ≠ 0) : (scaledPair τ hα).ω₂ = α * (τ : ℂ) := rfl

/-- The normalised period ratio of `scaledPair τ hα` is `τ` itself. -/
lemma scaledPair_τ (τ : ℍ) {α : ℂ} (hα : α ≠ 0) : (scaledPair τ hα).τ = τ := by
  have hdiv : (scaledPair τ hα).ω₂ / (scaledPair τ hα).ω₁ = (τ : ℂ) := by
    rw [scaledPair_ω₁, scaledPair_ω₂, mul_div_cancel_left₀ _ hα]
  refine UpperHalfPlane.ext ?_
  rw [coe_τ_of_im_pos _ (by rw [hdiv]; exact τ.im_pos), hdiv]

lemma G_scaledPair (τ : ℍ) {α : ℂ} (hα : α ≠ 0) (n : ℕ) :
    (scaledPair τ hα).G n = (α ^ n)⁻¹ * (periodPair τ).G n := by
  have := G_eq_smul_of_latticeEquiv (scalingEquiv (scaledPair τ hα))
    (scalingEquiv_apply (scaledPair τ hα)) n
  rw [scaledPair_τ τ hα, scaledPair_ω₁, inv_pow, inv_inv] at this
  rw [this, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hα), one_mul]

lemma g₂_scaledPair (τ : ℍ) {α : ℂ} (hα : α ≠ 0) :
    (scaledPair τ hα).g₂ = (α ^ 4)⁻¹ * (periodPair τ).g₂ := by
  rw [PeriodPair.g₂, G_scaledPair τ hα 4, PeriodPair.g₂]; ring

lemma g₃_scaledPair (τ : ℍ) {α : ℂ} (hα : α ≠ 0) :
    (scaledPair τ hα).g₃ = (α ^ 6)⁻¹ * (periodPair τ).g₃ := by
  rw [PeriodPair.g₃, G_scaledPair τ hα 6, PeriodPair.g₃]; ring

/-- A solution `α` of `α⁴ · (-4A) = g₂(ℤ+ℤτ)` and `α⁶ · (-4B) = g₃(ℤ+ℤτ)` yields the lattice
`α·(ℤ+ℤτ)` with invariants `g₂ = -4A` and `g₃ = -4B`. -/
lemma scaledPair_g₂_g₃ (τ : ℍ) {α : ℂ} (hα : α ≠ 0) {A B : ℂ}
    (h₂ : α ^ 4 * (-4 * A) = (periodPair τ).g₂) (h₃ : α ^ 6 * (-4 * B) = (periodPair τ).g₃) :
    (scaledPair τ hα).g₂ = -4 * A ∧ (scaledPair τ hα).g₃ = -4 * B :=
  ⟨by rw [g₂_scaledPair τ hα, ← h₂, inv_mul_cancel_left₀ (pow_ne_zero 4 hα)],
    by rw [g₃_scaledPair τ hα, ← h₃, inv_mul_cancel_left₀ (pow_ne_zero 6 hα)]⟩

/-- The short Weierstrass curve `y² = x³ + A x + B`. -/
def shortWeierstrassCurve (A B : ℂ) : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := A
  a₆ := B

lemma shortWeierstrassCurve_Δ (A B : ℂ) : (shortWeierstrassCurve A B).Δ =
    -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  simp only [shortWeierstrassCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma shortWeierstrassCurve_Δ_neZero {A B : ℂ} (h : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)  :
    (shortWeierstrassCurve A B).Δ ≠ 0 := by
  rw [shortWeierstrassCurve_Δ]
  exact mul_ne_zero (by norm_num) h

lemma shortWeierstrasCurve_elliptic {A B : ℂ} (h : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    (shortWeierstrassCurve A B).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (shortWeierstrassCurve_Δ_neZero h)⟩

lemma shortWeierstrassCurve_c₄ (A B : ℂ) : (shortWeierstrassCurve A B).c₄ = -48 * A := by
  simp only [shortWeierstrassCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

/-- The identity `j ⬝ Δ = c₄ ^ 3` for the curve `y² = x³ + Ax + B`, in terms of `A` and `B`. -/
lemma shortWeierstrassCurve_j_mul_Δ (A B : ℂ) [(shortWeierstrassCurve A B).IsElliptic] :
    (shortWeierstrassCurve A B).j * (-16 * (4 * A ^ 3 + 27 * B ^ 2)) = (-48 * A) ^ 3 := by
  have := (shortWeierstrassCurve A B).j_mul_Δ
  rwa [shortWeierstrassCurve_Δ, shortWeierstrassCurve_c₄] at this

/-- If the lattice `ℤ + ℤτ` and the curve `y² = x³ + Ax + B` have the same `j`-invariant,
then `B² g₂(τ)³ + 4A³ g₃(τ)² = 0`. -/
lemma g₂_g₃_relation_of_j_eq {A B : ℂ} (τ : ℍ) [(shortWeierstrassCurve A B).IsElliptic]
    (hj : (periodPair τ).weierstrassCurve.j = (shortWeierstrassCurve A B).j) :
    B ^ 2 * (periodPair τ).g₂ ^ 3 + 4 * A ^ 3 * (periodPair τ).g₃ ^ 2 = 0 := by
  have : (12 * (periodPair τ).g₂) ^ 3 * (-16 * (4 * A ^ 3 + 27 * B ^ 2))
      = (-48 * A) ^ 3 * ((periodPair τ).g₂ ^ 3 - 27 * (periodPair τ).g₃ ^ 2) := by
    rw [← (periodPair τ).weierstrassCurve_j_mul_Δ, ← shortWeierstrassCurve_j_mul_Δ A B, hj]
    ring
  linear_combination this / (-746496)

theorem exists_periodPair_g₂_g₃ {A B : ℂ} (h : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    ∃ L : PeriodPair, L.g₂ = -4 * A ∧ L.g₃ = -4 * B := by
  haveI := shortWeierstrasCurve_elliptic h
  -- Choose `τ` with `j(ℤ+ℤτ) = j(y² = x³ + Ax + B)`.
  obtain ⟨τ, hτ⟩ := j_surjective (shortWeierstrassCurve A B).j
  have := g₂_g₃_relation_of_j_eq τ ((periodPair_j_eq_j τ).trans hτ)
  -- Case analysis on `A`, `B`.
  rcases eq_or_ne A 0 with hA | hA
  · -- `A = 0`: then `g₂(τ) = 0`, and any `α` with `α⁶ · (-4B) = g₃(τ)` works.
    subst hA
    have hB : B ≠ 0 := by grind
    have hg₂0 : (periodPair τ).g₂ = 0 := eq_zero_of_mul_pow_eq_zero (B ^ 2) 3 (by norm_num)
      (pow_ne_zero 2 hB) (by linear_combination this)
    obtain ⟨α, hα, hP6⟩ := exists_pow_mul_eq 6 (by norm_num) (-4 * B)
      ((periodPair τ).g₃_ne_zero_of_g₂_eq_zero hg₂0) (mul_ne_zero (by norm_num) hB)
    exact ⟨scaledPair τ hα, scaledPair_g₂_g₃ τ hα (by rw [hg₂0]; ring) hP6⟩
  rcases eq_or_ne B 0 with hB | hB
  · -- `B = 0`: then `g₃(τ) = 0`, and any `α` with `α⁴ · (-4A) = g₂(τ)` works.
    subst hB
    have hg₃0 : (periodPair τ).g₃ = 0 := eq_zero_of_mul_pow_eq_zero (4 * A ^ 3) 2 (by norm_num)
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 hA)) (by linear_combination this)
    obtain ⟨α, hα, hP4⟩ := exists_pow_mul_eq 4 (by norm_num) (-4 * A)
      ((periodPair τ).g₂_ne_zero_of_g₃_eq_zero hg₃0) (mul_ne_zero (by norm_num) hA)
    exact ⟨scaledPair τ hα, scaledPair_g₂_g₃ τ hα hP4 (by rw [hg₃0]; ring)⟩
  · -- `A, B ≠ 0`: then `g₂(τ), g₃(τ) ≠ 0`, and any `α` with `α² = A g₃(τ) / (B g₂(τ))` works.
    have hg₂ne : (periodPair τ).g₂ ≠ 0 := fun h₂ ↦ (periodPair τ).g₃_ne_zero_of_g₂_eq_zero h₂
      (eq_zero_of_mul_pow_eq_zero (4 * A ^ 3) 2 (by norm_num) (mul_ne_zero (by norm_num)
      (pow_ne_zero 3 hA)) (by linear_combination this - B ^ 2 * (periodPair τ).g₂ ^ 2 * h₂))
    have hg₃ne : (periodPair τ).g₃ ≠ 0 := fun h₃ ↦ hg₂ne (eq_zero_of_mul_pow_eq_zero (B ^ 2) 3
      (by norm_num) (pow_ne_zero 2 hB) (by linear_combination this - 4 * A ^ 3 *
      (periodPair τ).g₃ * h₃))
    set β := A * (periodPair τ).g₃ / (B * (periodPair τ).g₂) with hβ
    obtain ⟨α, hα2⟩ := IsAlgClosed.exists_pow_nat_eq β (n := 2) (by norm_num)
    have hα : α ≠ 0 := fun h0 ↦ (show β ≠ 0 by
      simpa [hβ] using div_ne_zero (mul_ne_zero hA hg₃ne) (mul_ne_zero hB hg₂ne)) (by grind)
    have hP4 : α ^ 4 * (-4 * A) = (periodPair τ).g₂ := by
      have h4 : α ^ 4 = β ^ 2 := by grind
      rw [h4, hβ]
      field_simp
      linear_combination -this
    have hP6 : α ^ 6 * (-4 * B) = (periodPair τ).g₃ := by
      have h6 : α ^ 6 = β ^ 3 := by
        rw [← hα2]
        ring
      rw [h6, hβ]
      field_simp
      linear_combination -this
    exact ⟨scaledPair τ hα, scaledPair_g₂_g₃ τ hα hP4 hP6⟩

theorem exists_periodPair_weierstrassCurve_eq {A B : ℂ} (h : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    ∃ L : PeriodPair, L.weierstrassCurve = shortWeierstrassCurve A B := by
  obtain ⟨L, hg₂, hg₃⟩ := exists_periodPair_g₂_g₃ h
  refine ⟨L, ?_⟩
  simp only [PeriodPair.weierstrassCurve, shortWeierstrassCurve, hg₂, hg₃, WeierstrassCurve.mk.injEq]
  norm_num
