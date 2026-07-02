import LeanBridge.work.addition_euler

/-!
# Towards the addition theorem for `℘` and additivity of the uniformization map `φ`

`forward.lean` builds the uniformization map `φ : ℂ/Λ → E(ℂ)` (`PeriodPair.uniformization`,
`z ↦ (℘(z), ½℘'(z))`) and proves its structural properties (`φ(0)=O`, `φ(-z)=-φ(z)`) sorry-free.
The one remaining group-homomorphism property is **additivity** `φ(z+w) = φ(z) + φ(w)`, matching the
analytic group law on `ℂ/Λ` with the chord–tangent group law on `E`.

This file *completes* that proof (no `sorry`s remain).  The strategy:

1. **Reduce to a pointwise statement on `ℂ`.**  Since `φ = toPoint ∘ (mk : ℂ → ℂ/Λ)` and `mk` is a
   group homomorphism, additivity of `φ` is equivalent to
   `PeriodPair.toPoint_add : toPoint (z + w) = toPoint z + toPoint w`  for all `z w : ℂ`.
   (`uniformization_add_of_toPoint_add`, sorry-free.)

2. **Structural cases of `toPoint_add`** — where one of `z`, `w`, `z + w` lies in `Λ` — are proved
   here sorry-free, using the periodicity (`toPoint_add_mem`) and negation (`toPoint_neg`) lemmas
   from `forward.lean`.

3. **The generic (chord) case** `℘(z) ≠ ℘(w)` is wired end-to-end to Mathlib's explicit group law
   (`Point.add_of_X_ne`, `slope`, `addX`, `addY`), modulo the two analytic identities
   `weierstrassP_add` / `derivWeierstrassP_add` — the **addition theorem for `℘`**.

## The analytic input

`weierstrassP_add` and `derivWeierstrassP_add` are the classical addition formulae for the
Weierstrass `℘`-function.  Classically these rest on the **valence formula** for elliptic
functions, which is not yet in Mathlib; instead they are proved sorry-free in
`LeanBridge.work.addition_euler` by Euler's differential-equation argument
(`weierstrassP_add_of_euler`, `derivWeierstrassP_add_of_euler`), which needs no contour
integration.  The same file supplies the fiber lemma
(`sub_mem_or_add_mem_of_weierstrassP_eq`), the 2-torsion characterisation of the zeros of `℘'`
(`two_mul_mem_lattice_of_derivWeierstrassP_eq_zero`) and the duplication formulas
(`weierstrassP_two_mul`, `derivWeierstrassP_two_mul`) used for the doubling (tangent) case of
`toPoint_add` below.
-/

open Complex UpperHalfPlane EisensteinSeries ModularForm PeriodPair
open scoped UpperHalfPlane CongruenceSubgroup MatrixGroups

noncomputable section

namespace PeriodPair

/-! ### The addition theorem for `℘` (the missing analytic input)

In the affine coordinates `(x, y) = (℘, ½℘')` the line through `φ(z)` and `φ(w)` has slope
`ℓ = (½℘'(z) - ½℘'(w)) / (℘(z) - ℘(w)) = (℘'(z) - ℘'(w)) / (2(℘(z) - ℘(w)))`, and the classical
addition formula reads `℘(z+w) = ℓ² - ℘(z) - ℘(w)`.  Matching Mathlib's `addX` (with `a₁ = a₂ = 0`)
`addX x₁ x₂ ℓ = ℓ² - x₁ - x₂` gives exactly the `X`-coordinate of `φ(z) + φ(w)`. -/

/-- **Addition theorem for `℘` (X-coordinate).**  For `z`, `w`, `z + w` outside the lattice with
`℘(z) ≠ ℘(w)`,
`℘(z + w) = ((℘'(z) - ℘'(w)) / (2(℘(z) - ℘(w))))² - ℘(z) - ℘(w)`.

Proved in `addition_euler.lean` by Euler's differential-equation argument (no valence formula
needed). -/
theorem weierstrassP_add (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z + w ∉ L.lattice) (hx : ℘[L] z ≠ ℘[L] w) :
    ℘[L] (z + w)
      = ((℘'[L] z - ℘'[L] w) / (2 * (℘[L] z - ℘[L] w))) ^ 2 - ℘[L] z - ℘[L] w :=
  L.weierstrassP_add_of_euler hz hw hzw hx

/-- **Addition theorem for `℘` (Y-coordinate).**  Companion to `weierstrassP_add`, fixing the sign
of `℘'(z + w)`: the third intersection of the chord with `E` is `-(φ(z) + φ(w))`, so
`℘'(z + w) = -((℘'(z) - ℘'(w)) / (℘(z) - ℘(w)) · (℘(z+w) - ℘(z)) + ℘'(z))`.

Proved in `addition_euler.lean` by differentiating the X-formula. -/
theorem derivWeierstrassP_add (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z + w ∉ L.lattice) (hx : ℘[L] z ≠ ℘[L] w) :
    ℘'[L] (z + w)
      = -((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w) * (℘[L] (z + w) - ℘[L] z) + ℘'[L] z) :=
  L.derivWeierstrassP_add_of_euler hz hw hzw hx

/-! ### `toPoint_add`: additivity of the lift `ℂ → E(ℂ)` -/

/-- **The pointwise additivity of the uniformization lift.**  `toPoint (z + w) = toPoint z +
toPoint w` for all `z w : ℂ`.  Structural cases (`z`, `w`, or `z + w` in `Λ`) use periodicity and
negation; the chord case matches Mathlib's `add_of_X_ne` via the addition formulae, and the
doubling case matches `add_of_Y_ne` via the fiber lemma and the duplication formulae. -/
theorem toPoint_add (L : PeriodPair) (z w : ℂ) :
    L.toPoint (z + w) = L.toPoint z + L.toPoint w := by
  -- Case `z ∈ Λ`: `φ(z) = O` and `z + w ≡ w`.
  by_cases hz : z ∈ L.lattice
  · have h0 : L.toPoint z = 0 := by simp [PeriodPair.toPoint, dif_pos hz]
    rw [h0, zero_add, add_comm z w]
    exact L.toPoint_add_mem w ⟨z, hz⟩
  -- Case `w ∈ Λ`: `φ(w) = O` and `z + w ≡ z`.
  by_cases hw : w ∈ L.lattice
  · have h0 : L.toPoint w = 0 := by simp [PeriodPair.toPoint, dif_pos hw]
    rw [h0, add_zero]
    exact L.toPoint_add_mem z ⟨w, hw⟩
  -- Case `z + w ∈ Λ`: `φ(z + w) = O` and `w ≡ -z`, so `φ(z) + φ(w) = φ(z) - φ(z) = O`.
  by_cases hzw : z + w ∈ L.lattice
  · have h0 : L.toPoint (z + w) = 0 := by simp [PeriodPair.toPoint, dif_pos hzw]
    have hwz : L.toPoint w = - L.toPoint z := by
      have h := L.toPoint_add_mem (-z) ⟨z + w, hzw⟩
      rw [show (-z + ((⟨z + w, hzw⟩ : L.lattice) : ℂ)) = w from by
        show -z + (z + w) = w; ring] at h
      rw [h, L.toPoint_neg]
    rw [h0, hwz, add_neg_cancel]
  -- Generic position: `z, w, z + w ∉ Λ`.  Both images are affine points.
  simp only [PeriodPair.toPoint, dif_neg hz, dif_neg hw, dif_neg hzw]
  by_cases hxx : ℘[L] z = ℘[L] w
  · -- Doubling case: `℘ z = ℘ w` and `z + w ∉ Λ` force `z ≡ w (mod Λ)` (fiber lemma), so the
    -- sum is the tangent point at `z`, computed by the duplication formulas.
    have hsub : z - w ∈ L.lattice :=
      (L.sub_mem_or_add_mem_of_weierstrassP_eq hz hw hxx).resolve_right hzw
    have hwz : w - z ∈ L.lattice := by
      have h := neg_mem hsub
      rwa [neg_sub] at h
    have h2z : 2 * z ∉ L.lattice := fun h2z ↦ hzw (by
      have h : z + w = 2 * z + (w - z) := by ring
      rw [h]
      exact add_mem h2z hwz)
    have hy0 : ℘'[L] z ≠ 0 :=
      fun h ↦ h2z (L.two_mul_mem_lattice_of_derivWeierstrassP_eq_zero hz h)
    -- periodicity along `w = z + (w - z)`: `℘' w = ℘' z`, and the sum point is the `2z`-point
    have hy : ℘'[L] w = ℘'[L] z := by
      have h := L.derivWeierstrassP_add_coe z ⟨w - z, hwz⟩
      rwa [show z + ((⟨w - z, hwz⟩ : L.lattice) : ℂ) = w from by
        show z + (w - z) = w; ring] at h
    have hPzw : ℘[L] (z + w) = ℘[L] (2 * z) := by
      have h := L.weierstrassP_add_coe (2 * z) ⟨w - z, hwz⟩
      rwa [show 2 * z + ((⟨w - z, hwz⟩ : L.lattice) : ℂ) = z + w from by
        show 2 * z + (w - z) = z + w; ring] at h
    have hP'zw : ℘'[L] (z + w) = ℘'[L] (2 * z) := by
      have h := L.derivWeierstrassP_add_coe (2 * z) ⟨w - z, hwz⟩
      rwa [show 2 * z + ((⟨w - z, hwz⟩ : L.lattice) : ℂ) = z + w from by
        show 2 * z + (w - z) = z + w; ring] at h
    -- tangent case of the group law: `y₁ ≠ negY`, since `℘' z ≠ 0`
    have hyne : ℘'[L] z / 2 ≠ L.weierstrassCurve.toAffine.negY (℘[L] w) (℘'[L] w / 2) := by
      simp only [WeierstrassCurve.Affine.negY, PeriodPair.weierstrassCurve]
      rw [hy]
      intro heq
      apply hy0
      linear_combination heq
    rw [WeierstrassCurve.Affine.Point.add_of_Y_ne hyne]
    congr 1
    · -- X-coordinate: the duplication formula `℘(2z) = (℘''/(2℘'))² - 2℘`.
      rw [WeierstrassCurve.Affine.slope_of_Y_ne hxx hyne]
      simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
        PeriodPair.weierstrassCurve]
      rw [hPzw, L.weierstrassP_two_mul hz h2z, ← hxx]
      ring_nf
    · -- Y-coordinate: the duplication formula for `℘'(2z)`.
      rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.slope_of_Y_ne hxx hyne]
      simp only [WeierstrassCurve.Affine.negY, PeriodPair.weierstrassCurve]
      rw [hP'zw, L.derivWeierstrassP_two_mul hz h2z, L.weierstrassP_two_mul hz h2z, ← hxx]
      ring_nf
  · -- Chord case `℘(z) ≠ ℘(w)`: match Mathlib's `add_of_X_ne`.
    rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxx]
    have hne : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr hxx
    congr 1
    · -- X-coordinate: `℘(z+w) = addX ℘z ℘w (slope ...)`.
      rw [WeierstrassCurve.Affine.slope_of_X_ne hxx]
      simp only [WeierstrassCurve.Affine.addX, PeriodPair.weierstrassCurve]
      rw [L.weierstrassP_add hz hw hzw hxx]
      field_simp
      ring
    · -- Y-coordinate: `½℘'(z+w) = addY ℘z ℘w (½℘'z) (slope ...)`.  Unfold the whole group-law
      -- formula to base terms and substitute both addition formulae.
      rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.slope_of_X_ne hxx]
      simp only [PeriodPair.weierstrassCurve]
      rw [L.derivWeierstrassP_add hz hw hzw hxx, L.weierstrassP_add hz hw hzw hxx]
      field_simp
      ring

/-! ### Additivity of `φ` on the quotient -/

/-- **Additivity of the uniformization map `φ : ℂ/Λ → E(ℂ)`**, reduced to the pointwise statement
`toPoint_add`.  This is the `map_add'` field needed to upgrade `φ` to an `AddMonoidHom`. -/
theorem uniformization_add_of_toPoint_add (L : PeriodPair)
    (q p : ℂ ⧸ L.lattice.toAddSubgroup) :
    L.uniformization (q + p) = L.uniformization q + L.uniformization p := by
  induction q using QuotientAddGroup.induction_on with
  | _ z =>
    induction p using QuotientAddGroup.induction_on with
    | _ w =>
      have hmk : (QuotientAddGroup.mk z + QuotientAddGroup.mk w : ℂ ⧸ L.lattice.toAddSubgroup)
          = QuotientAddGroup.mk (z + w) := (map_add (QuotientAddGroup.mk' _) z w).symm
      rw [hmk, uniformization_mk, uniformization_mk, uniformization_mk, L.toPoint_add]

/-- **The addition theorem.**  `φ` is additive.  (Moved here from `forward.lean`, where it was
the single remaining `sorry`; it is now a direct consequence of `toPoint_add`.) -/
theorem uniformization_add (L : PeriodPair) (q p : ℂ ⧸ L.lattice.toAddSubgroup) :
    L.uniformization (q + p) = L.uniformization q + L.uniformization p :=
  L.uniformization_add_of_toPoint_add q p

/-- **`φ` as an additive group homomorphism `ℂ/Λ → E(ℂ)`** (Proposition 3.6(b), the map together
with its group-homomorphism structure).  Sorry-free. -/
def uniformizationHom (L : PeriodPair) :
    (ℂ ⧸ L.lattice.toAddSubgroup) →+ L.weierstrassCurve.toAffine.Point where
  toFun := L.uniformization
  map_zero' := L.uniformization_zero
  map_add' := L.uniformization_add

end PeriodPair
