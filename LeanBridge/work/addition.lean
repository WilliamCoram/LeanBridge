import LeanBridge.work.forward

/-!
# Towards the addition theorem for `℘` and additivity of the uniformization map `φ`

`forward.lean` builds the uniformization map `φ : ℂ/Λ → E(ℂ)` (`PeriodPair.uniformization`,
`z ↦ (℘(z), ½℘'(z))`) and proves its structural properties (`φ(0)=O`, `φ(-z)=-φ(z)`) sorry-free.
The one remaining group-homomorphism property is **additivity** `φ(z+w) = φ(z) + φ(w)`, matching the
analytic group law on `ℂ/Λ` with the chord–tangent group law on `E`.

This file *starts* on that proof.  The strategy:

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

## The genuinely missing input

`weierstrassP_add` and `derivWeierstrassP_add` are the classical addition formulae for the
Weierstrass `℘`-function.  Their proof rests on the **valence formula** for elliptic functions
(a non-zero elliptic function has equally many zeros and poles in a fundamental domain, and the
sum of its zeros is congruent to the sum of its poles modulo `Λ`), applied to the order-3 elliptic
function `℘'(u) - (ℓ ℘(u) + c)` cut out by a line.  This elliptic-function theory is **not yet in
Mathlib**, so those two identities are the `sorry`s isolated below; everything else is derived from
them.  The doubling (tangent) case and the "vertical line" degenerate case are likewise left as
`sorry` pending the same input.
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

*Analytic input, not yet available in Mathlib* (valence formula for elliptic functions). -/
theorem weierstrassP_add (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z + w ∉ L.lattice) (hx : ℘[L] z ≠ ℘[L] w) :
    ℘[L] (z + w)
      = ((℘'[L] z - ℘'[L] w) / (2 * (℘[L] z - ℘[L] w))) ^ 2 - ℘[L] z - ℘[L] w := by
  sorry

/-- **Addition theorem for `℘` (Y-coordinate).**  Companion to `weierstrassP_add`, fixing the sign
of `℘'(z + w)`: the third intersection of the chord with `E` is `-(φ(z) + φ(w))`, so
`℘'(z + w) = -((℘'(z) - ℘'(w)) / (℘(z) - ℘(w)) · (℘(z+w) - ℘(z)) + ℘'(z))`.

*Analytic input, not yet available in Mathlib* (valence formula for elliptic functions). -/
theorem derivWeierstrassP_add (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z + w ∉ L.lattice) (hx : ℘[L] z ≠ ℘[L] w) :
    ℘'[L] (z + w)
      = -((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w) * (℘[L] (z + w) - ℘[L] z) + ℘'[L] z) := by
  sorry

/-! ### `toPoint_add`: additivity of the lift `ℂ → E(ℂ)` -/

/-- **The pointwise additivity of the uniformization lift.**  `toPoint (z + w) = toPoint z +
toPoint w` for all `z w : ℂ`.  Structural cases (`z`, `w`, or `z + w` in `Λ`) and the generic chord
case are handled; the doubling and vertical-line cases await the same analytic input. -/
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
  · -- Doubling / vertical-line case: needs the tangent addition formula (same analytic input).
    sorry
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

end PeriodPair
