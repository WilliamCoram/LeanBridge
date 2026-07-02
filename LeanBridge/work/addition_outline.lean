import LeanBridge.work.addition

/-!
# Outline: the analytic input for the addition theorem for `℘`

This file is a *road map*, not a proof: every statement below is `sorry`ed, but each one
elaborates, so the file doubles as a to-do list whose items can be proved independently and
in (roughly) the order given.  The goal is to discharge the three `sorry`s of
`LeanBridge/work/addition.lean`:

* `weierstrassP_add`        — the addition formula for `℘` (X-coordinate, chord case);
* `derivWeierstrassP_add`   — the companion formula for `℘'` (Y-coordinate, chord case);
* the `hxx : ℘ z = ℘ w` branch of `toPoint_add` (doubling / vertical-line case).

## What Mathlib already provides (`Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass`)

* `℘[L]`, `℘'[L]`, double periodicity (`weierstrassP_add_coe`, `derivWeierstrassP_add_coe`),
  parity (`weierstrassP_neg`, `derivWeierstrassP_neg`);
* analyticity off the lattice (`analyticOnNhd_weierstrassP`, `analyticOnNhd_derivWeierstrassP`)
  and meromorphy on all of `ℂ` (`meromorphic_weierstrassP`, `meromorphic_derivWeierstrassP`);
* the pole order of `℘` (`order_weierstrassP : meromorphicOrderAt ℘[L] l₀ = -2`);
* `deriv ℘[L] = ℘'[L]` (`deriv_weierstrassP`);
* the differential equation `℘'² = 4℘³ - g₂℘ - g₃` (`derivWeierstrassP_sq`);
* Liouville-type compactness: `IsZLattice.isCompact_range_of_periodic`;
* meromorphic order/divisor bookkeeping: `meromorphicOrderAt`, `MeromorphicOn.divisor`
  (`Mathlib.Analysis.Meromorphic.*`).

## What is genuinely missing

Mathlib has **no residue theorem, no argument principle, and no valence formula**.  Sections 3–5
below outline that theory in the special case needed here (a period parallelogram).  Section 7
sketches an alternative route that avoids contour integration entirely, at the price of more
Laurent-expansion bookkeeping.

## Dependency graph

```
§1 Laurent data at the poles           (provable today, no new theory)
§2 Liouville I for elliptic functions   (provable today via isCompact_range_of_periodic)
§3 residues + argument principle on the period parallelogram   (NEW complex analysis)
        │
        ▼
§4 valence formula + Abel relation      (NEW, from §3)
        │
        ├──▶ §5 fibers of ℘, zeros of ℘'       (order-2 / order-3 counting)
        │
        ▼
§6 chord construction ⇒ weierstrassP_add, derivWeierstrassP_add
§6 tangent construction ⇒ doubling case of toPoint_add
```
-/

open Complex Filter Topology Function PeriodPair

noncomputable section

namespace PeriodPair

variable (L : PeriodPair)

/-! ## §1 Laurent data at the poles

Everything here is provable **today** from the power-series API already in Mathlib
(`weierstrassPExcept`, `analyticAt_weierstrassPExcept`, `hasFPowerSeriesAt_weierstrassPExcept`,
`iteratedDeriv_weierstrassPExcept_self`, and their `℘'` analogues): near a lattice point `l₀`
one has `℘(z) = (z - l₀)⁻² + (analytic)` and `℘'(z) = -2 (z - l₀)⁻³ + (analytic)`. -/

/-- `℘'` has a pole of order exactly `3` at each lattice point.  Companion to Mathlib's
`order_weierstrassP`; proved the same way, from `derivWeierstrassPExcept`. -/
theorem order_derivWeierstrassP {l₀ : ℂ} (h : l₀ ∈ L.lattice) :
    meromorphicOrderAt ℘'[L] l₀ = -3 := by
  sorry

/-- Leading Laurent coefficient of `℘` at `0`: `z² ℘(z) → 1`.  Needed to evaluate the constants
appearing in the Liouville arguments of §6/§7.  Follows from `℘(z) = z⁻² + ℘[L - 0](z)` and
continuity of the analytic part. -/
theorem tendsto_sq_mul_weierstrassP :
    Tendsto (fun z : ℂ ↦ z ^ 2 * ℘[L] z) (𝓝[≠] 0) (𝓝 1) := by
  sorry

/-- Leading Laurent coefficient of `℘'` at `0`: `z³ ℘'(z) → -2`. -/
theorem tendsto_cube_mul_derivWeierstrassP :
    Tendsto (fun z : ℂ ↦ z ^ 3 * ℘'[L] z) (𝓝[≠] 0) (𝓝 (-2)) := by
  sorry

/-- `℘'' = 6℘² - g₂/2` off the lattice: differentiate `derivWeierstrassP_sq` using
`deriv_weierstrassP` and analyticity of both sides on the open set `L.latticeᶜ`.
Provable today; this is the slope of the *tangent* line in §6. -/
theorem deriv_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 := by
  sorry

/-! ## §2 Elliptic functions and Liouville I -/

/-- An **elliptic function** for the lattice `Λ = L.lattice`: meromorphic on `ℂ` and
`Λ`-periodic.  All functions in this file (`℘`, `℘'`, and the chord/tangent combinations)
are elliptic. -/
def IsEllipticFunction (f : ℂ → ℂ) : Prop :=
  Meromorphic f ∧ ∀ l ∈ L.lattice, Periodic f l

/-- **Liouville I.**  An *entire* `Λ`-periodic function is constant.  Provable today:
the range is compact (`IsZLattice.isCompact_range_of_periodic`), hence bounded, and
`Differentiable.apply_eq_apply_of_bounded` (Liouville) finishes — exactly the argument used for
`relation_eq_zero` in Mathlib's `Elliptic/Weierstrass.lean`. -/
theorem apply_eq_apply_of_differentiable_of_periodic {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hper : ∀ l ∈ L.lattice, Periodic f l) (z w : ℂ) :
    f z = f w := by
  sorry

/-- **Liouville I′.**  An elliptic function with no poles is constant.  From
`apply_eq_apply_of_differentiable_of_periodic` after upgrading `AnalyticOnNhd` to
`Differentiable`. -/
theorem isEllipticFunction_const {f : ℂ → ℂ} (hf : L.IsEllipticFunction f)
    (hf' : AnalyticOnNhd ℂ f Set.univ) (z w : ℂ) :
    f z = f w := by
  sorry

/-! ## §3 The missing complex analysis: residues on the period parallelogram

None of this is elliptic-function specific; it belongs in `Mathlib.Analysis.Meromorphic` /
`Mathlib.Analysis.SpecialFunctions.Complex`.  The integration contour is the boundary of a
(translated) fundamental parallelogram `x₀ + [0,1)·ω₁ + [0,1)·ω₂`; Mathlib's rectangle-contour
API (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` etc.) covers rectangles only,
so either (a) a parallelogram version must be developed, or (b) one works with
`circleIntegral` around each singularity plus a homotopy/decomposition argument. -/

/-- **(C1) The residue** of `f` at `x`: the coefficient `a₋₁` of the Laurent expansion,
equivalently `(2πi)⁻¹ ∮_{C(x,r)} f` for all small `r > 0`.  *Missing from Mathlib.*
A workable definition: `meromorphicTrailingCoeffAt`-style extraction from the local normal form
`f = (z - x)^n • g` (`MeromorphicAt.meromorphicOrderAt_eq_int_iff`), or directly as the circle
integral.  Needs the basic API: residue of an analytic function is `0`, residue of
`c/(z - x)` is `c`, additivity, and behaviour under `deriv`. -/
def residue (f : ℂ → ℂ) (x : ℂ) : ℂ := by
  sorry

/-- **(C2) Residue of a logarithmic derivative = order** (the local argument principle).
`logDeriv f = deriv f / f` is Mathlib's `logDeriv`.  Proof: write `f = (z-x)^n • g` with
`g x ≠ 0` (`meromorphicOrderAt_eq_int_iff`), so `logDeriv f = n/(z-x) + logDeriv g` near `x`. -/
theorem residue_logDeriv {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x)
    (h : meromorphicOrderAt f x ≠ ⊤) :
    residue (logDeriv f) x = ((meromorphicOrderAt f x).untop₀ : ℂ) := by
  sorry

/-- **(C2′) Residue of `z ↦ z · logDeriv f z` = order · point.**  The weighted version feeding
the Abel relation (§4).  Same local computation as `residue_logDeriv`. -/
theorem residue_mul_logDeriv {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x)
    (h : meromorphicOrderAt f x ≠ ⊤) :
    residue (fun z ↦ z * logDeriv f z) x = ((meromorphicOrderAt f x).untop₀ : ℂ) * x := by
  sorry

/-- **(C3) Liouville II: the residues of an elliptic function sum to zero** over a fundamental
domain.  Proof: integrate over the boundary of a translated period parallelogram avoiding all
poles (possible since the poles are discrete); opposite sides cancel by periodicity; the residue
theorem (the genuinely new ingredient) identifies the integral with the sum of residues inside.
The `∑ᶠ` is legitimate: an elliptic `f ≢ 0` has only finitely many poles in a fundamental
domain (discreteness of the polar set + compactness of the closure). -/
theorem sum_residue_eq_zero {f : ℂ → ℂ} (hf : L.IsEllipticFunction f) (hf' : f ≠ 0) :
    ∑ᶠ x ∈ ZSpan.fundamentalDomain L.basis, residue f x = 0 := by
  sorry

/-! ## §4 The valence formula and the Abel relation

Both follow by applying §3 to `logDeriv f` and `z · logDeriv f z`.  For the second, the
integrand is *not* periodic — `(z + ω) logDeriv f (z + ω) - z logDeriv f z = ω · logDeriv f z` —
so the side-pairing leaves `ω₁ (2πi)⁻¹∮ logDeriv f + ω₂ (2πi)⁻¹∮ logDeriv f`, and each
`(2πi)⁻¹ ∮_side logDeriv f` is a *winding number*, hence an integer: this is where
`z ↦ f(z)` along one period side being a closed loop is used, and it is why the conclusion is
only a congruence mod `Λ`. -/

/-- **(C4) Valence formula / Liouville III.**  A nonzero elliptic function has as many zeros as
poles in a fundamental domain, counted with multiplicity (`MeromorphicOn.divisor` records
`(meromorphicOrderAt f x).untop₀`).  From `sum_residue_eq_zero` applied to `logDeriv f`
via `residue_logDeriv` (note `logDeriv f` is again elliptic). -/
theorem valence_formula {f : ℂ → ℂ} (hf : L.IsEllipticFunction f) (hf' : f ≠ 0) :
    ∑ᶠ x ∈ ZSpan.fundamentalDomain L.basis, MeromorphicOn.divisor f Set.univ x = 0 := by
  sorry

/-- **(C5) Abel relation / Liouville IV.**  The multiplicity-weighted sum of the zeros and poles
of a nonzero elliptic function lies in the lattice.  From `sum_residue_eq_zero` applied to
`z ↦ z * logDeriv f z` via `residue_mul_logDeriv`, plus the winding-number argument for the
boundary correction terms described above. -/
theorem abel_relation {f : ℂ → ℂ} (hf : L.IsEllipticFunction f) (hf' : f ≠ 0) :
    (∑ᶠ x ∈ ZSpan.fundamentalDomain L.basis, MeromorphicOn.divisor f Set.univ x • x)
      ∈ L.lattice := by
  sorry

/-! ## §5 Fibers of `℘` and zeros of `℘'`

`℘` is elliptic of order 2 (one double pole per fundamental domain, `order_weierstrassP`), so by
the valence formula applied to `u ↦ ℘(u) - c` it takes every value exactly twice.  Since `℘` is
even, the two solutions of `℘(u) = ℘(w)` are `u ≡ ±w`.  These fiber lemmas are what convert
"same X-coordinate" hypotheses into lattice congruences, and they also pin down the doubling
case. -/

/-- **Fibers of `℘`.**  For `z, w ∉ Λ`:  `℘(z) = ℘(w) ↔ z ≡ w or z ≡ -w (mod Λ)`.
(⇐ is periodicity + evenness, available today; ⇒ needs `valence_formula` applied to
`u ↦ ℘(u) - ℘(w)`, which has a single double pole, hence exactly two zeros mod `Λ`,
and `abel_relation` or evenness to identify them as `±w`.) -/
theorem weierstrassP_eq_weierstrassP_iff {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) :
    ℘[L] z = ℘[L] w ↔ z - w ∈ L.lattice ∨ z + w ∈ L.lattice := by
  sorry

/-- **Zeros of `℘'` are the 2-torsion points.**  For `z ∉ Λ`: `℘'(z) = 0 ↔ 2z ∈ Λ`.
(⇐ is oddness + periodicity: `℘'(z) = ℘'(z - 2z) = ℘'(-z) = -℘'(z)`, available today.
⇒: `℘'` is elliptic of order 3 and the three half-periods `ω₁/2, ω₂/2, (ω₁+ω₂)/2` already
supply three zeros, so by `valence_formula` there are no others.) -/
theorem derivWeierstrassP_eq_zero_iff {z : ℂ} (hz : z ∉ L.lattice) :
    ℘'[L] z = 0 ↔ 2 * z ∈ L.lattice := by
  sorry

/-- Convenience form: off the lattice and away from 2-torsion, `℘' ≠ 0`.  This is the
nondegeneracy needed for the tangent slope in the doubling case. -/
theorem derivWeierstrassP_ne_zero {z : ℂ} (hz : z ∉ L.lattice) (h2z : 2 * z ∉ L.lattice) :
    ℘'[L] z ≠ 0 :=
  fun h ↦ h2z ((L.derivWeierstrassP_eq_zero_iff hz).mp h)

/-! ## §6 The chord and tangent constructions

The line `y = a·x + b` through `(℘ z, ℘' z)` and `(℘ w, ℘' w)` cuts out the elliptic function
`g(u) = ℘'(u) - a ℘(u) - b` of order 3 (one triple pole at `Λ`, by §1).  By the valence formula
`g` has three zeros mod `Λ`; two of them are `z` and `w`, and by the Abel relation the third is
`≡ -(z + w)`.  Evaluating the line there and substituting into the differential equation gives
both addition formulae. -/

/-- Slope of the chord through `(℘ z, ℘' z)` and `(℘ w, ℘' w)`.  (This is `2 ·` Mathlib's
`WeierstrassCurve.Affine.slope`, because the curve coordinate is `y = ℘'/2`.) -/
def chordSlope (z w : ℂ) : ℂ := (℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w)

/-- Intercept of the same chord. -/
def chordIntercept (z w : ℂ) : ℂ := ℘'[L] z - L.chordSlope z w * ℘[L] z

/-- The chord function `g(u) = ℘'(u) - (a ℘(u) + b)` is elliptic.  Provable **today** from
`meromorphic_weierstrassP`, `meromorphic_derivWeierstrassP` and the `_add_coe` periodicity
lemmas — no new theory needed. -/
theorem isEllipticFunction_chordFun (z w : ℂ) :
    L.IsEllipticFunction
      fun u ↦ ℘'[L] u - (L.chordSlope z w * ℘[L] u + L.chordIntercept z w) := by
  sorry

/-- The chord function has a pole of order exactly 3 at the lattice (the `℘'` term dominates).
From §1 (`order_derivWeierstrassP`, `order_weierstrassP`) and
`meromorphicOrderAt` arithmetic (`meromorphicOrderAt_add_eq_left_of_lt`-style lemmas). -/
theorem order_chordFun (z w : ℂ) {l₀ : ℂ} (h : l₀ ∈ L.lattice) :
    meromorphicOrderAt
      (fun u ↦ ℘'[L] u - (L.chordSlope z w * ℘[L] u + L.chordIntercept z w)) l₀ = -3 := by
  sorry

/-- **The key valence-formula application: the third intersection point.**
Under the chord-case hypotheses, `-(z + w)` lies on the chord; by oddness of `℘'` and evenness
of `℘` this reads `℘'(z + w) = -(a ℘(z + w) + b)`.

Proof sketch: the chord function `g` is elliptic of order 3 (`order_chordFun`), vanishes at `z`
and `w` (definition of `a`, `b`), so `valence_formula` gives exactly three zeros mod `Λ` and
`abel_relation` forces the zero multiset `{z, w, u₃}` to satisfy `z + w + u₃ ∈ Λ`, i.e.
`u₃ ≡ -(z+w)`.  Care is needed when the third zero collides with `z` or `w` (then it is a
double zero and the statement still follows from multiplicity counting); the hypothesis
`℘ z ≠ ℘ w` rules out `z ≡ ±w` (via `weierstrassP_eq_weierstrassP_iff`), which keeps `z`, `w`
distinct zeros mod `Λ`. -/
theorem chordFun_third_zero {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z + w ∉ L.lattice) (hx : ℘[L] z ≠ ℘[L] w) :
    ℘'[L] (z + w) = -(L.chordSlope z w * ℘[L] (z + w) + L.chordIntercept z w) := by
  sorry

/-- **Vieta step.**  Any point `u` on the chord with `u ∉ Λ` satisfies, by the differential
equation `derivWeierstrassP_sq`, `(a ℘(u) + b)² = 4℘(u)³ - g₂ ℘(u) - g₃`; that is, `℘(u)` is a
root of the cubic `4X³ - a²X² - (2ab + g₂)X - (b² + g₃)`.  By `chordFun_third_zero` this applies
to `u = z, w, z + w`, and multiplicity counting (again the valence formula, applied to
`u ↦ ℘(u) - r` for each root `r`) shows `℘ z, ℘ w, ℘(z+w)` exhaust the roots with the right
multiplicities.  Vieta on the `X²` coefficient gives the sum of the roots. -/
theorem chord_vieta {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z + w ∉ L.lattice) (hx : ℘[L] z ≠ ℘[L] w) :
    ℘[L] z + ℘[L] w + ℘[L] (z + w) = L.chordSlope z w ^ 2 / 4 := by
  sorry

/-- `weierstrassP_add` (the first `sorry` of `addition.lean`) is pure algebra from
`chord_vieta`: `((℘'z - ℘'w)/(2(℘z - ℘w)))² = a²/4`. -/
example {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z + w ∉ L.lattice) (hx : ℘[L] z ≠ ℘[L] w) :
    ℘[L] (z + w)
      = ((℘'[L] z - ℘'[L] w) / (2 * (℘[L] z - ℘[L] w))) ^ 2 - ℘[L] z - ℘[L] w := by
  have h := L.chord_vieta hz hw hzw hx
  have hne : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr hx
  rw [chordSlope] at h
  field_simp at h ⊢
  linear_combination h

/-- `derivWeierstrassP_add` (the second `sorry` of `addition.lean`) is pure algebra from
`chordFun_third_zero`: unfold `chordIntercept` and rearrange. -/
example {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z + w ∉ L.lattice) (hx : ℘[L] z ≠ ℘[L] w) :
    ℘'[L] (z + w)
      = -((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w) * (℘[L] (z + w) - ℘[L] z) + ℘'[L] z) := by
  have h := L.chordFun_third_zero hz hw hzw hx
  rw [chordIntercept, chordSlope] at h
  rw [h]
  ring

/-! ### The doubling (tangent) case

In the remaining branch of `toPoint_add` we have `z, w, z + w ∉ Λ` and `℘ z = ℘ w`.  By
`weierstrassP_eq_weierstrassP_iff`, `z ≡ w` or `z ≡ -w` mod `Λ`; the latter contradicts
`z + w ∉ Λ`, so `z ≡ w` and (by periodicity of `℘, ℘'` and `toPoint_add_mem`) everything
reduces to the honest doubling statement at `z` with `2z ∉ Λ`.  Then `℘'(z) ≠ 0`
(`derivWeierstrassP_ne_zero`), the tangent line has slope `a = ℘''(z)/℘'(z)`
(`deriv_derivWeierstrassP` computes the numerator), and the same valence/Abel argument applied
to the *tangent* function — where `z` is now a **double** zero — yields the duplication
formulae.  On the Mathlib side the relevant group-law lemmas are
`WeierstrassCurve.Affine.Point.add_of_Y_ne` and `slope_of_Y_ne` (note `y = ℘'/2`, so
Mathlib's tangent slope `(3x² + a₄)/(2y)` equals `℘''/(2·½℘'·2) = a/2`, consistent with the
chord case). -/

/-- **Duplication formula, X-coordinate.**  Tangent-line analogue of `chord_vieta` +
`chord_vieta`-algebra: `℘(2z) = (℘''(z) / (2℘'(z)))² - 2℘(z)`. -/
theorem weierstrassP_two_mul {z : ℂ} (hz : z ∉ L.lattice) (h2z : 2 * z ∉ L.lattice) :
    ℘[L] (2 * z)
      = ((6 * ℘[L] z ^ 2 - L.g₂ / 2) / (2 * ℘'[L] z)) ^ 2 - 2 * ℘[L] z := by
  sorry

/-- **Duplication formula, Y-coordinate.**  Tangent-line analogue of `chordFun_third_zero`. -/
theorem derivWeierstrassP_two_mul {z : ℂ} (hz : z ∉ L.lattice) (h2z : 2 * z ∉ L.lattice) :
    ℘'[L] (2 * z)
      = -((6 * ℘[L] z ^ 2 - L.g₂ / 2) / ℘'[L] z * (℘[L] (2 * z) - ℘[L] z) + ℘'[L] z) := by
  sorry

/-- **The third `sorry` of `addition.lean`** (the `hxx : ℘ z = ℘ w` branch of `toPoint_add`),
stated at the `toPoint` level.  Proof plan: `weierstrassP_eq_weierstrassP_iff` + `hzw` give
`z - w ∈ Λ`; `toPoint_add_mem` rewrites `toPoint w = toPoint z` and `toPoint (z + w) =
toPoint (2z)`; `derivWeierstrassP_ne_zero` (with `2z = z + w - (w - z) ∉ Λ`) shows we are in
Mathlib's `add_of_Y_ne` case; finish with `weierstrassP_two_mul`, `derivWeierstrassP_two_mul`
and `deriv_derivWeierstrassP`, exactly mirroring the chord-case wiring already in
`addition.lean`. -/
theorem toPoint_add_of_weierstrassP_eq {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z + w ∉ L.lattice) (hxx : ℘[L] z = ℘[L] w) :
    L.toPoint (z + w) = L.toPoint z + L.toPoint w := by
  sorry

/-! ## §7 Alternative route (no contour integration)

For comparison: the addition theorem can be proved without §3–§4, using only Liouville I (§2)
and Laurent expansions (§1).  Fix `w ∉ Λ` generic and set

  `F(z) = ℘(z + w) + ℘(z) + ℘(w) - ¼ ((℘'(z) - ℘'(w)) / (℘(z) - ℘(w)))²`.

One shows: (i) `F` is `Λ`-periodic and meromorphic in `z`; (ii) its only candidate poles
(`z ∈ Λ`, `z ≡ ±w`) are removable — this is a finite Laurent-coefficient computation using §1,
e.g. at `z = 0` the `z⁻²` of `℘(z)` cancels against the expansion of the squared slope term;
(iii) by Liouville I′ (`isEllipticFunction_const`), `F` is constant; (iv) the constant is `0`,
by evaluating the limit `z → 0` via §1.  This route trades the residue theorem for careful
`analyticAt` bookkeeping at the removable singularities (`Mathlib`'s
`Complex.analyticAt_update`-style removable-singularity API:
`Complex.differentiableOn_update_limUnder_of_bddAbove` etc.).  The fiber lemma
`weierstrassP_eq_weierstrassP_iff` — still needed for the doubling reduction — can also be
obtained this way, from injectivity of an order-2 map on a half-domain, though the counting
proof of §5 is cleaner.  If the residue theorem turns out to be far off, this is the pragmatic
fallback; the statements of §6 are unchanged. -/

end PeriodPair
