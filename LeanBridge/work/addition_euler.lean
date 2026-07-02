import LeanBridge.work.addition_outline

/-!
# The Euler route to the addition theorem: no contour integration

This file does two things.

**Part I (this docstring)** records why §3–§4 of `addition_outline.lean` — residues on the
period parallelogram, the valence formula, and the Abel relation — are the expensive part of
that plan.

**Part II (the declarations below)** details an alternative proof of the addition theorem,
going back to Euler's differential-equation argument, in which *every* analytic ingredient is
already in Mathlib.  Somewhat surprisingly, the fiber lemma and the doubling case — the two
places where the valence formula seemed unavoidable — can also be recovered *from* the addition
formula by elementary limit arguments, so the entire contour-integration layer (§3–§4 of the
outline) can be bypassed for the purpose of closing the three `sorry`s of `addition.lean`.

## Part I: why §3–§4 of the outline are hard

What the current Mathlib pin has:

* the full circle-integral calculus `∮ (z - w)^n` (`circleIntegral.integral_sub_zpow_of_ne`,
  `circleIntegral.integral_sub_inv_of_mem_ball` giving `2πi`);
* Cauchy–Goursat for **axis-aligned rectangles only**
  (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`);
* meromorphic normal forms and divisors (`meromorphicOrderAt_eq_int_iff`,
  `MeromorphicOn.divisor`), `MeromorphicAt.deriv`, `MeromorphicAt.div`.

What it does **not** have: any residue theorem, any argument principle, winding numbers.
Concretely, two walls stand between the outline's §3 statements and a proof:

1. **The residue theorem on a parallelogram.**  There is no conformal shortcut: ℂ-affine maps
   preserve angles, so a genuine period parallelogram is never the affine image of a rectangle.
   Parallelogram Cauchy–Goursat must be re-proved (feasible: pull the ℝ-linear substitution
   `x + iy ↦ x·ω₁ + y·ω₂` through the box divergence theorem underlying
   `CauchyIntegral.lean`, ~300 lines), and then the residue extraction needs
   `∮_∂P (z - p)⁻¹ = 2πi` for `p` inside `P` — an integer-valuedness argument (loop-lifting)
   plus continuity in `p` plus one genuinely fiddly explicit evaluation with `Complex.log`
   branch bookkeeping.
2. **Abel's integrality.**  For the Abel relation the integrand `z·f'(z)/f(z)` is not periodic;
   side-pairing leaves terms `ω·(2πi)⁻¹∮ f'/f` that must be shown to be *integers* — a winding
   number in disguise, needing the self-contained `exp`-lift trick (`φ(t) =
   f(γ t)·exp(-∫₀ᵗ f'/f)` has vanishing derivative).

Plus deceptively expensive plumbing: choosing a translated parallelogram whose boundary avoids
the (discrete) polar set and matching sums over it with `∑ᶠ` over
`ZSpan.fundamentalDomain L.basis`.  Realistic total: 2–3k lines of new Lean, weeks of
contributor time.  (Prior art worth mining: the PNT+ project `PrimeNumberTheoremAnd` built
rectangle-contour residue machinery that never landed in Mathlib.)  That investment is the
*right* one if the goal is elliptic function theory in Mathlib; it is overkill if the goal is
the three `sorry`s.

## Part II: the Euler route

### The chord (generic) case

Fix `s ∉ Λ` and slide a point along the line `z + w = s`: set `w = s - z` and

  `G_s(z) = ¼·slope(z)² - ℘(z) - ℘(s-z)`,  `slope(z) = (℘'(z) - ℘'(s-z)) / (℘(z) - ℘(s-z))`.

The addition theorem says `G_s ≡ ℘(s)` on its natural domain.  Euler's observation: `G_s' = 0`
follows *pointwise* from the differential equation `℘'² = 4℘³ - g₂℘ - g₃` and its derivative
`℘'' = 6℘² - g₂/2`, via a polynomial identity (`euler_slope_identity` below — proved here by
`linear_combination`, so the algebraic heart of the theorem is already machine-checked).
The analytic scaffolding this needs is only:

* chain/quotient rule differentiation (`HasDerivAt` API);
* the domain `U_s = {z ∉ Λ, s - z ∉ Λ, ℘(z) ≠ ℘(s-z)}` is *open* with *countable* complement
  (`Λ` is countable; `{℘(z) = ℘(s-z)}` is the zero set of a nonvanishing analytic function,
  hence discrete by `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`), hence path-connected
  by `Set.Countable.isPathConnected_compl_of_one_lt_rank`;
* zero derivative on an open connected set ⇒ constant (`IsOpen.is_const_of_fderiv_eq_zero`);
* the value of the constant, from the limit `z → 0` of `G_s` using the Laurent data
  `℘(z) = z⁻² + O(z²)`, `℘'(z) = -2z⁻³ + O(z)` (all extractable from Mathlib's
  `weierstrassPExcept` power-series API).

The Y-coordinate formula then falls out by differentiating the X-formula in `z` at *fixed* `w`
and applying a second `linear_combination` identity (`euler_tangency_identity`).

### The fiber lemma and the doubling case, *from* the addition formula

The outline (§5) derives `℘(z) = ℘(w) ↔ z ≡ ±w` and `℘'(z) = 0 ↔ 2z ∈ Λ` from the valence
formula.  Both instead follow from the chord formulas by limits:

* **Injectivity of `(℘, ℘')`.**  If `(℘, ℘')` agree at `a` and `b`, the X-formula computes
  `℘(a + u)` and `℘(b + u)` from the *same* data for all `u` outside a countable set, so
  `℘(a + u) = ℘(b + u)` everywhere by the identity theorem
  (`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`).  Let `u → -b`: the right side blows
  up (`℘` has a pole at `0`), so the left side must too, forcing `a - b ∈ Λ`.  The fiber lemma
  follows by the differential equation (`℘'(z) = ±℘'(w)`) and parity.
* **Zeros of `℘'`.**  If `℘'(z₀) = 0` with `z₀, 2z₀ ∉ Λ`, feed `w → z₀` into the X-formula:
  the left side tends to the finite `℘(2z₀)`, while
  `slope² = (4℘(w)³ - g₂℘(w) - g₃)/(℘(w) - ℘(z₀))²` — using `℘'(z₀)² = 0` — blows up because
  `℘(z₀)` is a *simple* root of the cubic (`weierstrassDiscriminant_ne_zero`, already proved
  sorry-free in `forward.lean`).  Contradiction; no valence formula.
* **Duplication.**  With `℘'(z) ≠ 0` secured, the tangent formulas
  (`weierstrassP_two_mul`, `derivWeierstrassP_two_mul` of the outline) are the limits `w → z`
  of the chord formulas: `chordSlope z w → ℘''(z)/℘'(z)` is a quotient of difference quotients.

Bottom line: this route replaces the outline's §3–§5 by the lemmas below, all of which sit on
existing Mathlib API — differentiation, isolated zeros, identity theorem, countable-complement
connectivity, and `Tendsto` calculus.  Rough estimate: 1–1.5k lines, no single hard step; the
worst items are the `z → 0` limit evaluation (`tendsto_eulerG_zero`) and `HasDerivAt`
bookkeeping (`hasDerivAt_eulerG`), both mechanical.  The outline's §3–§4 remain the right
long-term Mathlib contribution, but nothing below depends on them.
-/

open Complex Filter Topology Function PeriodPair

noncomputable section

namespace PeriodPair

variable (L : PeriodPair)

/-! ## §A Laurent data at `0` (provable today)

Sharper versions of the outline's §1, packaged for the limit computations below.  All content
is in Mathlib's `weierstrassPExcept` API: `℘(z) = z⁻² + ℘[L - 0](z)` (split the `l = 0` term
off the defining sum), `analyticAt_weierstrassPExcept`, and evenness kills the linear term. -/

/-- **Laurent expansion of `℘` and `℘'` at `0`, analytic-remainder form.**  There is a single
analytic `g` with `g(0) = g'(0) = 0` such that `℘(z) = z⁻² + g(z)` and `℘'(z) = -2z⁻³ + g'(z)`
off `0`.  (`g = ℘[L - 0]` restricted near `0`; `deriv g 0 = 0` because `g` is even.) -/
theorem exists_laurent_weierstrassP :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ deriv g 0 = 0 ∧
      (∀ z : ℂ, z ≠ 0 → ℘[L] z = (z ^ 2)⁻¹ + g z) ∧
      (∀ z : ℂ, z ≠ 0 → ℘'[L] z = -2 * (z ^ 3)⁻¹ + deriv g z) := by
  sorry

/-- `℘` blows up (in norm) at every lattice point — the pole is genuine.  Used for the
"pole detection" step of `sub_mem_lattice_of_weierstrassP_eq`.  From
`exists_laurent_weierstrassP` at `0` and periodicity elsewhere. -/
theorem tendsto_norm_weierstrassP_atTop {l₀ : ℂ} (h : l₀ ∈ L.lattice) :
    Tendsto (fun z ↦ ‖℘[L] z‖) (𝓝[≠] l₀) atTop := by
  sorry

/-! ## §B The algebraic heart (proved, not sorried)

Both differential identities driving the Euler argument are polynomial consequences of the two
Weierstrass equations.  They are proved here by `linear_combination`, so the *mathematical*
content of the addition theorem is already verified; everything else in this file is analytic
bookkeeping. -/

/-- **Euler's identity (X-coordinate).**  If `(x₁, y₁)` and `(x₂, y₂)` satisfy
`y² = 4x³ - g₂x - g₃`, then `N'D - ND' = 2D³` where `N = y₁ - y₂`, `D = x₁ - x₂` and primes are
taken along the flow `x₁' = y₁, x₂' = -y₂, y₁' = 6x₁² - g₂/2, y₂' = -(6x₂² - g₂/2)` — i.e. the
numerator of `d/dz [¼(N/D)²  - x₁ - x₂]` vanishes.  This is why `eulerG` is locally constant. -/
theorem euler_slope_identity {x₁ x₂ y₁ y₂ g₂ g₃ : ℂ}
    (h₁ : y₁ ^ 2 = 4 * x₁ ^ 3 - g₂ * x₁ - g₃)
    (h₂ : y₂ ^ 2 = 4 * x₂ ^ 3 - g₂ * x₂ - g₃) :
    (6 * (x₁ ^ 2 + x₂ ^ 2) - g₂) * (x₁ - x₂) - (y₁ - y₂) * (y₁ + y₂)
      = 2 * (x₁ - x₂) ^ 3 := by
  linear_combination h₂ - h₁

/-- **Euler's identity (Y-coordinate).**  The analogous polynomial identity showing that the
`z`-derivative of the chord slope (at fixed `w`) equals `-slope²/2 + 4x₁ + 2x₂`; differentiating
the X-formula and substituting this yields the Y-formula.  `N = y₁ - y₂`, `D = x₁ - x₂`. -/
theorem euler_tangency_identity {x₁ x₂ y₁ y₂ g₂ g₃ : ℂ}
    (h₁ : y₁ ^ 2 = 4 * x₁ ^ 3 - g₂ * x₁ - g₃)
    (h₂ : y₂ ^ 2 = 4 * x₂ ^ 3 - g₂ * x₂ - g₃) :
    2 * ((6 * x₁ ^ 2 - g₂ / 2) * (x₁ - x₂) - (y₁ - y₂) * y₁)
      = -(y₁ - y₂) ^ 2 + 2 * (4 * x₁ + 2 * x₂) * (x₁ - x₂) ^ 2 := by
  linear_combination h₂ - h₁

/-! ## §C Euler's function and its domain -/

/-- The chord slope along the anti-diagonal `z + w = s`, as a function of `z`. -/
def eulerSlope (s z : ℂ) : ℂ := (℘'[L] z - ℘'[L] (s - z)) / (℘[L] z - ℘[L] (s - z))

/-- Euler's function: the candidate value for `℘(s)`, as a function of the split point `z`.
The addition theorem is `eulerG s ≡ ℘ s` on `eulerDomain s`. -/
def eulerG (s z : ℂ) : ℂ := L.eulerSlope s z ^ 2 / 4 - ℘[L] z - ℘[L] (s - z)

/-- The natural domain of `eulerG s`: both points off the lattice and distinct X-coordinates. -/
def eulerDomain (s : ℂ) : Set ℂ :=
  {z | z ∉ L.lattice ∧ s - z ∉ L.lattice ∧ ℘[L] z ≠ ℘[L] (s - z)}

/-- `eulerDomain` is open: `Λ` is closed (`isClosed_lattice`) and `℘` is continuous off it. -/
theorem isOpen_eulerDomain (s : ℂ) : IsOpen (L.eulerDomain s) := by
  sorry

/-- For `s ∉ Λ` the complement of `eulerDomain s` is **countable**: `Λ` and `s - Λ` are
countable (`latticeEquivProd`), and `{℘(z) = ℘(s - z)}` is the zero set of an analytic
function on the connected open set `{z ∉ Λ, s - z ∉ Λ}` that is not identically zero (it blows
up as `z → 0` by `tendsto_norm_weierstrassP_atTop`, since `s ∉ Λ` keeps `℘(s - z)` bounded
there) — hence has only isolated zeros (`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`),
and a discrete subset of a second-countable space is countable. -/
theorem countable_compl_eulerDomain {s : ℂ} (hs : s ∉ L.lattice) :
    Set.Countable (L.eulerDomain s)ᶜ := by
  sorry

/-- Open with countable complement ⇒ preconnected, via
`Set.Countable.isPathConnected_compl_of_one_lt_rank` (`rank ℝ ℂ = 2 > 1`). -/
theorem isPreconnected_eulerDomain {s : ℂ} (hs : s ∉ L.lattice) :
    IsPreconnected (L.eulerDomain s) := by
  sorry

/-- `0` is an accumulation point of `eulerDomain s` (any ball is uncountable, the complement is
countable).  Needed so the limit `z → 0` sees the domain. -/
theorem mem_closure_eulerDomain {s : ℂ} (hs : s ∉ L.lattice) :
    (0 : ℂ) ∈ closure (L.eulerDomain s) := by
  sorry

/-! ## §D `eulerG` is constant, and the constant is `℘ s` -/

/-- **The Euler derivative computation.**  On its domain, `eulerG s` has vanishing derivative.
Proof plan: `℘`, `℘'` are differentiable off `Λ` (`analyticOnNhd_weierstrassP`,
`analyticOnNhd_derivWeierstrassP`), `deriv ℘ = ℘'` (`deriv_weierstrassP`) and
`deriv ℘' = 6℘² - g₂/2` (outline §1, `deriv_derivWeierstrassP`); the chain rule gives the
derivative of `z ↦ ℘(s - z)` a sign flip.  Assemble with the quotient rule; the resulting
rational expression vanishes by `euler_slope_identity` applied with
`h₁ = derivWeierstrassP_sq z`, `h₂ = derivWeierstrassP_sq (s - z)`. -/
theorem hasDerivAt_eulerG {s z : ℂ} (hz : z ∈ L.eulerDomain s) :
    HasDerivAt (L.eulerG s) 0 z := by
  sorry

/-- **Evaluation of the constant.**  As `z → 0` through the domain, `eulerG s z → ℘ s`.
Proof plan: write `℘(z) = z⁻² + g(z)`, `℘'(z) = -2z⁻³ + g'(z)` (`exists_laurent_weierstrassP`)
and expand:
`slope = (-2z⁻³ + O(1)) / (z⁻² + O(1)) = (-2/z)·(1 + O(z²))⁻¹·(1 + O(z³))`, so
`slope²/4 = z⁻² + ℘(s) + ℘'(s)·z·(-1) + o(z)`-type cancellation; the `z⁻²` cancels against
`-℘(z)` and the constant term assembles to `℘(s)` using `g(0) = g'(0) = 0` and continuity of
`℘, ℘'` at `s`.  Mechanically: clear denominators, express everything as a ratio of functions
continuous at `0`, and apply `Tendsto` arithmetic — no new theory, just care. -/
theorem tendsto_eulerG_zero {s : ℂ} (hs : s ∉ L.lattice) :
    Tendsto (L.eulerG s) (𝓝[L.eulerDomain s] 0) (𝓝 (℘[L] s)) := by
  sorry

/-- **The addition theorem, Euler form.**  Combining: `eulerG s` is differentiable with zero
derivative on the open preconnected `eulerDomain s`, hence constant
(`IsOpen.is_const_of_fderiv_eq_zero`); the constant is `℘ s` by `tendsto_eulerG_zero` and
`mem_closure_eulerDomain` (constants propagate to limit points along the domain). -/
theorem eulerG_eq_weierstrassP {s : ℂ} (hs : s ∉ L.lattice) {z : ℂ}
    (hz : z ∈ L.eulerDomain s) :
    L.eulerG s z = ℘[L] s := by
  sorry

/-- `weierstrassP_add` — the first `sorry` of `addition.lean` — is pure algebra from
`eulerG_eq_weierstrassP` at `s = z + w`.  (Real proof, no sorry.) -/
example {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z + w ∉ L.lattice) (hx : ℘[L] z ≠ ℘[L] w) :
    ℘[L] (z + w)
      = ((℘'[L] z - ℘'[L] w) / (2 * (℘[L] z - ℘[L] w))) ^ 2 - ℘[L] z - ℘[L] w := by
  have hz' : z ∈ L.eulerDomain (z + w) :=
    ⟨hz, by rwa [add_sub_cancel_left], by rwa [add_sub_cancel_left]⟩
  have h := L.eulerG_eq_weierstrassP hzw hz'
  rw [eulerG, eulerSlope, add_sub_cancel_left] at h
  have hne : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr hx
  rw [← h]
  field_simp
  ring

/-! ## §E The Y-coordinate, by differentiating in `z` at fixed `w` -/

/-- Derivative of the fixed-`w` chord slope (`chordSlope` from `addition_outline.lean`), by the
quotient rule.  Provable today. -/
theorem hasDerivAt_chordSlope {z w : ℂ} (hz : z ∉ L.lattice) (hx : ℘[L] z ≠ ℘[L] w) :
    HasDerivAt (fun u ↦ L.chordSlope u w)
      (((6 * ℘[L] z ^ 2 - L.g₂ / 2) * (℘[L] z - ℘[L] w)
          - (℘'[L] z - ℘'[L] w) * ℘'[L] z) / (℘[L] z - ℘[L] w) ^ 2) z := by
  sorry

/-- **Y-formula from X-formula.**  Once the X-formula holds on the (open) chord locus, both
sides are differentiable in `z` there; differentiating (`hasDerivAt_chordSlope`,
`deriv_weierstrassP`) and simplifying with `euler_tangency_identity` gives exactly
`derivWeierstrassP_add` — the second `sorry` of `addition.lean`.  Stated conditionally to make
the dependency explicit. -/
theorem derivWeierstrassP_add_of_weierstrassP_add
    (hX : ∀ z w : ℂ, z ∉ L.lattice → w ∉ L.lattice → z + w ∉ L.lattice →
      ℘[L] z ≠ ℘[L] w →
      ℘[L] (z + w) = L.chordSlope z w ^ 2 / 4 - ℘[L] z - ℘[L] w)
    {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) (hzw : z + w ∉ L.lattice)
    (hx : ℘[L] z ≠ ℘[L] w) :
    ℘'[L] (z + w) = -(L.chordSlope z w * (℘[L] (z + w) - ℘[L] z) + ℘'[L] z) := by
  sorry

/-! ## §F Fibers of `℘` from the addition formula (replaces the valence-formula uses of §5)

These two lemmas recover the outline's §5 *without* any counting argument. -/

/-- **Translation principle.**  If `a` and `b` have the same `(℘, ℘')`-image, then `℘(a + ·)`
and `℘(b + ·)` agree wherever both are defined.  Proof plan: for `u` outside a countable bad
set (lattice translates and `{℘ u = ℘ a}`, countable as in `countable_compl_eulerDomain`), the
X-formula computes `℘(a + u)` and `℘(b + u)` from the identical data
`(℘ a, ℘' a, ℘ u, ℘' u) = (℘ b, ℘' b, ℘ u, ℘' u)`.  Both sides are analytic in `u` on the open
connected complement of `(Λ - a) ∪ (Λ - b)`; conclude by
`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`. -/
theorem weierstrassP_add_right_eq {a b : ℂ} (ha : a ∉ L.lattice) (hb : b ∉ L.lattice)
    (hP : ℘[L] a = ℘[L] b) (hP' : ℘'[L] a = ℘'[L] b) :
    ∀ u : ℂ, a + u ∉ L.lattice → b + u ∉ L.lattice → ℘[L] (a + u) = ℘[L] (b + u) := by
  sorry

/-- **Injectivity of `(℘, ℘')` on `(ℂ ∖ Λ)/Λ`.**  Let `u → -b` in
`weierstrassP_add_right_eq`: if `a - b ∉ Λ` then `℘(a + u) → ℘(a - b)` stays bounded while
`℘(b + u) = ℘(u + b) → ∞` (`tendsto_norm_weierstrassP_atTop` at `0`); contradiction.  (The
approach `u = -b + ε` stays in the allowed set for all small `ε ≠ 0` because `Λ` is closed and
`a - b ∉ Λ`.) -/
theorem sub_mem_lattice_of_weierstrassP_eq {a b : ℂ} (ha : a ∉ L.lattice) (hb : b ∉ L.lattice)
    (hP : ℘[L] a = ℘[L] b) (hP' : ℘'[L] a = ℘'[L] b) :
    a - b ∈ L.lattice := by
  sorry

/-- The outline's fiber lemma `weierstrassP_eq_weierstrassP_iff` (forward direction) now
follows with **no valence formula**: the differential equation forces `℘'(z) = ±℘'(w)`, and
each sign reduces to `sub_mem_lattice_of_weierstrassP_eq` (for `-`, against `-w`, using
evenness of `℘` and oddness of `℘'`).  Real proof modulo the two lemmas above and parity. -/
example {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) (h : ℘[L] z = ℘[L] w) :
    z - w ∈ L.lattice ∨ z + w ∈ L.lattice := by
  have hsq : ℘'[L] z ^ 2 = ℘'[L] w ^ 2 := by
    rw [L.derivWeierstrassP_sq z hz, L.derivWeierstrassP_sq w hw, h]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h' | h'
  · exact Or.inl (L.sub_mem_lattice_of_weierstrassP_eq hz hw h h')
  · refine Or.inr ?_
    have hw' : -w ∉ L.lattice := fun hmem ↦ hw (by simpa using neg_mem hmem)
    have h₁ : ℘[L] z = ℘[L] (-w) := by rw [L.weierstrassP_neg]; exact h
    have h₂ : ℘'[L] z = ℘'[L] (-w) := by rw [L.derivWeierstrassP_neg]; exact h'
    simpa [sub_neg_eq_add] using L.sub_mem_lattice_of_weierstrassP_eq hz hw' h₁ h₂

/-! ## §G Zeros of `℘'` and the doubling case, from the addition formula -/

/-- **Simple-root lemma.**  Any root of `4X³ - g₂X - g₃` is simple, because
`Δ = g₂³ - 27g₃² ≠ 0` (`weierstrassDiscriminant_ne_zero`, sorry-free in `forward.lean`).
Pure algebra: the resultant/Bézout identity expresses `g₂³ - 27g₃²` as an explicit polynomial
combination of `4e³ - g₂e - g₃` and `12e² - g₂`, so both vanishing forces `Δ = 0`.
(Provable by `linear_combination` once the two cofactors are written down.) -/
theorem cubic_deriv_ne_zero_of_root {e : ℂ} (he : 4 * e ^ 3 - L.g₂ * e - L.g₃ = 0) :
    12 * e ^ 2 - L.g₂ ≠ 0 := by
  sorry

/-- **Blow-up of the squared chord slope at a critical point.**  If `℘'(z₀) = 0`, then by the
differential equation `chordSlope z₀ w ^ 2 = (4℘(w)³ - g₂℘(w) - g₃)/(℘(w) - ℘(z₀))²`, and
`4X³ - g₂X - g₃ = (X - ℘(z₀))·q(X)` with `q(℘(z₀)) = 12℘(z₀)² - g₂ ≠ 0`
(`cubic_deriv_ne_zero_of_root`; note `q` here is the *depressed* cofactor, whose value at the
root is `12e² - g₂` after using `he` — a `ring` computation).  So the slope squared behaves
like `q(℘ w)/(℘ w - ℘ z₀) → ∞` as `w → z₀` through `{℘ w ≠ ℘ z₀}`. -/
theorem tendsto_norm_chordSlope_sq_atTop {z₀ : ℂ} (hz : z₀ ∉ L.lattice)
    (h0 : ℘'[L] z₀ = 0) :
    Tendsto (fun w ↦ ‖L.chordSlope z₀ w ^ 2‖)
      (𝓝[{w | w ∉ L.lattice ∧ ℘[L] w ≠ ℘[L] z₀}] z₀) atTop := by
  sorry

/-- **`℘'` vanishes only at 2-torsion — no valence formula.**  Suppose `℘'(z) = 0` but
`2z ∉ Λ`.  Feed `w → z` into the X-formula (the punctured approach stays in the chord locus:
`℘(w) ≠ ℘(z)` eventually since `℘ - ℘(z)` has isolated zeros, and `w, z + w ∉ Λ` are open
conditions): the left side `℘(z + w) → ℘(2z)` is finite, but the right side
`chordSlope²/4 - ℘z - ℘w → ∞` by `tendsto_norm_chordSlope_sq_atTop`.  Contradiction.
This is the forward direction of the outline's `derivWeierstrassP_eq_zero_iff`. -/
theorem two_mul_mem_lattice_of_derivWeierstrassP_eq_zero {z : ℂ} (hz : z ∉ L.lattice)
    (h0 : ℘'[L] z = 0) :
    2 * z ∈ L.lattice := by
  sorry

/-- **Tangent slope as a limit of chord slopes.**  When `℘'(z) ≠ 0`, the chord slope tends to
`℘''(z)/℘'(z)` as `w → z`: write it as a quotient of difference quotients
`[(℘'(w) - ℘'(z))/(w - z)] / [(℘(w) - ℘(z))/(w - z)]` and use `deriv_derivWeierstrassP`
(numerator) and `deriv_weierstrassP` (denominator, nonzero limit).  The punctured filter is
legitimate: `℘ - ℘(z)` has a *simple* zero at `z` (its derivative is `℘'(z) ≠ 0`), so
`℘(w) ≠ ℘(z)` eventually. -/
theorem tendsto_chordSlope_self {z : ℂ} (hz : z ∉ L.lattice) (h0 : ℘'[L] z ≠ 0) :
    Tendsto (fun w ↦ L.chordSlope z w) (𝓝[≠] z)
      (𝓝 ((6 * ℘[L] z ^ 2 - L.g₂ / 2) / ℘'[L] z)) := by
  sorry

/-!
### Assembling the doubling case

With the above, the outline's remaining §6 statements close as limits — no new theory:

* `weierstrassP_two_mul` : take `w → z` in the X-formula.  Left side `℘(z + w) → ℘(2z)` by
  continuity (`2z ∉ Λ`); right side tends to `(℘''(z)/(2℘'(z)))² - 2℘(z)` by
  `tendsto_chordSlope_self` (the hypothesis `℘'(z) ≠ 0` is
  `two_mul_mem_lattice_of_derivWeierstrassP_eq_zero`, contraposed); uniqueness of limits.
* `derivWeierstrassP_two_mul` : same limit in the Y-formula
  (`derivWeierstrassP_add_of_weierstrassP_add`), using continuity of `℘'` at `2z`.
* `toPoint_add_of_weierstrassP_eq` (the third `sorry` of `addition.lean`): from
  `℘ z = ℘ w` and `z + w ∉ Λ`, the §F fiber lemma gives `z - w ∈ Λ` (the `z + w ∈ Λ` branch is
  excluded), so `toPoint w = toPoint z` and `toPoint (z + w) = toPoint (2z)`
  (`toPoint_add_mem`); `℘'(z) ≠ 0` puts us in Mathlib's
  `WeierstrassCurve.Affine.Point.add_of_Y_ne` case (`y₁ = ½℘'(z) ≠ -½℘'(z) = negY`), whose
  `slope_of_Y_ne` is `(3x² + a₄)/(2y) = (3℘z² - g₂/4)/℘'z = ½·℘''(z)/℘'(z)` — matching the
  duplication formulas exactly as the chord case was wired in `addition.lean`.

### Suggested proving order

1. §B is done.  §A (`exists_laurent_weierstrassP`, `tendsto_norm_weierstrassP_atTop`) — pure
   Mathlib API work, independent of everything else.
2. §C topology (`isOpen_`, `countable_compl_`, `isPreconnected_`, `mem_closure_`) — independent.
3. `hasDerivAt_eulerG` (§D) — the biggest single item, but mechanical `HasDerivAt` algebra;
   needs the outline's §1 `deriv_derivWeierstrassP` (provable today).
4. `tendsto_eulerG_zero` (§D) — the fiddliest item; pure `Tendsto` calculus over §A.
5. `eulerG_eq_weierstrassP` — glue (constant + limit); then `weierstrassP_add` is the §D
   example, and `derivWeierstrassP_add` follows from §E.
6. §F, §G in order — each is a limit/identity-theorem argument over the previous ones; then
   the doubling case assembles as described above, and `toPoint_add` in `addition.lean` is
   sorry-free.
-/

-- suggests it should be 1-1.5k lines as opposed to 2-3k with residue-theorem route.

end PeriodPair
