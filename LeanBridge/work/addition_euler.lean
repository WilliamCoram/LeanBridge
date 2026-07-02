import LeanBridge.work.forward

/-!
# The Euler route to the addition theorem: no contour integration

This file does two things.

**Part I (this docstring)** records why the classical route — residues on the period
parallelogram, the valence formula, and the Abel relation — would be the expensive part of any
formalisation plan.

**Part II (the declarations below)** details an alternative proof of the addition theorem,
going back to Euler's differential-equation argument, in which *every* analytic ingredient is
already in Mathlib.  Somewhat surprisingly, the fiber lemma and the doubling case — the two
places where the valence formula seemed unavoidable — can also be recovered *from* the addition
formula by elementary limit arguments, so the entire contour-integration layer can be bypassed
for the purpose of closing the three `sorry`s of `addition.lean`.

## Part I: why the valence-formula route is hard

What the current Mathlib pin has:

* the full circle-integral calculus `∮ (z - w)^n` (`circleIntegral.integral_sub_zpow_of_ne`,
  `circleIntegral.integral_sub_inv_of_mem_ball` giving `2πi`);
* Cauchy–Goursat for **axis-aligned rectangles only**
  (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`);
* meromorphic normal forms and divisors (`meromorphicOrderAt_eq_int_iff`,
  `MeromorphicOn.divisor`), `MeromorphicAt.deriv`, `MeromorphicAt.div`.

What it does **not** have: any residue theorem, any argument principle, winding numbers.
Concretely, two walls stand between the residue-theorem statements and a proof:

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

Classically one derives `℘(z) = ℘(w) ↔ z ≡ ±w` and `℘'(z) = 0 ↔ 2z ∈ Λ` from the valence
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
  (`weierstrassP_two_mul`, `derivWeierstrassP_two_mul`, §H) are the limits `w → z`
  of the chord formulas: `chordSlope z w → ℘''(z)/℘'(z)` is a quotient of difference quotients.

Bottom line: this route replaces the valence-formula machinery by the lemmas below, all of
which sit on existing Mathlib API — differentiation, isolated zeros, identity theorem,
countable-complement connectivity, and `Tendsto` calculus.  The residue theorem and valence
formula remain the right long-term Mathlib contribution, but nothing below depends on them.
-/

open Complex Filter Topology Function PeriodPair

noncomputable section

namespace PeriodPair

variable (L : PeriodPair)

/-! ## §A Laurent data at `0`

Laurent data at the pole, packaged for the limit computations below.  All content
is in Mathlib's `weierstrassPExcept` API: `℘(z) = z⁻² + ℘[L - 0](z)` (split the `l = 0` term
off the defining sum), `analyticAt_weierstrassPExcept`, and evenness kills the linear term. -/

/-- **Laurent expansion of `℘` and `℘'` at `0`, analytic-remainder form.**  There is a single
analytic `g` with `g(0) = g'(0) = 0` such that `℘(z) = z⁻² + g(z)` (globally — junk values
conspire at the lattice) and `℘'(z) = -2z⁻³ + g'(z)` off the lattice.  (The witness is
`g = ℘[L - 0]`; `deriv g 0 = 0` because `g` is even.  The `℘'` clause needs `z ∉ Λ` rather than
`z ≠ 0`: at other lattice points `℘'` and `deriv g` are junk `0` while `-2z⁻³` is not.) -/
theorem exists_laurent_weierstrassP :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ deriv g 0 = 0 ∧
      (∀ z : ℂ, ℘[L] z = (z ^ 2)⁻¹ + g z) ∧
      (∀ z : ℂ, z ∉ L.lattice → ℘'[L] z = -2 * (z ^ 3)⁻¹ + deriv g z) := by
  refine ⟨L.weierstrassPExcept 0, L.analyticAt_weierstrassPExcept 0,
    L.weierstrassPExcept_zero 0, ?_, fun z ↦ ?_, fun z hz ↦ ?_⟩
  · -- `deriv ℘[L - 0] 0 = ℘'[L - 0] 0 = 0` (evenness).
    rw [L.deriv_weierstrassPExcept_same 0]
    exact L.derivWeierstrassPExcept_zero_zero
  · -- Split the `l = 0` term off the defining sum: `weierstrassPExcept_add`.
    have h := L.weierstrassPExcept_add 0 z
    simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, div_zero, one_div] at h
    rw [← h]
    ring
  · -- Same splitting for `℘'`; off the lattice `deriv ℘[L - 0] = ℘'[L - 0]`.
    have hd : deriv (L.weierstrassPExcept 0) z = L.derivWeierstrassPExcept 0 z :=
      L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 (by simp [hz])
    have h := L.derivWeierstrassPExcept_sub 0 z
    simp only [ZeroMemClass.coe_zero, sub_zero] at h
    rw [← h, hd]
    ring

/-- `℘` blows up (in norm) at every lattice point — the pole is genuine.  Used for the
"pole detection" step of `sub_mem_lattice_of_weierstrassP_eq`.  From
`exists_laurent_weierstrassP` at `0` and periodicity elsewhere. -/
theorem tendsto_norm_weierstrassP_atTop {l₀ : ℂ} (h : l₀ ∈ L.lattice) :
    Tendsto (fun z ↦ ‖℘[L] z‖) (𝓝[≠] l₀) atTop := by
  obtain ⟨g, hg, -, -, hP, -⟩ := L.exists_laurent_weierstrassP
  -- The case `l₀ = 0`: `‖℘ z‖ ≥ ‖z⁻²‖ - ‖g z‖` with `g` bounded near `0`.
  have h0 : Tendsto (fun z : ℂ ↦ ‖℘[L] z‖) (𝓝[≠] (0 : ℂ)) atTop := by
    have hinv : Tendsto (fun z : ℂ ↦ ‖(z ^ 2)⁻¹‖) (𝓝[≠] (0 : ℂ)) atTop := by
      have h1 : Tendsto (fun z : ℂ ↦ ‖z‖ ^ 2) (𝓝[≠] (0 : ℂ)) (𝓝[>] (0 : ℝ)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have h2 : Tendsto (fun z : ℂ ↦ ‖z‖ ^ 2) (𝓝 0) (𝓝 (‖(0 : ℂ)‖ ^ 2)) :=
            (continuous_norm.pow 2).tendsto 0
          simpa using h2.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with z hz
          exact Set.mem_Ioi.mpr (pow_pos (norm_pos_iff.mpr hz) 2)
      refine (tendsto_inv_nhdsGT_zero.comp h1).congr fun z ↦ ?_
      simp [Function.comp_apply]
    have hgc : Tendsto (fun z ↦ ‖g z‖) (𝓝 (0 : ℂ)) (𝓝 ‖g 0‖) := hg.continuousAt.norm
    have hgM : ∀ᶠ z in 𝓝 (0 : ℂ), ‖g z‖ ≤ ‖g 0‖ + 1 :=
      hgc.eventually (eventually_le_nhds (lt_add_one _))
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-(‖g 0‖ + 1)) hinv)
    filter_upwards [hgM.filter_mono nhdsWithin_le_nhds] with z hgz
    have h1 : ‖(z ^ 2)⁻¹‖ - ‖g z‖ ≤ ‖(z ^ 2)⁻¹ + g z‖ := by
      have h2 := norm_sub_norm_le ((z ^ 2)⁻¹) (-(g z))
      rwa [norm_neg, sub_neg_eq_add] at h2
    rw [hP z]
    linarith
  -- Transfer along the translation `z ↦ z - l₀`, using periodicity.
  have hper : ∀ z : ℂ, ℘[L] (z - l₀) = ℘[L] z := fun z ↦ L.weierstrassP_sub_coe z ⟨l₀, h⟩
  have hmap : Tendsto (fun z : ℂ ↦ z - l₀) (𝓝[≠] l₀) (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h2 : Tendsto (fun z : ℂ ↦ z - l₀) (𝓝 l₀) (𝓝 (l₀ - l₀)) :=
        (continuous_sub_right l₀).tendsto l₀
      simpa using h2.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
      exact sub_ne_zero.mpr hz
  refine (h0.comp hmap).congr fun z ↦ ?_
  simp only [Function.comp_apply]
  rw [hper z]

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
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨hz1, hsz, hne⟩ := hz
  have h1 : ∀ᶠ w in 𝓝 z, w ∉ L.lattice := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz1] with w hw
    exact hw
  have h2 : ∀ᶠ w in 𝓝 z, s - w ∉ L.lattice := by
    have hc : ContinuousAt (fun w : ℂ ↦ s - w) z :=
      (continuous_const.sub continuous_id).continuousAt
    filter_upwards [hc.eventually_mem (L.isClosed_lattice.isOpen_compl.mem_nhds hsz)] with w hw
    exact hw
  have hc1 : ContinuousAt ℘[L] z := (L.analyticOnNhd_weierstrassP z hz1).continuousAt
  have hc2 : ContinuousAt (fun w : ℂ ↦ ℘[L] (s - w)) z := by
    have hb : ContinuousAt ℘[L] (s - z) :=
      (L.analyticOnNhd_weierstrassP (s - z) hsz).continuousAt
    exact hb.comp (continuous_const.sub continuous_id).continuousAt
  have h3 : ∀ᶠ w in 𝓝 z, ℘[L] w ≠ ℘[L] (s - w) := by
    have hne0 : ℘[L] z - ℘[L] (s - z) ≠ 0 := sub_ne_zero.mpr hne
    filter_upwards [(hc1.sub hc2).eventually_ne hne0] with w hw
    exact sub_ne_zero.mp hw
  filter_upwards [h1, h2, h3] with w hw1 hw2 hw3
  exact ⟨hw1, hw2, hw3⟩

/-- The period lattice is countable (as a set of complex numbers): it is in bijection with
`ℤ × ℤ` via `latticeEquivProd`. -/
theorem countable_lattice : Set.Countable (L.lattice : Set ℂ) := by
  haveI : Countable L.lattice := Countable.of_equiv _ L.latticeEquivProd.symm.toEquiv
  refine (Set.countable_range fun l : L.lattice ↦ (l : ℂ)).mono ?_
  rintro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

/-- For `s ∉ Λ` the complement of `eulerDomain s` is **countable**: `Λ` and `s - Λ` are
countable (`countable_lattice`), and `{℘(z) = ℘(s - z)}` is the zero set of an analytic
function on the connected open set `{z ∉ Λ, s - z ∉ Λ}` that is not identically zero (it blows
up as `z → 0` by `tendsto_norm_weierstrassP_atTop`, since `s ∉ Λ` keeps `℘(s - z)` bounded
there) — hence has only isolated zeros (`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` +
the identity theorem), so it is a discrete subset of a hereditarily Lindelöf space, hence
countable (`IsLindelof.countable`). -/
theorem countable_compl_eulerDomain {s : ℂ} (hs : s ∉ L.lattice) :
    Set.Countable (L.eulerDomain s)ᶜ := by
  -- The two "bad translate" sets and their union `U`.
  set U : Set ℂ := {z : ℂ | z ∈ L.lattice ∨ s - z ∈ L.lattice} with hUdef
  have hcU : Set.Countable U := by
    have h2 : Set.Countable {z : ℂ | s - z ∈ L.lattice} := by
      have hinj : Function.Injective fun z : ℂ ↦ s - z := fun a b hab ↦ by
        simpa [sub_sub_cancel] using congrArg (fun t : ℂ ↦ s - t) hab
      exact L.countable_lattice.preimage hinj
    refine (L.countable_lattice.union h2).mono ?_
    rintro z (hz | hz)
    exacts [Set.mem_union_left _ hz, Set.mem_union_right _ hz]
  -- `Uᶜ` is open and preconnected (complement of a countable set).
  have hopenU : IsOpen Uᶜ := by
    have hcl : IsClosed ((L.lattice : Set ℂ) ∪ (fun z : ℂ ↦ s - z) ⁻¹' (L.lattice : Set ℂ)) :=
      L.isClosed_lattice.union
        (L.isClosed_lattice.preimage (continuous_const.sub continuous_id))
    exact hcl.isOpen_compl
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
    exact_mod_cast one_lt_two
  have hUpre : IsPreconnected Uᶜ :=
    (hcU.isPathConnected_compl_of_one_lt_rank hrank).isConnected.isPreconnected
  -- The difference `℘(z) - ℘(s - z)` is analytic on `Uᶜ`.
  have hFan : AnalyticOnNhd ℂ (fun z : ℂ ↦ ℘[L] z - ℘[L] (s - z)) Uᶜ := by
    intro x hx
    have hx1 : x ∉ L.lattice := fun h ↦ hx (Or.inl h)
    have hx2 : s - x ∉ L.lattice := fun h ↦ hx (Or.inr h)
    have ha1 : AnalyticAt ℂ ℘[L] x := L.analyticOnNhd_weierstrassP x hx1
    have ha2 : AnalyticAt ℂ (fun z : ℂ ↦ ℘[L] (s - z)) x := by
      have hb : AnalyticAt ℂ ℘[L] (s - x) := L.analyticOnNhd_weierstrassP (s - x) hx2
      exact hb.comp (analyticAt_const.sub analyticAt_id)
    exact ha1.sub ha2
  -- The difference is not identically zero: near `0`, `℘(z)` blows up while `℘(s - z)` stays
  -- bounded.
  have hz₁ : ∃ z₁, z₁ ∈ Uᶜ ∧ ℘[L] z₁ ≠ ℘[L] (s - z₁) := by
    have hC : Tendsto (fun z ↦ ‖℘[L] z‖) (𝓝[≠] (0 : ℂ)) atTop :=
      L.tendsto_norm_weierstrassP_atTop (zero_mem _)
    have hcont : Tendsto (fun z : ℂ ↦ ‖℘[L] (s - z)‖) (𝓝 0) (𝓝 ‖℘[L] (s - 0)‖) := by
      have h℘ : ContinuousAt ℘[L] (s - 0) :=
        (L.analyticOnNhd_weierstrassP (s - 0) (by simpa using hs)).continuousAt
      exact (h℘.comp ((continuous_const.sub continuous_id).continuousAt)).norm
    have h1 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖℘[L] (s - 0)‖ + 1 < ‖℘[L] z‖ :=
      hC.eventually_gt_atTop _
    have h2 : ∀ᶠ z in 𝓝 (0 : ℂ), ‖℘[L] (s - z)‖ ≤ ‖℘[L] (s - 0)‖ + 1 :=
      hcont.eventually (eventually_le_nhds (lt_add_one _))
    have h3 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds
        (L.compl_lattice_sdiff_singleton_mem_nhds 0), self_mem_nhdsWithin] with z hz1 hz2
      exact fun hzΛ ↦ hz1 ⟨hzΛ, hz2⟩
    have h4 : ∀ᶠ z in 𝓝 (0 : ℂ), s - z ∉ L.lattice := by
      have hc : ContinuousAt (fun z : ℂ ↦ s - z) 0 :=
        (continuous_const.sub continuous_id).continuousAt
      have hmem : (↑L.lattice : Set ℂ)ᶜ ∈ 𝓝 (s - 0) :=
        L.isClosed_lattice.isOpen_compl.mem_nhds (by simpa using hs)
      filter_upwards [hc.eventually_mem hmem] with z hz
      exact hz
    obtain ⟨z₁, h1z, h2z, h3z, h4z⟩ := (h1.and ((h2.filter_mono nhdsWithin_le_nhds).and
      (h3.and (h4.filter_mono nhdsWithin_le_nhds)))).exists
    refine ⟨z₁, fun hor ↦ hor.elim h3z h4z, fun heq ↦ ?_⟩
    rw [heq] at h1z
    exact absurd h1z (not_lt.mpr h2z)
  -- The zero set `Z` is discrete: each zero is isolated, else the identity theorem forces the
  -- difference to vanish identically on the connected `Uᶜ`, contradicting `hz₁`.
  set Z : Set ℂ := {z : ℂ | z ∈ Uᶜ ∧ ℘[L] z = ℘[L] (s - z)} with hZdef
  have hdisc : DiscreteTopology Z := by
    rw [discreteTopology_subtype_iff]
    intro x hx
    rw [inf_principal_eq_bot]
    obtain ⟨hxV, hxF⟩ := hx
    rcases (hFan x hxV).eventually_eq_zero_or_eventually_ne_zero with hcase | hcase
    · exfalso
      obtain ⟨z₁, hz₁V, hz₁ne⟩ := hz₁
      have hev : (fun z : ℂ ↦ ℘[L] z - ℘[L] (s - z)) =ᶠ[𝓝 x] 0 := by
        filter_upwards [hcase] with w hw
        simpa using hw
      have heq := hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUpre hxV hev
      exact hz₁ne (sub_eq_zero.mp (by simpa using heq hz₁V))
    · filter_upwards [hcase] with w hw
      exact fun hwZ ↦ hw (sub_eq_zero.mpr hwZ.2)
  have hcZ : Set.Countable Z := (HereditarilyLindelofSpace.isLindelof Z).countable hdisc
  -- Assemble: the complement of the domain is contained in `U ∪ Z`.
  refine (hcU.union hcZ).mono ?_
  intro z hz
  by_cases h1 : z ∈ L.lattice
  · exact Or.inl (Or.inl h1)
  by_cases h2 : s - z ∈ L.lattice
  · exact Or.inl (Or.inr h2)
  refine Or.inr ⟨fun hor ↦ hor.elim h1 h2, ?_⟩
  by_contra hne
  exact hz ⟨h1, h2, hne⟩

/-- Open with countable complement ⇒ preconnected, via
`Set.Countable.isPathConnected_compl_of_one_lt_rank` (`rank ℝ ℂ = 2 > 1`). -/
theorem isPreconnected_eulerDomain {s : ℂ} (hs : s ∉ L.lattice) :
    IsPreconnected (L.eulerDomain s) := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
    exact_mod_cast one_lt_two
  have h := (L.countable_compl_eulerDomain hs).isPathConnected_compl_of_one_lt_rank hrank
  rw [compl_compl] at h
  exact h.isConnected.isPreconnected

/-- `0` is an accumulation point of `eulerDomain s`: the domain is dense, because its complement
is countable (`Set.Countable.dense_compl`).  Needed so the limit `z → 0` sees the domain. -/
theorem mem_closure_eulerDomain {s : ℂ} (hs : s ∉ L.lattice) :
    (0 : ℂ) ∈ closure (L.eulerDomain s) := by
  have hd : Dense (L.eulerDomain s) := by
    have h := (L.countable_compl_eulerDomain hs).dense_compl ℂ
    rwa [compl_compl] at h
  exact hd 0

/-! ## §D `eulerG` is constant, and the constant is `℘ s` -/

/-- `Λᶜ` is preconnected: the complement of a countable set in `ℂ` is path-connected. -/
theorem isPreconnected_compl_lattice : IsPreconnected (L.lattice : Set ℂ)ᶜ := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
    exact_mod_cast one_lt_two
  exact (L.countable_lattice.isPathConnected_compl_of_one_lt_rank
    hrank).isConnected.isPreconnected

/-- **`℘'' = 6℘² - g₂/2`**, in `HasDerivAt` form; this feeds `hasDerivAt_eulerG` and the
tangent-slope limit `tendsto_chordSlope_self`.  Proof: differentiate the Weierstrass
ODE `℘'² = 4℘³ - g₂℘ - g₃` (which holds on the open set `Λᶜ`), giving
`2℘'·℘'' = (12℘² - g₂)·℘'` pointwise.  Where `℘' ≠ 0` divide; the degenerate case `℘' ≡ 0`
near a point would propagate along the connected `Λᶜ` by the identity theorem and force `℘` to
be constant there, contradicting the pole at `0`.  The two cases glue by continuity of
`deriv ℘'` along the (nontrivial) punctured filter. -/
theorem hasDerivAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt ℘'[L] (6 * ℘[L] z ^ 2 - L.g₂ / 2) z := by
  have hP'z : HasDerivAt ℘'[L] (deriv ℘'[L] z) z :=
    (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt
  suffices h : deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 by rwa [h] at hP'z
  -- The differentiated ODE, pointwise on `Λᶜ`.
  have hode : ∀ w : ℂ, w ∉ L.lattice →
      2 * ℘'[L] w * deriv ℘'[L] w = (12 * ℘[L] w ^ 2 - L.g₂) * ℘'[L] w := by
    intro w hw
    have hPw : HasDerivAt ℘[L] (℘'[L] w) w := by
      have h := (L.analyticOnNhd_weierstrassP w hw).differentiableAt.hasDerivAt
      rwa [L.deriv_weierstrassP] at h
    have hP'w : HasDerivAt ℘'[L] (deriv ℘'[L] w) w :=
      (L.analyticOnNhd_derivWeierstrassP w hw).differentiableAt.hasDerivAt
    have hL : HasDerivAt (fun u ↦ ℘'[L] u ^ 2) (2 * ℘'[L] w * deriv ℘'[L] w) w :=
      (hP'w.pow 2).congr_deriv (by push_cast; ring)
    have hR : HasDerivAt (fun u ↦ 4 * ℘[L] u ^ 3 - L.g₂ * ℘[L] u - L.g₃)
        ((12 * ℘[L] w ^ 2 - L.g₂) * ℘'[L] w) w :=
      ((((hPw.pow 3).const_mul (4 : ℂ)).sub (hPw.const_mul L.g₂)).sub_const L.g₃).congr_deriv
        (by push_cast; ring)
    have hev : (fun u ↦ ℘'[L] u ^ 2)
        =ᶠ[𝓝 w] fun u ↦ 4 * ℘[L] u ^ 3 - L.g₂ * ℘[L] u - L.g₃ := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hw] with u hu
      exact L.derivWeierstrassP_sq u hu
    exact (hL.congr_of_eventuallyEq hev.symm).unique hR
  rcases (L.analyticOnNhd_derivWeierstrassP z hz).eventually_eq_zero_or_eventually_ne_zero
    with hcase | hcase
  · -- `℘' ≡ 0` near `z` is impossible: it would make `℘` constant on `Λᶜ`.
    exfalso
    have hzero : Set.EqOn ℘'[L] 0 (L.lattice : Set ℂ)ᶜ := by
      refine L.analyticOnNhd_derivWeierstrassP.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        L.isPreconnected_compl_lattice hz ?_
      filter_upwards [hcase] with u hu
      simpa using hu
    have hconst : Set.EqOn ℘[L] (fun _ ↦ ℘[L] z) (L.lattice : Set ℂ)ᶜ := by
      refine L.isClosed_lattice.isOpen_compl.eqOn_of_deriv_eq L.isPreconnected_compl_lattice
        L.differentiableOn_weierstrassP (differentiableOn_const _) ?_ hz rfl
      intro u hu
      rw [L.deriv_weierstrassP, deriv_const]
      simpa using hzero hu
    have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℂ), ‖℘[L] z‖ < ‖℘[L] u‖ :=
      (L.tendsto_norm_weierstrassP_atTop (zero_mem _)).eventually_gt_atTop _
    have h2 : ∀ᶠ u in 𝓝[≠] (0 : ℂ), u ∉ L.lattice := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds
        (L.compl_lattice_sdiff_singleton_mem_nhds 0), self_mem_nhdsWithin] with u hu1 hu2
      exact fun huΛ ↦ hu1 ⟨huΛ, hu2⟩
    obtain ⟨u, hu1, hu2⟩ := (h1.and h2).exists
    rw [show ℘[L] u = ℘[L] z from hconst hu2] at hu1
    exact lt_irrefl _ hu1
  · -- `℘' ≠ 0` on a punctured neighbourhood: divide the differentiated ODE there and pass to
    -- the limit.
    have hmem : ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds
        (L.isClosed_lattice.isOpen_compl.mem_nhds hz)] with w hw
      exact hw
    have hev : ∀ᶠ w in 𝓝[≠] z, deriv ℘'[L] w = 6 * ℘[L] w ^ 2 - L.g₂ / 2 := by
      filter_upwards [hcase, hmem] with w hw hwΛ
      have h2 : 2 * ℘'[L] w * deriv ℘'[L] w
          = 2 * ℘'[L] w * (6 * ℘[L] w ^ 2 - L.g₂ / 2) := by
        rw [hode w hwΛ]; ring
      exact mul_left_cancel₀ (mul_ne_zero two_ne_zero hw) h2
    have t1 : Tendsto (deriv ℘'[L]) (𝓝[≠] z) (𝓝 (deriv ℘'[L] z)) :=
      ((L.analyticOnNhd_derivWeierstrassP z hz).deriv.continuousAt).mono_left nhdsWithin_le_nhds
    have t2 : Tendsto (deriv ℘'[L]) (𝓝[≠] z) (𝓝 (6 * ℘[L] z ^ 2 - L.g₂ / 2)) := by
      have hc2 : ContinuousAt (fun w ↦ 6 * ℘[L] w ^ 2 - L.g₂ / 2) z :=
        (((L.analyticOnNhd_weierstrassP z hz).continuousAt.pow 2).const_mul 6).sub
          continuousAt_const
      refine Tendsto.congr' ?_ (hc2.mono_left nhdsWithin_le_nhds)
      filter_upwards [hev] with w hw
      exact hw.symm
    exact tendsto_nhds_unique t1 t2

/-- **The Euler derivative computation.**  On its domain, `eulerG s` has vanishing derivative:
assemble `deriv ℘ = ℘'` (`deriv_weierstrassP`), `℘'' = 6℘² - g₂/2`
(`hasDerivAt_derivWeierstrassP`), the chain rule for `z ↦ ℘(s - z)` (sign flip), and the
quotient rule; the resulting rational expression vanishes by `euler_slope_identity` applied to
`derivWeierstrassP_sq` at `z` and `s - z`. -/
theorem hasDerivAt_eulerG {s z : ℂ} (hz : z ∈ L.eulerDomain s) :
    HasDerivAt (L.eulerG s) 0 z := by
  obtain ⟨hz1, hsz, hne⟩ := hz
  have hD0 : ℘[L] z - ℘[L] (s - z) ≠ 0 := sub_ne_zero.mpr hne
  have haff : HasDerivAt (fun u : ℂ ↦ s - u) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub s
  have hP : HasDerivAt ℘[L] (℘'[L] z) z := by
    have h := (L.analyticOnNhd_weierstrassP z hz1).differentiableAt.hasDerivAt
    rwa [L.deriv_weierstrassP] at h
  have hPs : HasDerivAt ℘[L] (℘'[L] (s - z)) (s - z) := by
    have h := (L.analyticOnNhd_weierstrassP (s - z) hsz).differentiableAt.hasDerivAt
    rwa [L.deriv_weierstrassP] at h
  have hP' : HasDerivAt ℘'[L] (6 * ℘[L] z ^ 2 - L.g₂ / 2) z :=
    L.hasDerivAt_derivWeierstrassP hz1
  have hPs' : HasDerivAt ℘'[L] (6 * ℘[L] (s - z) ^ 2 - L.g₂ / 2) (s - z) :=
    L.hasDerivAt_derivWeierstrassP hsz
  -- composites with the reflection `u ↦ s - u`
  have hPc : HasDerivAt (fun u : ℂ ↦ ℘[L] (s - u)) (-℘'[L] (s - z)) z :=
    (hPs.comp z haff).congr_deriv (by ring)
  have hPc' : HasDerivAt (fun u : ℂ ↦ ℘'[L] (s - u))
      (-(6 * ℘[L] (s - z) ^ 2 - L.g₂ / 2)) z :=
    (hPs'.comp z haff).congr_deriv (by ring)
  -- numerator and denominator of the slope, with derivatives shaped for the key identity
  have hN : HasDerivAt (fun u : ℂ ↦ ℘'[L] u - ℘'[L] (s - u))
      (6 * (℘[L] z ^ 2 + ℘[L] (s - z) ^ 2) - L.g₂) z :=
    (hP'.sub hPc').congr_deriv (by ring)
  have hD : HasDerivAt (fun u : ℂ ↦ ℘[L] u - ℘[L] (s - u))
      (℘'[L] z + ℘'[L] (s - z)) z :=
    (hP.sub hPc).congr_deriv (by ring)
  have hkey := euler_slope_identity (L.derivWeierstrassP_sq z hz1)
    (L.derivWeierstrassP_sq (s - z) hsz)
  have hG := ((((hN.div hD hD0).pow 2).div_const 4).sub hP).sub hPc
  refine hG.congr_deriv ?_
  simp only [Pi.div_apply]
  rw [hkey]
  field_simp
  linear_combination (4 * (℘'[L] z - ℘'[L] (s - z))) * mul_inv_cancel₀ hD0

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
  obtain ⟨g, hg, hg0, -, hP, hP'⟩ := L.exists_laurent_weierstrassP
  -- The auxiliary expression: continuous at `0`, and equal to `eulerG s` on the domain.
  -- (Substituting `℘ = z⁻² + g`, `℘' = -2z⁻³ + g'` into `eulerG` and clearing the poles: with
  -- `A = g' - ℘'(s - ·)` and `B = g - ℘(s - ·)`, one has
  -- `slope²/4 - z⁻² = (-4zA + z⁴A² - 8B - 4z²B²) / (4(1 + z²B)²)`.)
  set E : ℂ → ℂ := fun z ↦
    (-4 * z * (deriv g z - ℘'[L] (s - z)) + z ^ 4 * (deriv g z - ℘'[L] (s - z)) ^ 2
        - 8 * (g z - ℘[L] (s - z)) - 4 * z ^ 2 * (g z - ℘[L] (s - z)) ^ 2)
      / (4 * (1 + z ^ 2 * (g z - ℘[L] (s - z))) ^ 2)
      - g z - ℘[L] (s - z) with hE
  have key : Tendsto E (𝓝 (0 : ℂ)) (𝓝 (℘[L] s)) := by
    have hgc : ContinuousAt g 0 := hg.continuousAt
    have hg' : ContinuousAt (deriv g) 0 := hg.deriv.continuousAt
    have hPs : ContinuousAt (fun z : ℂ ↦ ℘[L] (s - z)) 0 := by
      have hb : ContinuousAt ℘[L] (s - 0) :=
        (L.analyticOnNhd_weierstrassP (s - 0) (by simpa using hs)).continuousAt
      exact hb.comp ((continuous_const.sub continuous_id).continuousAt)
    have hPs' : ContinuousAt (fun z : ℂ ↦ ℘'[L] (s - z)) 0 := by
      have hb : ContinuousAt ℘'[L] (s - 0) :=
        (L.analyticOnNhd_derivWeierstrassP (s - 0) (by simpa using hs)).continuousAt
      exact hb.comp ((continuous_const.sub continuous_id).continuousAt)
    have hA : ContinuousAt (fun z : ℂ ↦ deriv g z - ℘'[L] (s - z)) 0 := hg'.sub hPs'
    have hB : ContinuousAt (fun z : ℂ ↦ g z - ℘[L] (s - z)) 0 := hgc.sub hPs
    have hnum : ContinuousAt (fun z : ℂ ↦
        -4 * z * (deriv g z - ℘'[L] (s - z)) + z ^ 4 * (deriv g z - ℘'[L] (s - z)) ^ 2
          - 8 * (g z - ℘[L] (s - z)) - 4 * z ^ 2 * (g z - ℘[L] (s - z)) ^ 2) 0 :=
      ((((continuousAt_const.mul continuousAt_id).mul hA).add
        ((continuousAt_id.pow 4).mul (hA.pow 2))).sub
        (continuousAt_const.mul hB)).sub
        ((continuousAt_const.mul (continuousAt_id.pow 2)).mul (hB.pow 2))
    have hden : ContinuousAt (fun z : ℂ ↦
        4 * (1 + z ^ 2 * (g z - ℘[L] (s - z))) ^ 2) 0 :=
      continuousAt_const.mul ((continuousAt_const.add ((continuousAt_id.pow 2).mul hB)).pow 2)
    have hden0 : (4 : ℂ) * (1 + (0 : ℂ) ^ 2 * (g 0 - ℘[L] (s - 0))) ^ 2 ≠ 0 := by norm_num
    have hcont : ContinuousAt E 0 := ((hnum.div hden hden0).sub hgc).sub hPs
    have hval : E 0 = ℘[L] s := by
      simp only [hE]
      norm_num [hg0]
      ring
    rw [← hval]
    exact hcont
  -- On the domain, `eulerG` agrees with `E`: substitute the Laurent forms and clear
  -- denominators (all nonzero there).
  refine Tendsto.congr' ?_ (key.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with w hw
  obtain ⟨hw1, hws, hwne⟩ := hw
  have hw0 : w ≠ 0 := fun h ↦ hw1 (by rw [h]; exact zero_mem _)
  have hw2 : (w : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ hw0
  have hDl : (w ^ 2)⁻¹ + g w - ℘[L] (s - w) ≠ 0 := by
    have hD : ℘[L] w - ℘[L] (s - w) ≠ 0 := sub_ne_zero.mpr hwne
    rwa [hP w] at hD
  have h1B : (1 : ℂ) + w ^ 2 * (g w - ℘[L] (s - w)) ≠ 0 := by
    have heq : w ^ 2 * ((w ^ 2)⁻¹ + g w - ℘[L] (s - w))
        = (1 : ℂ) + w ^ 2 * (g w - ℘[L] (s - w)) := by
      rw [mul_sub, mul_add, mul_inv_cancel₀ hw2]
      ring
    rw [← heq]
    exact mul_ne_zero hw2 hDl
  simp only [hE, eulerG, eulerSlope]
  rw [hP w, hP' w hw1, sub_add_eq_sub_sub]
  congr 1
  congr 1
  -- ⊢ num / (4 * (1 + w²B)²) = slope² / 4 - (w²)⁻¹, with all denominators explicit
  have hwC : w * (1 + w ^ 2 * (g w - ℘[L] (s - w))) ≠ 0 := mul_ne_zero hw0 h1B
  have hslope : (-2 * (w ^ 3)⁻¹ + deriv g w - ℘'[L] (s - w))
      / ((w ^ 2)⁻¹ + g w - ℘[L] (s - w))
      = (-2 + w ^ 3 * (deriv g w - ℘'[L] (s - w)))
        / (w * (1 + w ^ 2 * (g w - ℘[L] (s - w)))) := by
    rw [div_eq_div_iff hDl hwC]
    field_simp
    ring
  have h4C : (4 : ℂ) * (1 + w ^ 2 * (g w - ℘[L] (s - w))) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 h1B)
  have hbig : w ^ 2 * (1 + w ^ 2 * (g w - ℘[L] (s - w))) ^ 2 * 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hw2 (pow_ne_zero 2 h1B)) (by norm_num)
  rw [hslope, div_pow, mul_pow, div_div, inv_eq_one_div,
    div_sub_div _ _ hbig hw2, div_eq_div_iff h4C (mul_ne_zero hbig hw2)]
  ring

/-- **The addition theorem, Euler form.**  Combining: `eulerG s` is differentiable with zero
derivative on the open preconnected `eulerDomain s`, hence constant
(`IsOpen.eqOn_of_deriv_eq` against the constant function); the constant is `℘ s` by
`tendsto_eulerG_zero` and `mem_closure_eulerDomain` (uniqueness of limits along the nontrivial
filter `𝓝[eulerDomain s] 0`). -/
theorem eulerG_eq_weierstrassP {s : ℂ} (hs : s ∉ L.lattice) {z : ℂ}
    (hz : z ∈ L.eulerDomain s) :
    L.eulerG s z = ℘[L] s := by
  have hconst : Set.EqOn (L.eulerG s) (fun _ ↦ L.eulerG s z) (L.eulerDomain s) := by
    refine (L.isOpen_eulerDomain s).eqOn_of_deriv_eq (L.isPreconnected_eulerDomain hs)
      (fun x hx ↦ (L.hasDerivAt_eulerG hx).differentiableAt.differentiableWithinAt)
      (differentiableOn_const _) (fun x hx ↦ ?_) hz rfl
    rw [(L.hasDerivAt_eulerG hx).deriv, deriv_const]
  haveI hne : (𝓝[L.eulerDomain s] (0 : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (L.mem_closure_eulerDomain hs)
  have h1 : Tendsto (L.eulerG s) (𝓝[L.eulerDomain s] (0 : ℂ)) (𝓝 (L.eulerG s z)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (hconst hw).symm
  exact tendsto_nhds_unique h1 (L.tendsto_eulerG_zero hs)

/-- **The addition theorem for `℘` (X-coordinate), sorry-free.**  This is exactly the statement
of `weierstrassP_add`, the first `sorry` of `addition.lean`: pure algebra from
`eulerG_eq_weierstrassP` at `s = z + w`.  (`#print axioms` confirms it uses only
`propext, Classical.choice, Quot.sound` — no `sorryAx`.) -/
theorem weierstrassP_add_of_euler {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
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

/-- Slope of the chord through `(℘ z, ℘' z)` and `(℘ w, ℘' w)`.  (This is `2 ·` Mathlib's
`WeierstrassCurve.Affine.slope`, because the curve coordinate is `y = ℘'/2`.) -/
def chordSlope (z w : ℂ) : ℂ := (℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w)

/-- Derivative of the fixed-`w` chord slope, by the quotient rule. -/
theorem hasDerivAt_chordSlope {z w : ℂ} (hz : z ∉ L.lattice) (hx : ℘[L] z ≠ ℘[L] w) :
    HasDerivAt (fun u ↦ L.chordSlope u w)
      (((6 * ℘[L] z ^ 2 - L.g₂ / 2) * (℘[L] z - ℘[L] w)
          - (℘'[L] z - ℘'[L] w) * ℘'[L] z) / (℘[L] z - ℘[L] w) ^ 2) z := by
  simp only [chordSlope]
  have hP : HasDerivAt ℘[L] (℘'[L] z) z := by
    have h := (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
    rwa [L.deriv_weierstrassP] at h
  have hN : HasDerivAt (fun u : ℂ ↦ ℘'[L] u - ℘'[L] w) (6 * ℘[L] z ^ 2 - L.g₂ / 2) z :=
    (L.hasDerivAt_derivWeierstrassP hz).sub_const _
  have hD : HasDerivAt (fun u : ℂ ↦ ℘[L] u - ℘[L] w) (℘'[L] z) z := hP.sub_const _
  exact hN.div hD (sub_ne_zero.mpr hx)

/-- **Y-formula from X-formula.**  Once the X-formula holds on the (open) chord locus, both
sides are differentiable in `z` there; differentiating (`hasDerivAt_chordSlope`,
`deriv_weierstrassP`) and simplifying with `euler_tangency_identity` gives exactly
`derivWeierstrassP_add` — the second `sorry` of `addition.lean`.  Stated conditionally to make
the dependency explicit; see `derivWeierstrassP_add_of_euler` for the discharged version. -/
theorem derivWeierstrassP_add_of_weierstrassP_add
    (hX : ∀ z w : ℂ, z ∉ L.lattice → w ∉ L.lattice → z + w ∉ L.lattice →
      ℘[L] z ≠ ℘[L] w →
      ℘[L] (z + w) = L.chordSlope z w ^ 2 / 4 - ℘[L] z - ℘[L] w)
    {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) (hzw : z + w ∉ L.lattice)
    (hx : ℘[L] z ≠ ℘[L] w) :
    ℘'[L] (z + w) = -(L.chordSlope z w * (℘[L] (z + w) - ℘[L] z) + ℘'[L] z) := by
  have hD0 : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr hx
  have hP : HasDerivAt ℘[L] (℘'[L] z) z := by
    have h := (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
    rwa [L.deriv_weierstrassP] at h
  -- derivative of the left side `u ↦ ℘(u + w)` at `z`
  have hL : HasDerivAt (fun u : ℂ ↦ ℘[L] (u + w)) (℘'[L] (z + w)) z := by
    have hPzw : HasDerivAt ℘[L] (℘'[L] (z + w)) (z + w) := by
      have h := (L.analyticOnNhd_weierstrassP (z + w) hzw).differentiableAt.hasDerivAt
      rwa [L.deriv_weierstrassP] at h
    have haff : HasDerivAt (fun u : ℂ ↦ u + w) 1 z := (hasDerivAt_id z).add_const w
    exact (hPzw.comp z haff).congr_deriv (mul_one _)
  -- derivative of the right side at `z`
  have hR := (((L.hasDerivAt_chordSlope hz hx).pow 2).div_const 4).sub hP |>.sub_const (℘[L] w)
  -- the two sides agree near `z` (the chord locus is open), so the derivatives agree
  have hev : (fun u : ℂ ↦ ℘[L] (u + w)) =ᶠ[𝓝 z]
      fun u : ℂ ↦ L.chordSlope u w ^ 2 / 4 - ℘[L] u - ℘[L] w := by
    have h1 : ∀ᶠ u in 𝓝 z, u ∉ L.lattice := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with u hu
      exact hu
    have h2 : ∀ᶠ u in 𝓝 z, u + w ∉ L.lattice := by
      have hc : ContinuousAt (fun u : ℂ ↦ u + w) z :=
        (continuous_id.add continuous_const).continuousAt
      filter_upwards [hc.eventually_mem (L.isClosed_lattice.isOpen_compl.mem_nhds hzw)] with u hu
      exact hu
    have h3 : ∀ᶠ u in 𝓝 z, ℘[L] u ≠ ℘[L] w :=
      ((L.analyticOnNhd_weierstrassP z hz).continuousAt).eventually_ne hx
    filter_upwards [h1, h2, h3] with u hu1 hu2 hu3
    exact hX u w hu1 hw hu2 hu3
  have huniq := (hL.congr_of_eventuallyEq hev.symm).unique hR
  -- now pure algebra, using the tangency identity
  rw [huniq, hX z w hz hw hzw hx]
  have hkey := euler_tangency_identity (L.derivWeierstrassP_sq z hz)
    (L.derivWeierstrassP_sq w hw)
  simp only [chordSlope]
  push_cast
  field_simp
  linear_combination (℘'[L] z - ℘'[L] w) * hkey

/-- **The addition theorem for `℘'` (Y-coordinate), sorry-free** — exactly the statement of
`derivWeierstrassP_add`, the second `sorry` of `addition.lean`: the conditional theorem above,
with the X-formula hypothesis discharged by `weierstrassP_add_of_euler`. -/
theorem derivWeierstrassP_add_of_euler {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z + w ∉ L.lattice) (hx : ℘[L] z ≠ ℘[L] w) :
    ℘'[L] (z + w)
      = -((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w) * (℘[L] (z + w) - ℘[L] z) + ℘'[L] z) := by
  have h := L.derivWeierstrassP_add_of_weierstrassP_add ?_ hz hw hzw hx
  · rwa [chordSlope] at h
  · intro z w hz hw hzw hx
    rw [L.weierstrassP_add_of_euler hz hw hzw hx, chordSlope]
    have hne : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr hx
    field_simp
    ring

/-! ## §F Fibers of `℘` from the addition formula (replaces the valence-formula uses of §5)

These two lemmas recover the classical fiber facts *without* any counting argument. -/

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
  -- the common domain of the two translates
  set V : Set ℂ := {u : ℂ | a + u ∈ L.lattice ∨ b + u ∈ L.lattice}ᶜ with hV
  have hVc : Set.Countable Vᶜ := by
    rw [hV, compl_compl]
    refine ((L.countable_lattice.preimage (add_right_injective a)).union
      (L.countable_lattice.preimage (add_right_injective b))).mono ?_
    rintro u (hu | hu)
    exacts [Or.inl hu, Or.inr hu]
  have hVpre : IsPreconnected V := by
    have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
      rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
      exact_mod_cast one_lt_two
    have h := (hVc.isPathConnected_compl_of_one_lt_rank hrank).isConnected.isPreconnected
    rwa [compl_compl] at h
  -- both translates of `℘` are analytic on `V`
  have hF₁ : AnalyticOnNhd ℂ (fun u : ℂ ↦ ℘[L] (a + u)) V := by
    intro u hu
    exact (L.analyticOnNhd_weierstrassP (a + u) fun h ↦ hu (Or.inl h)).comp
      (analyticAt_const.add analyticAt_id)
  have hF₂ : AnalyticOnNhd ℂ (fun u : ℂ ↦ ℘[L] (b + u)) V := by
    intro u hu
    exact (L.analyticOnNhd_weierstrassP (b + u) fun h ↦ hu (Or.inr h)).comp
      (analyticAt_const.add analyticAt_id)
  -- a point `z₀` (near `0`, where `℘` blows up) at which the chord formulas apply to both pairs
  obtain ⟨z₀, hz4, hz1, hz2, hz3⟩ : ∃ z₀ : ℂ, ℘[L] a ≠ ℘[L] z₀ ∧ z₀ ∉ L.lattice ∧
      a + z₀ ∉ L.lattice ∧ b + z₀ ∉ L.lattice := by
    have h4 : ∀ᶠ u in 𝓝[≠] (0 : ℂ), ℘[L] a ≠ ℘[L] u := by
      filter_upwards [(L.tendsto_norm_weierstrassP_atTop
        (zero_mem _)).eventually_gt_atTop ‖℘[L] a‖] with u hu heq
      rw [heq] at hu
      exact lt_irrefl _ hu
    have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℂ), u ∉ L.lattice := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds
        (L.compl_lattice_sdiff_singleton_mem_nhds 0), self_mem_nhdsWithin] with u hu1 hu2
      exact fun huΛ ↦ hu1 ⟨huΛ, hu2⟩
    have h2 : ∀ᶠ u in 𝓝 (0 : ℂ), a + u ∉ L.lattice := by
      have hc : ContinuousAt (fun u : ℂ ↦ a + u) 0 :=
        (continuous_const.add continuous_id).continuousAt
      have hmem : (↑L.lattice : Set ℂ)ᶜ ∈ 𝓝 (a + 0) :=
        L.isClosed_lattice.isOpen_compl.mem_nhds (by simpa using ha)
      filter_upwards [hc.eventually_mem hmem] with u hu
      exact hu
    have h3 : ∀ᶠ u in 𝓝 (0 : ℂ), b + u ∉ L.lattice := by
      have hc : ContinuousAt (fun u : ℂ ↦ b + u) 0 :=
        (continuous_const.add continuous_id).continuousAt
      have hmem : (↑L.lattice : Set ℂ)ᶜ ∈ 𝓝 (b + 0) :=
        L.isClosed_lattice.isOpen_compl.mem_nhds (by simpa using hb)
      filter_upwards [hc.eventually_mem hmem] with u hu
      exact hu
    exact (h4.and (h1.and ((h2.filter_mono nhdsWithin_le_nhds).and
      (h3.filter_mono nhdsWithin_le_nhds)))).exists
  -- near `z₀`, both `℘(a + u)` and `℘(b + u)` are computed by the chord formula from the same
  -- data, so the two functions agree on a neighbourhood
  have hev : (fun u : ℂ ↦ ℘[L] (a + u)) =ᶠ[𝓝 z₀] fun u : ℂ ↦ ℘[L] (b + u) := by
    have e1 : ∀ᶠ u in 𝓝 z₀, u ∉ L.lattice := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz1] with u hu
      exact hu
    have e2 : ∀ᶠ u in 𝓝 z₀, a + u ∉ L.lattice := by
      have hc : ContinuousAt (fun u : ℂ ↦ a + u) z₀ :=
        (continuous_const.add continuous_id).continuousAt
      filter_upwards [hc.eventually_mem (L.isClosed_lattice.isOpen_compl.mem_nhds hz2)] with u hu
      exact hu
    have e3 : ∀ᶠ u in 𝓝 z₀, b + u ∉ L.lattice := by
      have hc : ContinuousAt (fun u : ℂ ↦ b + u) z₀ :=
        (continuous_const.add continuous_id).continuousAt
      filter_upwards [hc.eventually_mem (L.isClosed_lattice.isOpen_compl.mem_nhds hz3)] with u hu
      exact hu
    have e4 : ∀ᶠ u in 𝓝 z₀, ℘[L] a ≠ ℘[L] u := by
      have hc : ContinuousAt ℘[L] z₀ := (L.analyticOnNhd_weierstrassP z₀ hz1).continuousAt
      filter_upwards [hc.eventually_ne (Ne.symm hz4)] with u hu
      exact fun heq ↦ hu heq.symm
    filter_upwards [e1, e2, e3, e4] with u hu1 hu2 hu3 hu4
    rw [L.weierstrassP_add_of_euler ha hu1 hu2 hu4,
      L.weierstrassP_add_of_euler hb hu1 hu3 fun h ↦ hu4 (hP.trans h), hP, hP']
  -- identity theorem on the connected `V`
  have heq : Set.EqOn (fun u : ℂ ↦ ℘[L] (a + u)) (fun u : ℂ ↦ ℘[L] (b + u)) V :=
    hF₁.eqOn_of_preconnected_of_eventuallyEq hF₂ hVpre
      (fun hor ↦ hor.elim hz2 hz3) hev
  intro u hu1 hu2
  exact heq fun hor ↦ hor.elim hu1 hu2

/-- **Injectivity of `(℘, ℘')` on `(ℂ ∖ Λ)/Λ`.**  Let `u → -b` in
`weierstrassP_add_right_eq`: if `a - b ∉ Λ` then `℘(a + u) → ℘(a - b)` stays bounded while
`℘(b + u) = ℘(u + b) → ∞` (`tendsto_norm_weierstrassP_atTop` at `0`); contradiction.  (The
approach `u = -b + ε` stays in the allowed set for all small `ε ≠ 0` because `Λ` is closed and
`a - b ∉ Λ`.) -/
theorem sub_mem_lattice_of_weierstrassP_eq {a b : ℂ} (ha : a ∉ L.lattice) (hb : b ∉ L.lattice)
    (hP : ℘[L] a = ℘[L] b) (hP' : ℘'[L] a = ℘'[L] b) :
    a - b ∈ L.lattice := by
  by_contra hab
  have hab' : a + -b ∉ L.lattice := by simpa [sub_eq_add_neg] using hab
  have heq := L.weierstrassP_add_right_eq ha hb hP hP'
  -- as `u → -b`, `℘(b + u)` blows up ...
  have hblow : Tendsto (fun u : ℂ ↦ ‖℘[L] (b + u)‖) (𝓝[≠] (-b : ℂ)) atTop := by
    have hmap : Tendsto (fun u : ℂ ↦ b + u) (𝓝[≠] (-b : ℂ)) (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h2 : Tendsto (fun u : ℂ ↦ b + u) (𝓝 (-b)) (𝓝 (b + -b)) :=
          (continuous_const.add continuous_id).tendsto (-b)
        simpa using h2.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu ⊢
        exact fun h0 ↦ hu (eq_neg_of_add_eq_zero_right h0)
    exact (L.tendsto_norm_weierstrassP_atTop (zero_mem _)).comp hmap
  -- ... while `℘(a + u)` stays bounded near `℘(a - b)`
  have hbound : Tendsto (fun u : ℂ ↦ ‖℘[L] (a + u)‖) (𝓝 (-b : ℂ)) (𝓝 ‖℘[L] (a + -b)‖) := by
    have hc : ContinuousAt ℘[L] (a + -b) :=
      (L.analyticOnNhd_weierstrassP (a + -b) hab').continuousAt
    exact (hc.comp ((continuous_const.add continuous_id).continuousAt)).norm
  -- the approach stays in the set where `℘(a + u) = ℘(b + u)`
  have h1 : ∀ᶠ u in 𝓝 (-b : ℂ), a + u ∉ L.lattice := by
    have hc : ContinuousAt (fun u : ℂ ↦ a + u) (-b) :=
      (continuous_const.add continuous_id).continuousAt
    filter_upwards [hc.eventually_mem (L.isClosed_lattice.isOpen_compl.mem_nhds hab')] with u hu
    exact hu
  have h2 : ∀ᶠ u in 𝓝[≠] (-b : ℂ), b + u ∉ L.lattice := by
    have hc : ContinuousAt (fun u : ℂ ↦ b + u) (-b) :=
      (continuous_const.add continuous_id).continuousAt
    have hmem : ((↑L.lattice : Set ℂ) \ {0})ᶜ ∈ 𝓝 (b + -b) := by
      simpa using L.compl_lattice_sdiff_singleton_mem_nhds 0
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hc.eventually_mem hmem),
      self_mem_nhdsWithin] with u hu1 hu2
    intro hmem'
    have h0 : b + u = 0 := by
      by_contra h0
      exact hu1 ⟨hmem', h0⟩
    exact hu2 (eq_neg_of_add_eq_zero_right h0)
  -- combine everything at one point
  have h3 : ∀ᶠ u in 𝓝[≠] (-b : ℂ), ‖℘[L] (a + -b)‖ + 1 < ‖℘[L] (b + u)‖ :=
    hblow.eventually_gt_atTop _
  have h4 : ∀ᶠ u in 𝓝 (-b : ℂ), ‖℘[L] (a + u)‖ ≤ ‖℘[L] (a + -b)‖ + 1 :=
    hbound.eventually (eventually_le_nhds (lt_add_one _))
  obtain ⟨u, hu3, hu4, hu1, hu2⟩ := (h3.and ((h4.filter_mono nhdsWithin_le_nhds).and
    ((h1.filter_mono nhdsWithin_le_nhds).and h2))).exists
  rw [heq u hu1 hu2] at hu4
  exact absurd hu3 (not_lt.mpr hu4)

/-- **The fiber lemma (forward direction), with no valence formula**: if `℘ z = ℘ w` off the
lattice then `z ≡ ±w (mod Λ)`.  The differential equation forces `℘'(z) = ±℘'(w)`, and each
sign reduces to `sub_mem_lattice_of_weierstrassP_eq` (for `-`, against `-w`, using evenness of
`℘` and oddness of `℘'`). -/
theorem sub_mem_or_add_mem_of_weierstrassP_eq {z w : ℂ} (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) (h : ℘[L] z = ℘[L] w) :
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
  intro h
  apply weierstrassDiscriminant_ne_zero L
  have hg₂ : L.g₂ = 12 * e ^ 2 := by linear_combination -h
  have hg₃ : L.g₃ = -8 * e ^ 3 := by linear_combination -he + e * h
  rw [weierstrassDiscriminant, hg₂, hg₃]
  ring

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
  -- `℘ z₀` is a (simple, by `cubic_deriv_ne_zero_of_root`) root of the cubic
  have he : 4 * ℘[L] z₀ ^ 3 - L.g₂ * ℘[L] z₀ - L.g₃ = 0 := by
    have h := L.derivWeierstrassP_sq z₀ hz
    rw [h0] at h
    linear_combination -h
  have hq0 : 12 * ℘[L] z₀ ^ 2 - L.g₂ ≠ 0 := L.cubic_deriv_ne_zero_of_root he
  have hc2 : 0 < ‖12 * ℘[L] z₀ ^ 2 - L.g₂‖ := norm_pos_iff.mpr hq0
  -- the exact formula for the squared slope on the set: `q(℘ w) / (℘ w - ℘ z₀)`
  have hkey : ∀ w : ℂ, w ∉ L.lattice → ℘[L] w ≠ ℘[L] z₀ → L.chordSlope z₀ w ^ 2
      = (4 * ℘[L] w ^ 2 + 4 * ℘[L] z₀ * ℘[L] w + (4 * ℘[L] z₀ ^ 2 - L.g₂))
        / (℘[L] w - ℘[L] z₀) := by
    intro w hw1 hw2
    have hD : ℘[L] z₀ - ℘[L] w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw2)
    have hD' : ℘[L] w - ℘[L] z₀ ≠ 0 := sub_ne_zero.mpr hw2
    have hsq := L.derivWeierstrassP_sq w hw1
    rw [chordSlope, h0, div_pow, div_eq_div_iff (pow_ne_zero 2 hD) hD']
    linear_combination (℘[L] w - ℘[L] z₀) * hsq + (℘[L] w - ℘[L] z₀) * he
  -- the numerator tends (in norm) to `‖12℘z₀² - g₂‖ > 0` ...
  have hnum : Tendsto (fun w : ℂ ↦ ‖4 * ℘[L] w ^ 2 + 4 * ℘[L] z₀ * ℘[L] w
      + (4 * ℘[L] z₀ ^ 2 - L.g₂)‖) (𝓝 z₀) (𝓝 ‖12 * ℘[L] z₀ ^ 2 - L.g₂‖) := by
    have h℘ : ContinuousAt ℘[L] z₀ := (L.analyticOnNhd_weierstrassP z₀ hz).continuousAt
    have hc : ContinuousAt (fun w : ℂ ↦ 4 * ℘[L] w ^ 2 + 4 * ℘[L] z₀ * ℘[L] w
        + (4 * ℘[L] z₀ ^ 2 - L.g₂)) z₀ :=
      (((h℘.pow 2).const_mul 4).add (h℘.const_mul _)).add continuousAt_const
    have hval : (fun w : ℂ ↦ 4 * ℘[L] w ^ 2 + 4 * ℘[L] z₀ * ℘[L] w
        + (4 * ℘[L] z₀ ^ 2 - L.g₂)) z₀ = 12 * ℘[L] z₀ ^ 2 - L.g₂ := by
      show 4 * ℘[L] z₀ ^ 2 + 4 * ℘[L] z₀ * ℘[L] z₀ + (4 * ℘[L] z₀ ^ 2 - L.g₂)
          = 12 * ℘[L] z₀ ^ 2 - L.g₂
      ring
    rw [← hval]
    exact hc.norm
  -- ... while the denominator tends to `0` through positive values
  have hden : Tendsto (fun w : ℂ ↦ ‖℘[L] w - ℘[L] z₀‖)
      (𝓝[{w | w ∉ L.lattice ∧ ℘[L] w ≠ ℘[L] z₀}] z₀) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h℘ : ContinuousAt ℘[L] z₀ := (L.analyticOnNhd_weierstrassP z₀ hz).continuousAt
      have hc : ContinuousAt (fun w : ℂ ↦ ‖℘[L] w - ℘[L] z₀‖) z₀ :=
        (h℘.sub continuousAt_const).norm
      simpa using hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact Set.mem_Ioi.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr hw.2))
  have hinv : Tendsto (fun w : ℂ ↦ ‖℘[L] w - ℘[L] z₀‖⁻¹)
      (𝓝[{w | w ∉ L.lattice ∧ ℘[L] w ≠ ℘[L] z₀}] z₀) atTop :=
    tendsto_inv_nhdsGT_zero.comp hden
  -- assemble the lower bound
  have hev : ∀ᶠ w in 𝓝[{w | w ∉ L.lattice ∧ ℘[L] w ≠ ℘[L] z₀}] z₀,
      ‖12 * ℘[L] z₀ ^ 2 - L.g₂‖ / 2 ≤ ‖4 * ℘[L] w ^ 2 + 4 * ℘[L] z₀ * ℘[L] w
        + (4 * ℘[L] z₀ ^ 2 - L.g₂)‖ :=
    (hnum.eventually (eventually_ge_nhds (by linarith))).filter_mono nhdsWithin_le_nhds
  refine tendsto_atTop_mono' _ ?_ (hinv.const_mul_atTop (half_pos hc2))
  filter_upwards [hev, self_mem_nhdsWithin] with w hw1 hw2
  rw [hkey w hw2.1 hw2.2, norm_div, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hw1 (inv_nonneg.mpr (norm_nonneg _))

/-- **`℘'` vanishes only at 2-torsion — no valence formula.**  Suppose `℘'(z) = 0` but
`2z ∉ Λ`.  Feed `w → z` into the X-formula (the punctured approach stays in the chord locus:
`℘(w) ≠ ℘(z)` eventually since `℘ - ℘(z)` has isolated zeros, and `w, z + w ∉ Λ` are open
conditions): the left side `℘(z + w) → ℘(2z)` is finite, but the right side
`chordSlope²/4 - ℘z - ℘w → ∞` by `tendsto_norm_chordSlope_sq_atTop`.  Contradiction.
This is the forward direction of `℘'(z) = 0 ↔ 2z ∈ Λ`. -/
theorem two_mul_mem_lattice_of_derivWeierstrassP_eq_zero {z : ℂ} (hz : z ∉ L.lattice)
    (h0 : ℘'[L] z = 0) :
    2 * z ∈ L.lattice := by
  by_contra h2z
  have h2z' : z + z ∉ L.lattice := fun h ↦ h2z (by rwa [two_mul])
  -- `℘` is not locally equal to `℘ z` near `z` (else it is constant on `Λᶜ` — impossible)
  have hne : ∀ᶠ w in 𝓝[≠] z, ℘[L] w ≠ ℘[L] z := by
    rcases ((L.analyticOnNhd_weierstrassP z hz).sub
      analyticAt_const).eventually_eq_zero_or_eventually_ne_zero with hcase | hcase
    · exfalso
      have hzero : Set.EqOn (fun w ↦ ℘[L] w - ℘[L] z) 0 (L.lattice : Set ℂ)ᶜ := by
        refine AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (fun u hu ↦ (L.analyticOnNhd_weierstrassP u hu).sub analyticAt_const)
          L.isPreconnected_compl_lattice hz ?_
        filter_upwards [hcase] with u hu
        simpa using hu
      have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℂ), ‖℘[L] z‖ < ‖℘[L] u‖ :=
        (L.tendsto_norm_weierstrassP_atTop (zero_mem _)).eventually_gt_atTop _
      have h2 : ∀ᶠ u in 𝓝[≠] (0 : ℂ), u ∉ L.lattice := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds
          (L.compl_lattice_sdiff_singleton_mem_nhds 0), self_mem_nhdsWithin] with u hu1 hu2
        exact fun huΛ ↦ hu1 ⟨huΛ, hu2⟩
      obtain ⟨u, hu1, hu2⟩ := (h1.and h2).exists
      have heq : ℘[L] u = ℘[L] z := by simpa [sub_eq_zero] using hzero hu2
      rw [heq] at hu1
      exact lt_irrefl _ hu1
    · filter_upwards [hcase] with w hw
      simpa [sub_eq_zero] using hw
  have hΛ : ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      (L.isClosed_lattice.isOpen_compl.mem_nhds hz)] with w hw
    exact hw
  -- transfer the slope blow-up to `𝓝[≠] z`
  have hSmem : {w : ℂ | w ∉ L.lattice ∧ ℘[L] w ≠ ℘[L] z} ∈ 𝓝[≠] z := hΛ.and hne
  have hblow : Tendsto (fun w ↦ ‖L.chordSlope z w ^ 2‖) (𝓝[≠] z) atTop :=
    (L.tendsto_norm_chordSlope_sq_atTop hz h0).mono_left (nhdsWithin_le_iff.mpr hSmem)
  -- boundedness of the other terms of the X-formula near `z`
  have hb1 : ∀ᶠ w in 𝓝 z, ‖℘[L] (z + w)‖ ≤ ‖℘[L] (z + z)‖ + 1 := by
    have hc : Tendsto (fun w : ℂ ↦ ‖℘[L] (z + w)‖) (𝓝 z) (𝓝 ‖℘[L] (z + z)‖) := by
      have h℘ : ContinuousAt ℘[L] (z + z) :=
        (L.analyticOnNhd_weierstrassP (z + z) h2z').continuousAt
      exact (h℘.comp ((continuous_const.add continuous_id).continuousAt)).norm
    exact hc.eventually (eventually_le_nhds (lt_add_one _))
  have hb2 : ∀ᶠ w in 𝓝 z, ‖℘[L] w‖ ≤ ‖℘[L] z‖ + 1 := by
    have hc : Tendsto (fun w : ℂ ↦ ‖℘[L] w‖) (𝓝 z) (𝓝 ‖℘[L] z‖) :=
      ((L.analyticOnNhd_weierstrassP z hz).continuousAt).norm
    exact hc.eventually (eventually_le_nhds (lt_add_one _))
  have hzw : ∀ᶠ w in 𝓝 z, z + w ∉ L.lattice := by
    have hc : ContinuousAt (fun w : ℂ ↦ z + w) z :=
      (continuous_const.add continuous_id).continuousAt
    filter_upwards [hc.eventually_mem (L.isClosed_lattice.isOpen_compl.mem_nhds h2z')] with w hw
    exact hw
  have hbig : ∀ᶠ w in 𝓝[≠] z,
      4 * (‖℘[L] (z + z)‖ + 1 + (‖℘[L] z‖ + 1) + (‖℘[L] z‖ + 1)) < ‖L.chordSlope z w ^ 2‖ :=
    hblow.eventually_gt_atTop _
  obtain ⟨w, hw1, hw2, hw3, hw4, hw5, hw6⟩ := (hbig.and (hΛ.and (hne.and
    ((hzw.filter_mono nhdsWithin_le_nhds).and ((hb1.filter_mono nhdsWithin_le_nhds).and
    (hb2.filter_mono nhdsWithin_le_nhds)))))).exists
  -- the X-formula at `(z, w)` bounds the squared slope — contradiction
  have hX := L.weierstrassP_add_of_euler hz hw2 hw4 fun h ↦ hw3 h.symm
  have hS2 : L.chordSlope z w ^ 2 = 4 * (℘[L] (z + w) + ℘[L] z + ℘[L] w) := by
    have hD : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr fun h ↦ hw3 h.symm
    rw [chordSlope, hX]
    field_simp
    ring
  have hle : ‖℘[L] (z + w) + ℘[L] z + ℘[L] w‖
      ≤ ‖℘[L] (z + z)‖ + 1 + (‖℘[L] z‖ + 1) + (‖℘[L] z‖ + 1) := by
    refine norm_add₃_le.trans ?_
    gcongr
    linarith
  have hnorm : ‖L.chordSlope z w ^ 2‖
      ≤ 4 * (‖℘[L] (z + z)‖ + 1 + (‖℘[L] z‖ + 1) + (‖℘[L] z‖ + 1)) := by
    rw [hS2, norm_mul]
    have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [h4]
    exact mul_le_mul_of_nonneg_left hle (by norm_num)
  exact absurd hw1 (not_lt.mpr hnorm)

/-- **Tangent slope as a limit of chord slopes.**  When `℘'(z) ≠ 0`, the chord slope tends to
`℘''(z)/℘'(z)` as `w → z`: write it as a quotient of difference quotients
`[(℘'(w) - ℘'(z))/(w - z)] / [(℘(w) - ℘(z))/(w - z)]` and use `deriv_derivWeierstrassP`
(numerator) and `deriv_weierstrassP` (denominator, nonzero limit).  The punctured filter is
legitimate: `℘ - ℘(z)` has a *simple* zero at `z` (its derivative is `℘'(z) ≠ 0`), so
`℘(w) ≠ ℘(z)` eventually. -/
theorem tendsto_chordSlope_self {z : ℂ} (hz : z ∉ L.lattice) (h0 : ℘'[L] z ≠ 0) :
    Tendsto (fun w ↦ L.chordSlope z w) (𝓝[≠] z)
      (𝓝 ((6 * ℘[L] z ^ 2 - L.g₂ / 2) / ℘'[L] z)) := by
  have hP : HasDerivAt ℘[L] (℘'[L] z) z := by
    have h := (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
    rwa [L.deriv_weierstrassP] at h
  have hnum : Tendsto (slope ℘'[L] z) (𝓝[≠] z) (𝓝 (6 * ℘[L] z ^ 2 - L.g₂ / 2)) :=
    hasDerivAt_iff_tendsto_slope.mp (L.hasDerivAt_derivWeierstrassP hz)
  have hden : Tendsto (slope ℘[L] z) (𝓝[≠] z) (𝓝 (℘'[L] z)) :=
    hasDerivAt_iff_tendsto_slope.mp hP
  refine Tendsto.congr' ?_ (hnum.div hden h0)
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hwz : w - z ≠ 0 := sub_ne_zero.mpr hw
  simp only [Pi.div_apply]
  rw [slope_def_field, slope_def_field, chordSlope]
  by_cases hPw : ℘[L] w = ℘[L] z
  · rw [hPw]
    simp
  · have hB : ℘[L] w - ℘[L] z ≠ 0 := sub_ne_zero.mpr hPw
    have hB' : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr (Ne.symm hPw)
    field_simp
    ring

/-! ## §H The duplication formulas, as limits `w → z` of the chord formulas -/

/-- On a punctured neighbourhood of a non-critical, non-2-torsion `z`, the chord-formula
hypotheses hold for the pair `(z, w)`.  The `℘ z ≠ ℘ w` clause uses that `℘ - ℘ z` cannot
vanish on a neighbourhood of `z`: its derivative there would be `℘' z ≠ 0`. -/
private theorem eventually_chord_conditions {z : ℂ} (hz : z ∉ L.lattice) (h0 : ℘'[L] z ≠ 0)
    (hzz : z + z ∉ L.lattice) :
    ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice ∧ z + w ∉ L.lattice ∧ ℘[L] z ≠ ℘[L] w := by
  have hne : ∀ᶠ w in 𝓝[≠] z, ℘[L] z ≠ ℘[L] w := by
    rcases ((L.analyticOnNhd_weierstrassP z hz).sub
      analyticAt_const).eventually_eq_zero_or_eventually_ne_zero with hcase | hcase
    · exfalso
      apply h0
      have hev : (fun w ↦ ℘[L] w - ℘[L] z) =ᶠ[𝓝 z] fun _ ↦ (0 : ℂ) := by
        filter_upwards [hcase] with u hu
        simpa using hu
      have hP : HasDerivAt (fun w ↦ ℘[L] w - ℘[L] z) (℘'[L] z) z := by
        have h := (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
        have h2 := h.sub_const (℘[L] z)
        rwa [L.deriv_weierstrassP] at h2
      have hd := hev.deriv_eq
      rwa [hP.deriv, deriv_const] at hd
    · filter_upwards [hcase] with w hw
      exact fun heq ↦ hw (sub_eq_zero.mpr heq.symm)
  have hΛ : ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      (L.isClosed_lattice.isOpen_compl.mem_nhds hz)] with w hw
    exact hw
  have hzw : ∀ᶠ w in 𝓝[≠] z, z + w ∉ L.lattice := by
    have hc : ContinuousAt (fun w : ℂ ↦ z + w) z :=
      (continuous_const.add continuous_id).continuousAt
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      (hc.eventually_mem (L.isClosed_lattice.isOpen_compl.mem_nhds hzz))] with w hw
    exact hw
  filter_upwards [hΛ, hzw, hne] with w h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- **Duplication formula, X-coordinate.**  `℘(2z) = (℘''(z)/(2℘'(z)))² - 2℘(z)`, obtained as
the limit `w → z` of the chord formula `weierstrassP_add_of_euler` via
`tendsto_chordSlope_self`; `℘'(z) ≠ 0` because `2z ∉ Λ`
(`two_mul_mem_lattice_of_derivWeierstrassP_eq_zero`). -/
theorem weierstrassP_two_mul {z : ℂ} (hz : z ∉ L.lattice) (h2z : 2 * z ∉ L.lattice) :
    ℘[L] (2 * z)
      = ((6 * ℘[L] z ^ 2 - L.g₂ / 2) / (2 * ℘'[L] z)) ^ 2 - 2 * ℘[L] z := by
  have h0 : ℘'[L] z ≠ 0 :=
    fun h ↦ h2z (L.two_mul_mem_lattice_of_derivWeierstrassP_eq_zero hz h)
  have hzz : z + z ∉ L.lattice := fun h ↦ h2z (by rwa [two_mul])
  have hLHS : Tendsto (fun w : ℂ ↦ ℘[L] (z + w)) (𝓝[≠] z) (𝓝 (℘[L] (z + z))) := by
    have h℘ : ContinuousAt ℘[L] (z + z) :=
      (L.analyticOnNhd_weierstrassP (z + z) hzz).continuousAt
    exact (h℘.comp ((continuous_const.add continuous_id).continuousAt)).mono_left
      nhdsWithin_le_nhds
  have hRHS : Tendsto (fun w : ℂ ↦ L.chordSlope z w ^ 2 / 4 - ℘[L] z - ℘[L] w) (𝓝[≠] z)
      (𝓝 (((6 * ℘[L] z ^ 2 - L.g₂ / 2) / ℘'[L] z) ^ 2 / 4 - ℘[L] z - ℘[L] z)) := by
    have h℘ : Tendsto ℘[L] (𝓝[≠] z) (𝓝 (℘[L] z)) :=
      ((L.analyticOnNhd_weierstrassP z hz).continuousAt).mono_left nhdsWithin_le_nhds
    exact ((((L.tendsto_chordSlope_self hz h0).pow 2).div_const 4).sub
      tendsto_const_nhds).sub h℘
  have hev : (fun w : ℂ ↦ ℘[L] (z + w)) =ᶠ[𝓝[≠] z]
      fun w : ℂ ↦ L.chordSlope z w ^ 2 / 4 - ℘[L] z - ℘[L] w := by
    filter_upwards [L.eventually_chord_conditions hz h0 hzz] with w hw
    obtain ⟨h1, h2, h3⟩ := hw
    rw [L.weierstrassP_add_of_euler hz h1 h2 h3, chordSlope]
    have hD : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr h3
    field_simp
    ring
  have huniq := tendsto_nhds_unique (hLHS.congr' hev) hRHS
  rw [show (2 : ℂ) * z = z + z from two_mul z, huniq]
  have h2 : (2 : ℂ) * ℘'[L] z ≠ 0 := mul_ne_zero two_ne_zero h0
  field_simp
  ring

/-- **Duplication formula, Y-coordinate.**  The limit `w → z` of the chord formula
`derivWeierstrassP_add_of_euler`. -/
theorem derivWeierstrassP_two_mul {z : ℂ} (hz : z ∉ L.lattice) (h2z : 2 * z ∉ L.lattice) :
    ℘'[L] (2 * z)
      = -((6 * ℘[L] z ^ 2 - L.g₂ / 2) / ℘'[L] z * (℘[L] (2 * z) - ℘[L] z) + ℘'[L] z) := by
  have h0 : ℘'[L] z ≠ 0 :=
    fun h ↦ h2z (L.two_mul_mem_lattice_of_derivWeierstrassP_eq_zero hz h)
  have hzz : z + z ∉ L.lattice := fun h ↦ h2z (by rwa [two_mul])
  have hLHS : Tendsto (fun w : ℂ ↦ ℘'[L] (z + w)) (𝓝[≠] z) (𝓝 (℘'[L] (z + z))) := by
    have h℘ : ContinuousAt ℘'[L] (z + z) :=
      (L.analyticOnNhd_derivWeierstrassP (z + z) hzz).continuousAt
    exact (h℘.comp ((continuous_const.add continuous_id).continuousAt)).mono_left
      nhdsWithin_le_nhds
  have h℘c : Tendsto (fun w : ℂ ↦ ℘[L] (z + w)) (𝓝[≠] z) (𝓝 (℘[L] (z + z))) := by
    have h℘ : ContinuousAt ℘[L] (z + z) :=
      (L.analyticOnNhd_weierstrassP (z + z) hzz).continuousAt
    exact (h℘.comp ((continuous_const.add continuous_id).continuousAt)).mono_left
      nhdsWithin_le_nhds
  have hRHS : Tendsto
      (fun w : ℂ ↦ -(L.chordSlope z w * (℘[L] (z + w) - ℘[L] z) + ℘'[L] z)) (𝓝[≠] z)
      (𝓝 (-((6 * ℘[L] z ^ 2 - L.g₂ / 2) / ℘'[L] z * (℘[L] (z + z) - ℘[L] z) + ℘'[L] z))) :=
    (((L.tendsto_chordSlope_self hz h0).mul (h℘c.sub tendsto_const_nhds)).add
      tendsto_const_nhds).neg
  have hev : (fun w : ℂ ↦ ℘'[L] (z + w)) =ᶠ[𝓝[≠] z]
      fun w : ℂ ↦ -(L.chordSlope z w * (℘[L] (z + w) - ℘[L] z) + ℘'[L] z) := by
    filter_upwards [L.eventually_chord_conditions hz h0 hzz] with w hw
    obtain ⟨h1, h2, h3⟩ := hw
    rw [L.derivWeierstrassP_add_of_euler hz h1 h2 h3, chordSlope]
  have huniq := tendsto_nhds_unique (hLHS.congr' hev) hRHS
  rw [show (2 : ℂ) * z = z + z from two_mul z]
  exact huniq

/-!
### Status

Every declaration in this file is proved — no `sorry` anywhere.  Together the file supplies,
over `forward.lean` alone:

* the addition theorem for `℘` and `℘'` (`weierstrassP_add_of_euler`,
  `derivWeierstrassP_add_of_euler`) — the two analytic identities isolated in `addition.lean`;
* the fiber lemma `sub_mem_or_add_mem_of_weierstrassP_eq` and 2-torsion characterisation
  `two_mul_mem_lattice_of_derivWeierstrassP_eq_zero`;
* the duplication formulas `weierstrassP_two_mul`, `derivWeierstrassP_two_mul`.

These are exactly the ingredients `addition.lean` needs to close all three of its `sorry`s
(chord case, Y-coordinate, and the doubling branch of `toPoint_add`), making the uniformization
map `φ : ℂ/Λ → E(ℂ)` an `AddMonoidHom` with no analytic debt left.
-/

end PeriodPair
