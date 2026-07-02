import Mathlib

open PeriodPair

/-!
# Bridge: the Weierstrass lattice Eisenstein series `G` is a modular form
`Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass` defines, for a period pair `L`, the
**lattice Eisenstein series**
PeriodPair.G L n = ∑' l : L.lattice, (l ^ n)⁻¹
and explicitly leaves open `TODO: Establish connections with the ModularForm library.`
`Mathlib.NumberTheory.ModularForms.EisensteinSeries` defines, for `z : ℍ`, the **modular
Eisenstein series**

eisensteinSeries (a : Fin 2 → ZMod N) k z = ∑' v : gammaSet N 1 a, (v 0 * z + v 1) ^ (-k)

which it packages as a genuine `ModularForm Γ(N) k` (`ModularForm.eisensteinSeriesMF`), and, at
level one, as the normalised forms `ModularForm.E k` (with `E₄`, `E₆`).
This file is the **skeleton of the bridge** between the two. The strategy is:
1. Attach to `τ ∈ ℍ` the period pair `(1, τ)`, whose lattice is `ℤ + ℤτ` (`periodPair`).
2. Reindex the lattice sum `G_k(ℤ + ℤτ)` as a sum of `eisSummand` over all of `Fin 2 → ℤ`
(`G_eq_tsum_eisSummand`) — the combinatorial heart, mapping `m + nτ ↦ ![n, m]`.
3. Feed that into the existing Mathlib identity
`EisensteinSeries.tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries`, which evaluates the
full sum over `Fin 2 → ℤ` as `ζ(k) · eisensteinSeries 0 k z` by factoring out the gcd.
4. Conclude that `τ ↦ G_k(ℤ + ℤτ)` equals the modular form `2 ζ(k) · E_k`, hence **is** a
modular form (`GMF`, `GMF_apply`).
The skeleton is `sorry`-free: every step above is proved, with the heavy lifting of step (3)
delegated to the existing Mathlib lemma
`EisensteinSeries.tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries`.
## Main definitions and results
* `GaloisGroupCertification.ModularForms.periodPair` — the period pair `(1, τ)` for `τ ∈ ℍ`.
* `GaloisGroupCertification.ModularForms.G_eq_tsum_eisSummand` — the lattice/`Fin 2 → ℤ` reindexing.
* `GaloisGroupCertification.ModularForms.G_eq_riemannZeta_mul_eisensteinSeries` — the bridge to
the modular Eisenstein series.
* `GaloisGroupCertification.ModularForms.GMF` — `τ ↦ G_k(ℤ + ℤτ)` as a bona fide `ModularForm`.
* `GaloisGroupCertification.ModularForms.GMF_apply` — its values are the lattice series `G`.
-/
open Complex UpperHalfPlane EisensteinSeries ModularForm
open scoped UpperHalfPlane CongruenceSubgroup MatrixGroups
noncomputable section
/-! ### The period pair attached to `τ ∈ ℍ` -/
/-- `1` and `τ` are `ℝ`-linearly independent for `τ` in the upper half-plane (its imaginary
part is positive, in particular nonzero). -/
lemma linearIndependent_one_coe (τ : ℍ) : LinearIndependent ℝ ![(1 : ℂ), (τ : ℂ)] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  -- Take imaginary parts of `s • 1 + t • τ = 0`: only the `t τ.im` term survives.
  have him : t * (τ : ℂ).im = 0 := by
    have := congrArg Complex.im hst
    simpa [Complex.real_smul, Complex.add_im, Complex.mul_im] using this
  have htim : (τ : ℂ).im ≠ 0 := by
    simpa [UpperHalfPlane.coe_im] using τ.im_ne_zero
  have ht : t = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h htim
  refine ⟨?_, ht⟩
  -- With `t = 0`, the relation reads `s • 1 = 0`, forcing `s = 0`.
  have : (s : ℂ) = 0 := by simpa [ht, Complex.real_smul] using hst
  exact_mod_cast this

/-- The period pair `(ω₁, ω₂) = (1, τ)` attached to `τ ∈ ℍ`. Its `lattice` is `ℤ + ℤτ`. -/
def periodPair (τ : ℍ) : PeriodPair where
  ω₁ := 1
  ω₂ := τ
  indep := linearIndependent_one_coe τ

@[simp] lemma periodPair_ω₁ (τ : ℍ) : (periodPair τ).ω₁ = 1 := rfl

@[simp] lemma periodPair_ω₂ (τ : ℍ) : (periodPair τ).ω₂ = (τ : ℂ) := rfl

/-! ### Reindexing the lattice sum (analytic core) -/
/-- **Reindexing (combinatorial core of the bridge).**
The lattice sum defining `G_k` for the lattice `ℤ + ℤτ` is the full sum of `eisSummand` over
`Fin 2 → ℤ`. Concretely the lattice point `l = m·1 + n·τ` corresponds to the vector `![n, m]`,
under which `(l ^ k)⁻¹ = (n·τ + m) ^ (-k) = eisSummand k ![n, m] τ`.
Proof sketch: transport the `tsum` along `PeriodPair.latticeEquivProd` (`L.lattice ≃ₗ ℤ × ℤ`,
with `latticeEquiv_symm_apply : (latticeEquivProd L).symm (a, b) = a·ω₁ + b·ω₂`) composed with
`finTwoArrowEquiv`, then rewrite `(l ^ k)⁻¹ = l ^ (-k : ℤ)` via `zpow_neg`/`zpow_natCast` and
unfold `eisSummand`. -/
lemma G_eq_tsum_eisSummand (τ : ℍ) (k : ℕ) :
(periodPair τ).G k = ∑' v : Fin 2 → ℤ, eisSummand k v τ := by
  set L := periodPair τ with hL
  -- The reindexing bijection `![v 0, v 1] ↦ v 1 · 1 + v 0 · τ ∈ ℤ + ℤτ`.
  let e : (Fin 2 → ℤ) ≃ L.lattice :=
    ((finTwoArrowEquiv ℤ).trans (Equiv.prodComm ℤ ℤ)).trans L.latticeEquivProd.symm.toEquiv
  rw [PeriodPair.G, ← e.tsum_eq (fun l : L.lattice => ((l : ℂ) ^ k)⁻¹)]
  refine tsum_congr fun v => ?_
  have hev : ((e v : L.lattice) : ℂ) = (v 0 : ℂ) * (τ : ℂ) + (v 1 : ℂ) := by
    have := L.latticeEquiv_symm_apply ((Equiv.prodComm ℤ ℤ) (finTwoArrowEquiv ℤ v))
    simp only [e, Equiv.trans_apply, LinearEquiv.coe_toEquiv, Equiv.prodComm_apply,
      finTwoArrowEquiv_apply] at this ⊢
    rw [this]
    simp [hL, periodPair]
    ring
  rw [hev, eisSummand, zpow_neg, zpow_natCast]

/-! ### The bridge -/
/-- **Bridge to the modular Eisenstein series.** For weight `k ≥ 3`, the Weierstrass lattice
Eisenstein series of `ℤ + ℤτ` equals `ζ(k)` times Mathlib's level-one modular Eisenstein
series `eisensteinSeries 0 k`. -/
theorem G_eq_riemannZeta_mul_eisensteinSeries (τ : ℍ) {k : ℕ} (hk : 3 ≤ k) :
    (periodPair τ).G k = riemannZeta k * eisensteinSeries (N := 1) 0 k τ := by
  rw [G_eq_tsum_eisSummand, tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk]

/-- The level-one normalised Eisenstein series `E_k` is half the unnormalised one (it is summed
over coprime pairs). -/
lemma E_apply {k : ℕ} (hk : 3 ≤ k) (τ : ℍ) :
(ModularForm.E hk τ : ℂ) = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := by
  -- `E hk τ = (1/2) • eisensteinSeriesSIF 0 k τ` holds definitionally (see Mathlib's
  -- `EisensteinSeries.q_expansion_riemannZeta`), and `eisensteinSeriesSIF 0 k = eisensteinSeries 0 k`.
  rw [show ModularForm.E hk τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 k τ from rfl,
    eisensteinSeriesSIF_apply, smul_eq_mul]

/-- **`G` is a modular form (pointwise identity).** For weight `k ≥ 3`, the Weierstrass lattice
Eisenstein series of `ℤ + ℤτ` is the nonzero constant `2 ζ(k)` times the level-one weight-`k`
modular form `E_k`. -/
theorem G_eq_two_riemannZeta_mul_E (τ : ℍ) {k : ℕ} (hk : 3 ≤ k) :
    (periodPair τ).G k = 2 * riemannZeta k * (ModularForm.E hk τ : ℂ) := by
  rw [G_eq_riemannZeta_mul_eisensteinSeries τ hk, E_apply hk]
  ring

/-! ### Packaging `G` as a genuine `ModularForm`
Scalar multiples of modular forms are modular forms, so `2 ζ(k) • E_k` is an honest
`ModularForm 𝒮ℒ k` whose values are exactly the lattice Eisenstein series `G_k(ℤ + ℤτ)`. This
is the sense in which "`G` is a modular form". -/
/-- The level-one weight-`k` **modular form** whose value at `τ` is the Weierstrass lattice
Eisenstein series `G_k(ℤ + ℤτ)`. -/
def GMF {k : ℕ} (hk : 3 ≤ k) : ModularForm 𝒮ℒ k := (2 * riemannZeta k) • ModularForm.E hk

/-- The modular form `GMF` indeed evaluates to the lattice Eisenstein series `G`. -/
theorem GMF_apply {k : ℕ} (hk : 3 ≤ k) (τ : ℍ) : (GMF hk τ : ℂ) = (periodPair τ).G k := by
  rw [GMF, ModularForm.IsGLPos.smul_apply, G_eq_two_riemannZeta_mul_E τ hk, smul_eq_mul, mul_assoc]


/-! ### The discriminant of the Weierstrass equation is nonzero

The Weierstrass equation `℘'² = 4℘³ - g₂℘ - g₃` (`PeriodPair.derivWeierstrassP_sq`) has on its
right-hand side the cubic `4x³ - g₂x - g₃`, whose polynomial discriminant is
`16 (g₂³ - 27 g₃²)`. We prove the **Weierstrass / modular discriminant**
`Δ := g₂³ - 27 g₃²` of the lattice `ℤ + ℤτ` is nonzero — equivalently the cubic has three
distinct roots, so `℘` parametrises a nonsingular elliptic curve.

The deduction runs through the bridge: `g₂ = 120 ζ(4) E₄(τ)` and `g₃ = 280 ζ(6) E₆(τ)`, and the
normalising constants satisfy `(120 ζ(4))³ = 27 (280 ζ(6))²` (a consequence of
`ζ(4) = π⁴/90`, `ζ(6) = π⁶/945`). Hence `g₂³ - 27 g₃² = (120 ζ(4))³ (E₄³ - E₆²)`, and
`E₄³ - E₆² = 1728 Δ_modular = 1728 η²⁴` is nonvanishing on `ℍ`
(`ModularForm.discriminant_ne_zero`). -/

open Real

private theorem bernoulli'_five : bernoulli' 5 = 0 := by
  rw [bernoulli'_def]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose]

private theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, bernoulli'_five]

/-- The value `ζ(6) = π⁶/945` (companion to Mathlib's `riemannZeta_four`). -/
theorem riemannZeta_six : riemannZeta 6 = (π : ℂ) ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  rw [show (2 * ((3 : ℕ) : ℂ)) = 6 by norm_num] at h
  rw [h, bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_six]
  norm_num [Nat.factorial]
  ring

/-- The matching of normalising constants `27 (280 ζ(6))² = (120 ζ(4))³`. -/
theorem zeta_const_identity :
    27 * (280 * riemannZeta 6) ^ 2 = (120 * riemannZeta 4) ^ 3 := by
  rw [riemannZeta_four, riemannZeta_six]; ring

/-- The **discriminant** `g₂³ - 27 g₃²` of the Weierstrass cubic `4x³ - g₂x - g₃`. (Its
polynomial discriminant as a cubic is `16` times this.) -/
def weierstrassDiscriminant (L : PeriodPair) : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

lemma g₂_periodPair (τ : ℍ) :
    (periodPair τ).g₂ = 120 * riemannZeta 4 * (E₄ τ : ℂ) := by
  rw [PeriodPair.g₂, G_eq_two_riemannZeta_mul_E τ (k := 4) (by norm_num)]
  push_cast
  ring

lemma g₃_periodPair (τ : ℍ) :
    (periodPair τ).g₃ = 280 * riemannZeta 6 * (E₆ τ : ℂ) := by
  rw [PeriodPair.g₃, G_eq_two_riemannZeta_mul_E τ (k := 6) (by norm_num)]
  push_cast
  ring

/-- The Weierstrass discriminant of `ℤ + ℤτ` factors through the modular combination
`E₄³ - E₆²`. -/
lemma weierstrassDiscriminant_periodPair (τ : ℍ) :
    weierstrassDiscriminant (periodPair τ)
      = (120 * riemannZeta 4) ^ 3 * (E₄ τ ^ 3 - E₆ τ ^ 2) := by
  rw [weierstrassDiscriminant, g₂_periodPair, g₃_periodPair]
  linear_combination (-(E₆ τ ^ 2)) * zeta_const_identity

/-- `E₄³ - E₆²` is nonzero at every `τ ∈ ℍ`, because it equals `1728 Δ` and the modular
discriminant `Δ = η²⁴` never vanishes. -/
lemma E₄_cube_sub_E₆_sq_ne_zero (τ : ℍ) : (E₄ τ : ℂ) ^ 3 - E₆ τ ^ 2 ≠ 0 := by
  intro h
  refine ModularForm.discriminant_ne_zero τ ?_
  rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, h, zero_div]

/-- **The discriminant of the Weierstrass equation is nonzero.** For the period lattice
`ℤ + ℤτ` (`τ ∈ ℍ`) of the Weierstrass `℘`-function, `g₂³ - 27 g₃² ≠ 0`; the cubic
`4x³ - g₂x - g₃` of the Weierstrass equation `℘'² = 4℘³ - g₂℘ - g₃` therefore has distinct
roots. -/
theorem weierstrassDiscriminant_periodPair_ne_zero (τ : ℍ) :
    weierstrassDiscriminant (periodPair τ) ≠ 0 := by
  rw [weierstrassDiscriminant_periodPair]
  refine mul_ne_zero (pow_ne_zero _ (mul_ne_zero (by norm_num) ?_)) (E₄_cube_sub_E₆_sq_ne_zero τ)
  exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)

/-! ### From `ℤ + ℤτ` to an arbitrary lattice

A general `PeriodPair L = ⟨ω₁, ω₂⟩` has lattice `ℤω₁ + ℤω₂ = ω₁ · (ℤ + ℤτ)` for `τ = ±ω₂/ω₁`
chosen in `ℍ` (the ratio is non-real by `ℝ`-linear independence). The lattice Eisenstein
series, hence `g₂`, `g₃` and the discriminant, are homogeneous under this scaling, so the
nonvanishing for `periodPair τ` transfers to every lattice. -/

/-- **Homogeneity of `G`.** A bijection `e : L.lattice ≃ L'.lattice` that scales by `c`
(`↑(e x) = c • x`) scales `Gₙ` by `c⁻ⁿ`. -/
lemma G_eq_smul_of_latticeEquiv {L L' : PeriodPair} {c : ℂ}
    (e : L.lattice ≃ L'.lattice) (he : ∀ x : L.lattice, ((e x : L'.lattice) : ℂ) = c * x)
    (n : ℕ) : L'.G n = (c ^ n)⁻¹ * L.G n := by
  simp only [PeriodPair.G]
  rw [← e.tsum_eq (fun y : L'.lattice => ((y : ℂ) ^ n)⁻¹), ← tsum_mul_left]
  refine tsum_congr fun x => ?_
  rw [he, mul_pow, mul_inv]

/-- The Weierstrass discriminant is homogeneous of degree `-12` under a scaling of lattices. -/
lemma weierstrassDiscriminant_smul_eq {L L' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (e : L.lattice ≃ L'.lattice) (he : ∀ x : L.lattice, ((e x : L'.lattice) : ℂ) = c * x) :
    weierstrassDiscriminant L' = (c ^ 12)⁻¹ * weierstrassDiscriminant L := by
  have h4 := G_eq_smul_of_latticeEquiv e he 4
  have h6 := G_eq_smul_of_latticeEquiv e he 6
  simp only [weierstrassDiscriminant, PeriodPair.g₂, PeriodPair.g₃, h4, h6]
  field_simp

/-- Builder: a `ℤ × ℤ`-automorphism `σ` realising the scaling `↑(e x) = ω₁⁻¹ • x` against the
basis `(1, τ)` produces the scaling equiv between `L.lattice` and `(periodPair τ).lattice`. -/
lemma exists_scalingEquiv_aux (L : PeriodPair) (τ : ℍ) (σ : ℤ × ℤ ≃ ℤ × ℤ)
    (hσ : ∀ a b : ℤ, ((σ (a, b)).1 : ℂ) * (periodPair τ).ω₁ + ((σ (a, b)).2 : ℂ)
            * (periodPair τ).ω₂ = (L.ω₁)⁻¹ * ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂)) :
    ∃ e : L.lattice ≃ (periodPair τ).lattice,
      ∀ x : L.lattice, ((e x : (periodPair τ).lattice) : ℂ) = (L.ω₁)⁻¹ * x := by
  refine ⟨L.latticeEquivProd.toEquiv.trans (σ.trans (periodPair τ).latticeEquivProd.symm.toEquiv),
    fun x => ?_⟩
  have hx : ((x : L.lattice) : ℂ)
      = (L.latticeEquivProd x).1 * L.ω₁ + (L.latticeEquivProd x).2 * L.ω₂ := by
    have h := L.latticeEquiv_symm_apply (L.latticeEquivProd x)
    rwa [L.latticeEquivProd.symm_apply_apply] at h
  have hex : ((L.latticeEquivProd.toEquiv.trans
        (σ.trans (periodPair τ).latticeEquivProd.symm.toEquiv) x :
        (periodPair τ).lattice) : ℂ)
      = ((σ (L.latticeEquivProd x)).1 : ℂ) * (periodPair τ).ω₁
        + ((σ (L.latticeEquivProd x)).2 : ℂ) * (periodPair τ).ω₂ :=
    (periodPair τ).latticeEquiv_symm_apply (σ (L.latticeEquivProd x))
  rw [hex, hx]
  exact hσ _ _

/-- **The discriminant of the Weierstrass equation is nonzero for every period lattice.** For an
arbitrary `PeriodPair L` (any lattice `ℤω₁ + ℤω₂` with `ω₁, ω₂` `ℝ`-linearly independent), the
Weierstrass discriminant `g₂³ - 27 g₃²` is nonzero, so the cubic `4x³ - g₂x - g₃` of
`℘'² = 4℘³ - g₂℘ - g₃` has three distinct roots. -/
theorem weierstrassDiscriminant_ne_zero (L : PeriodPair) :
    weierstrassDiscriminant L ≠ 0 := by
  have hω₁ : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  -- The ratio `ω₂/ω₁` is non-real, otherwise `ω₂` is a real multiple of `ω₁`.
  have hτ₀ : (L.ω₂ / L.ω₁).im ≠ 0 := by
    intro h
    have hτ0re : (L.ω₂ / L.ω₁ : ℂ) = ((L.ω₂ / L.ω₁).re : ℝ) := by
      apply Complex.ext <;> simp [h]
    have hω₂ : (L.ω₂ / L.ω₁).re • L.ω₁ = L.ω₂ := by
      rw [Complex.real_smul, ← hτ0re]; field_simp
    have h0 : (L.ω₂ / L.ω₁).re • L.ω₁ + (-1 : ℝ) • L.ω₂ = 0 := by rw [hω₂]; simp
    exact absurd ((LinearIndependent.pair_iff.mp L.indep) _ _ h0).2 (by norm_num)
  -- Reduce to `periodPair τ` via the scaling equiv (degree `-12` homogeneity).
  suffices h : ∃ (τ : ℍ) (e : L.lattice ≃ (periodPair τ).lattice),
      ∀ x : L.lattice, ((e x : (periodPair τ).lattice) : ℂ) = (L.ω₁)⁻¹ * x by
    obtain ⟨τ, e, he⟩ := h
    intro hL
    have := weierstrassDiscriminant_smul_eq (c := (L.ω₁)⁻¹) (by simpa using hω₁) e he
    rw [hL, mul_zero] at this
    exact weierstrassDiscriminant_periodPair_ne_zero τ this
  rcases lt_or_gt_of_ne hτ₀ with h | h
  · -- `(ω₂/ω₁).im < 0`: take `τ = -(ω₂/ω₁) ∈ ℍ` and flip the second coordinate.
    refine ⟨UpperHalfPlane.mk (-(L.ω₂ / L.ω₁)) (by rw [Complex.neg_im]; exact neg_pos.mpr h), ?_⟩
    apply exists_scalingEquiv_aux L _ (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ))
    intro a b
    simp only [periodPair_ω₁, periodPair_ω₂, Equiv.prodCongr_apply, Equiv.coe_refl,
      Equiv.neg_apply, Prod.map_apply, id_eq]
    grind
  · -- `(ω₂/ω₁).im > 0`: take `τ = ω₂/ω₁ ∈ ℍ` and the identity reindexing.
    refine ⟨UpperHalfPlane.mk (L.ω₂ / L.ω₁) h, ?_⟩
    apply exists_scalingEquiv_aux L _ (Equiv.refl (ℤ × ℤ))
    grind [periodPair_ω₁, periodPair_ω₂]


/-! ### The elliptic curve attached to a period lattice

The Weierstrass equation `℘'² = 4℘³ - g₂℘ - g₃` (`PeriodPair.derivWeierstrassP_sq`) becomes, after
the substitution `(x, y) = (℘, ½ ℘')`, the short Weierstrass form `y² = x³ - (g₂/4) x - (g₃/4)`.
We package this as a Mathlib `WeierstrassCurve ℂ` and, using the nonvanishing of the discriminant
(`weierstrassDiscriminant_ne_zero`), give it the `IsElliptic` instance: it is a genuine elliptic
curve over `ℂ`, so `j`-invariant and all of the elliptic-curve API become available on it. -/

/-- The (short) **Weierstrass curve** `y² = x³ - (g₂/4) x - (g₃/4)` attached to a period pair `L`.
It is the image of the Weierstrass equation `℘'² = 4℘³ - g₂℘ - g₃` under `(x, y) = (℘, ½ ℘')`. -/
def PeriodPair.weierstrassCurve (L : PeriodPair) : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -L.g₂ / 4
  a₆ := -L.g₃ / 4

/-- The Mathlib discriminant of `L.weierstrassCurve` is the lattice discriminant `g₂³ - 27 g₃²`. -/
@[simp] lemma PeriodPair.weierstrassCurve_Δ (L : PeriodPair) :
    L.weierstrassCurve.Δ = weierstrassDiscriminant L := by
  grind [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, PeriodPair.weierstrassCurve, weierstrassDiscriminant]

/-- The Weierstrass curve of a period pair is an **elliptic curve**: its discriminant is a unit
(it is nonzero in the field `ℂ`). -/
instance (L : PeriodPair) : L.weierstrassCurve.IsElliptic where
  isUnit := by
    rw [PeriodPair.weierstrassCurve_Δ]
    exact isUnit_iff_ne_zero.mpr (weierstrassDiscriminant_ne_zero L)

/-- The discriminant `Δ'` (as a unit) of the elliptic curve of `L` is the lattice discriminant. -/
lemma PeriodPair.coe_weierstrassCurve_Δ' (L : PeriodPair) :
    (L.weierstrassCurve.Δ' : ℂ) = weierstrassDiscriminant L := by
  rw [WeierstrassCurve.coe_Δ', PeriodPair.weierstrassCurve_Δ]

/-! ### The `j`-invariant of the elliptic curve of `L` in terms of `g₂`, `g₃`

The classical modular invariants of the Weierstrass `℘`-function of `L` are `g₂ = 60 G₄` and
`g₃ = 140 G₆`.  The `j`-invariant of the elliptic curve `L.weierstrassCurve` (Mathlib's
`WeierstrassCurve.j`) is, classically, `j = 1728 g₂³ / (g₂³ - 27 g₃²)`.  The lemmas below provide
that bridge: first the `c`-invariants `c₄ = 12 g₂`, `c₆ = 216 g₃`, then the closed form for `j`. -/

/-- The `c₄`-invariant of the elliptic curve `y² = x³ - (g₂/4)x - (g₃/4)` of `L` is `12 g₂`. -/
@[simp] lemma PeriodPair.weierstrassCurve_c₄ (L : PeriodPair) :
    L.weierstrassCurve.c₄ = 12 * L.g₂ := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    PeriodPair.weierstrassCurve]
  ring

/-- The `c₆`-invariant of the elliptic curve `y² = x³ - (g₂/4)x - (g₃/4)` of `L` is `216 g₃`. -/
@[simp] lemma PeriodPair.weierstrassCurve_c₆ (L : PeriodPair) :
    L.weierstrassCurve.c₆ = 216 * L.g₃ := by
  simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    PeriodPair.weierstrassCurve]
  ring

/-- **The `j`-invariant of the elliptic curve of `L` as a function of the lattice invariants.**
For the elliptic curve `L.weierstrassCurve` attached to the Weierstrass `℘`-function of `L`, the
`j`-invariant is the classical expression `1728 g₂³ / (g₂³ - 27 g₃²)` in the modular invariants
`g₂ = 60 G₄(L)` and `g₃ = 140 G₆(L)`.  (The denominator `g₂³ - 27 g₃²` is the Weierstrass
discriminant `weierstrassDiscriminant L`, which is nonzero by `weierstrassDiscriminant_ne_zero`.) -/
theorem PeriodPair.weierstrassCurve_j (L : PeriodPair) :
    L.weierstrassCurve.j = 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  grind [WeierstrassCurve.j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul,
    WeierstrassCurve.coe_Δ', PeriodPair.weierstrassCurve_Δ, weierstrassDiscriminant,
    PeriodPair.weierstrassCurve_c₄]

/-- The same identity with the denominator written as the Weierstrass discriminant. -/
theorem PeriodPair.weierstrassCurve_j_eq_div_discriminant (L : PeriodPair) :
    L.weierstrassCurve.j = 1728 * L.g₂ ^ 3 / weierstrassDiscriminant L := by
  rw [PeriodPair.weierstrassCurve_j, weierstrassDiscriminant]

def f := fun τ => (periodPair τ).weierstrassCurve.j

lemma f_eq_j (τ : ℍ) : f τ =
1728 * (E₄ τ : ℂ) ^ 3 / (E₄ τ ^ 3 - E₆ τ ^ 2) := by
  have hz : (riemannZeta 4 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have ha : (120 * riemannZeta 4 : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hz
  have ha3 : (120 * riemannZeta 4 : ℂ) ^ 3 ≠ 0 := pow_ne_zero _ ha
  have hE : (E₄ τ : ℂ) ^ 3 - E₆ τ ^ 2 ≠ 0 := E₄_cube_sub_E₆_sq_ne_zero τ
  simp only [f, weierstrassCurve_j_eq_div_discriminant, weierstrassDiscriminant_periodPair,
    g₂_periodPair, mul_pow]
  field_simp


/-! ### Proposition 3.6(b): the uniformization map `φ : ℂ/Λ → E(ℂ)`

Proposition 3.6(b) constructs the map
`φ : ℂ/Λ ⟶ E(ℂ) ⊂ ℙ²(ℂ),   z ↦ [℘(z), ℘'(z), 1]`
and asserts it is a complex-analytic **isomorphism of complex Lie groups** — i.e. a bijective
group homomorphism.

This section constructs `φ` and the group-homomorphism *structure* around it.  In Mathlib's
affine coordinates the elliptic curve of `L` is `E : y² = x³ - (g₂/4) x - (g₃/4)`
(`PeriodPair.weierstrassCurve`), and the projective point `[℘, ℘', 1]` corresponds to the affine
point `(x, y) = (℘, ½℘')`: this is exactly the substitution turning the Weierstrass equation
`℘'² = 4℘³ - g₂℘ - g₃` (`derivWeierstrassP_sq`) into the curve equation.  The point at infinity
`[0 : 1 : 0]` is the image of the lattice points (`z ∈ Λ`, where `℘` has its pole).

What is proved sorry-free here:
* `PeriodPair.toPoint` / `PeriodPair.uniformization` — the map `φ` (as a lift `ℂ → E(ℂ)` and its
  descent to the quotient `ℂ/Λ`);
* `PeriodPair.weierstrassCurve_equation` — the image lands on the curve;
* well-definedness on `ℂ/Λ` (`toPoint_add_mem`, built into the descent);
* `uniformization_zero` — `φ(0) = O` (the point at infinity), and
* `uniformization_neg` — `φ(-z) = -φ(z)` (compatibility with negation).

The remaining `map_add'` property is the analytic **addition theorem** for `℘`.  It is proved in
`LeanBridge.work.addition_euler` (Euler's differential-equation argument) and assembled in
`LeanBridge.work.addition`, where `φ` is upgraded to the `AddMonoidHom`
`PeriodPair.uniformizationHom`. -/

open WeierstrassCurve.Affine in
/-- The image `(℘(z), ½℘'(z))` of a non-lattice point satisfies the Weierstrass equation of the
curve `E : y² = x³ - (g₂/4) x - (g₃/4)` of `L`.  This is the substitution `(x, y) = (℘, ½℘')`
applied to `℘'² = 4℘³ - g₂℘ - g₃`. -/
lemma PeriodPair.weierstrassCurve_equation (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    L.weierstrassCurve.toAffine.Equation (℘[L] z) (℘'[L] z / 2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [PeriodPair.weierstrassCurve]
  linear_combination (L.derivWeierstrassP_sq z hz) / 4

open Classical in
/-- **The uniformization map `φ`, as a lift `ℂ → E(ℂ)`.**  `z ↦ (℘(z), ½℘'(z))` for `z ∉ Λ`, and
`z ↦ O` (the point at infinity) for `z ∈ Λ`.  (Nonsingularity of the affine image is automatic on
an elliptic curve, `equation_iff_nonsingular`.) -/
def PeriodPair.toPoint (L : PeriodPair) (z : ℂ) : L.weierstrassCurve.toAffine.Point :=
  if hz : z ∈ L.lattice then 0
  else .some (℘[L] z) (℘'[L] z / 2)
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp (L.weierstrassCurve_equation hz))

/-- **Well-definedness on `ℂ/Λ`.**  `φ` is invariant under translation by a lattice point, because
`℘` and `℘'` are periodic (`weierstrassP_add_coe`, `derivWeierstrassP_add_coe`). -/
lemma PeriodPair.toPoint_add_mem (L : PeriodPair) (z : ℂ) (l : L.lattice) :
    L.toPoint (z + l) = L.toPoint z := by
  by_cases hz : z ∈ L.lattice
  · simp only [PeriodPair.toPoint, dif_pos (add_mem hz l.2), dif_pos hz]
  · have hzl : z + (l : ℂ) ∉ L.lattice := fun h => hz (by simpa using sub_mem h l.2)
    simp only [PeriodPair.toPoint, dif_neg hzl, dif_neg hz]
    congr 1
    · exact L.weierstrassP_add_coe z l
    · rw [L.derivWeierstrassP_add_coe z l]

/-- **Compatibility with negation.**  `φ(-z) = -φ(z)`, because `℘` is even and `℘'` is odd
(`weierstrassP_neg`, `derivWeierstrassP_neg`) and negation on `E` is `(x, y) ↦ (x, -y)`. -/
lemma PeriodPair.toPoint_neg (L : PeriodPair) (z : ℂ) : L.toPoint (-z) = - L.toPoint z := by
  by_cases hz : z ∈ L.lattice
  · simp only [PeriodPair.toPoint, dif_pos (neg_mem hz), dif_pos hz, neg_zero]
  · have hz' : -z ∉ L.lattice := fun h => hz (by simpa using neg_mem h)
    simp only [PeriodPair.toPoint, dif_neg hz', dif_neg hz,
      WeierstrassCurve.Affine.Point.neg_some]
    congr 1
    · exact L.weierstrassP_neg z
    · rw [WeierstrassCurve.Affine.negY, L.derivWeierstrassP_neg z]
      simp only [PeriodPair.weierstrassCurve]
      ring

/-- **The uniformization map `φ : ℂ/Λ → E(ℂ)`** of Proposition 3.6(b), descended from the lift
`PeriodPair.toPoint` via its lattice-translation invariance. -/
def PeriodPair.uniformization (L : PeriodPair) :
    (ℂ ⧸ L.lattice.toAddSubgroup) → L.weierstrassCurve.toAffine.Point := fun q =>
  Quotient.liftOn' q L.toPoint (by
    intro a b hab
    rw [QuotientAddGroup.leftRel_apply, Submodule.mem_toAddSubgroup] at hab
    have hmem : b - a ∈ L.lattice := by
      simpa [sub_eq_neg_add] using hab
    have h := L.toPoint_add_mem a ⟨b - a, hmem⟩
    rw [add_sub_cancel] at h
    exact h.symm)

@[simp] lemma PeriodPair.uniformization_mk (L : PeriodPair) (z : ℂ) :
    L.uniformization (QuotientAddGroup.mk z) = L.toPoint z := rfl

/-- `φ(O) = O`: the identity `0 ∈ ℂ/Λ` maps to the point at infinity. -/
@[simp] lemma PeriodPair.uniformization_zero (L : PeriodPair) :
    L.uniformization 0 = 0 := by
  show L.toPoint 0 = _
  simp only [PeriodPair.toPoint, dif_pos (zero_mem _)]

/-- **`φ` respects negation:** `φ(-q) = -φ(q)`. -/
lemma PeriodPair.uniformization_neg (L : PeriodPair) (q : ℂ ⧸ L.lattice.toAddSubgroup) :
    L.uniformization (-q) = - L.uniformization q := by
  induction q using QuotientAddGroup.induction_on with
  | _ z =>
    have h : (-(QuotientAddGroup.mk z) : ℂ ⧸ L.lattice.toAddSubgroup)
        = QuotientAddGroup.mk (-z) := (map_neg (QuotientAddGroup.mk' _) z).symm
    rw [h, uniformization_mk, uniformization_mk, L.toPoint_neg]

/-! ### The addition theorem

Bundling `φ` as a genuine `AddMonoidHom ℂ/Λ → E(ℂ)` needs additivity
`φ(z + w) = φ(z) + φ(w)`, i.e. the classical **addition theorem** for the Weierstrass
`℘`-function matched against the chord–tangent group law on `E`.  This is proved downstream:
the analytic input lives in `LeanBridge.work.addition_euler` (sorry-free), and
`LeanBridge.work.addition` assembles it into `PeriodPair.uniformization_add` and the
`AddMonoidHom` `PeriodPair.uniformizationHom`.  Everything in this file is `sorry`-free. -/
