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
    push_cast
    field_simp
  · -- `(ω₂/ω₁).im > 0`: take `τ = ω₂/ω₁ ∈ ℍ` and the identity reindexing.
    refine ⟨UpperHalfPlane.mk (L.ω₂ / L.ω₁) h, ?_⟩
    apply exists_scalingEquiv_aux L _ (Equiv.refl (ℤ × ℤ))
    intro a b
    simp only [periodPair_ω₁, periodPair_ω₂, Equiv.refl_apply]
    field_simp
