import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import LeanBridge.SayebWork.uniqueness

/-!
# Scaling and conjugation of the lattice invariants `g₂`, `g₃`, `j`

For a period pair `L` (with lattice `Λ = L.lattice`), a scale `a : ℂˣ`, and complex
conjugation, we prove:

* `PeriodPair.g₂_smul`, `PeriodPair.g₃_smul`, `PeriodPair.j_smul`:
  `g₂ (a • L) = (a ^ 4)⁻¹ * g₂ L`, `g₃ (a • L) = (a ^ 6)⁻¹ * g₃ L`, `j (a • L) = j L`.
* `PeriodPair.g₂_conjugate`, `PeriodPair.g₃_conjugate`, `PeriodPair.j_conjugate`:
  `g₂ L̄ = conj (g₂ L)`, and similarly for `g₃`, `j`.
* `PeriodPair.smul_lattice_eq_iff`: for `g₂ L ≠ 0` and `g₃ L ≠ 0`, `aΛ = Λ ↔ a = ±1`;
  `PeriodPair.smul_lattice_eq_iff_of_g₃_eq_zero` (`aΛ = Λ ↔ a⁴ = 1` when `g₃ L = 0`, where
  `j L = 1728`) and `PeriodPair.smul_lattice_eq_iff_of_g₂_eq_zero` (`aΛ = Λ ↔ a⁶ = 1` when
  `g₂ L = 0`, where `j L = 0`).
* `PeriodPair.isReal_iff`: `Λ` is real (`Λ̄ = Λ`) iff `g₂ L` and `g₃ L` are both real.

The classical facts that the discriminant `g₂³ - 27 g₃²` of a lattice never vanishes and that a
lattice is determined by its invariants (`PeriodPair.InvariantsDetermineLattice`) are not yet in
Mathlib; theorems needing them take them as explicit hypotheses, so this file is `sorry`-free.
-/

open scoped ComplexConjugate

noncomputable section

namespace PeriodPair

/-! ### Scaling and conjugating period pairs -/

/-- The period pair scaled by a nonzero complex number: `a • L` has periods `a * ω₁`, `a * ω₂`,
so its lattice is `a * L.lattice`. -/
protected def smul (a : ℂˣ) (L : PeriodPair) : PeriodPair where
  ω₁ := a * L.ω₁
  ω₂ := a * L.ω₂
  indep := by
    refine LinearIndependent.pair_iff.mpr fun s t hst =>
      LinearIndependent.pair_iff.mp L.indep s t ?_
    have h : (a : ℂ) * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [mul_add, mul_smul_comm, mul_smul_comm]
      exact hst
    exact (mul_eq_zero.mp h).resolve_left a.ne_zero

instance : SMul ℂˣ PeriodPair := ⟨PeriodPair.smul⟩

@[simp] lemma smul_ω₁ (a : ℂˣ) (L : PeriodPair) : (a • L).ω₁ = a * L.ω₁ := rfl
@[simp] lemma smul_ω₂ (a : ℂˣ) (L : PeriodPair) : (a • L).ω₂ = a * L.ω₂ := rfl

/-- The complex-conjugate period pair: `L.conjugate` has periods `conj ω₁`, `conj ω₂`,
so its lattice is the conjugate of `L.lattice`. -/
def conjugate (L : PeriodPair) : PeriodPair where
  ω₁ := conj L.ω₁
  ω₂ := conj L.ω₂
  indep := by
    refine LinearIndependent.pair_iff.mpr fun s t hst =>
      LinearIndependent.pair_iff.mp L.indep s t ?_
    have h := congrArg (starRingEnd ℂ) hst
    simpa [Complex.real_smul] using h

@[simp] lemma conjugate_ω₁ (L : PeriodPair) : L.conjugate.ω₁ = conj L.ω₁ := rfl
@[simp] lemma conjugate_ω₂ (L : PeriodPair) : L.conjugate.ω₂ = conj L.ω₂ := rfl

variable (L : PeriodPair)

lemma mem_smul_lattice {a : ℂˣ} {x : ℂ} :
    x ∈ (a • L).lattice ↔ ∃ y ∈ L.lattice, x = (a : ℂ) * y := by
  simp only [mem_lattice, smul_ω₁, smul_ω₂]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨(m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂, ⟨m, n, rfl⟩, by ring⟩
  · rintro ⟨y, ⟨m, n, rfl⟩, rfl⟩
    exact ⟨m, n, by ring⟩

lemma mem_conjugate_lattice {x : ℂ} :
    x ∈ L.conjugate.lattice ↔ conj x ∈ L.lattice := by
  simp only [mem_lattice, conjugate_ω₁, conjugate_ω₂]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp⟩
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, by simpa using congrArg (starRingEnd ℂ) h⟩

/-- Multiplication by `a` as an equivalence from `L.lattice` to `(a • L).lattice`. -/
def smulLatticeEquiv (a : ℂˣ) : L.lattice ≃ (a • L).lattice where
  toFun l := ⟨a * l, L.mem_smul_lattice.mpr ⟨l, l.2, rfl⟩⟩
  invFun l' := ⟨(a : ℂ)⁻¹ * l', by
    obtain ⟨y, hy, hxy⟩ := L.mem_smul_lattice.mp l'.2
    rw [hxy, inv_mul_cancel_left₀ a.ne_zero]
    exact hy⟩
  left_inv l := Subtype.ext (inv_mul_cancel_left₀ a.ne_zero (l : ℂ))
  right_inv l' := Subtype.ext (mul_inv_cancel_left₀ a.ne_zero (l' : ℂ))

@[simp] lemma smulLatticeEquiv_apply_coe (a : ℂˣ) (l : L.lattice) :
    (L.smulLatticeEquiv a l : ℂ) = a * l := rfl

/-- Conjugation as an equivalence from `L.lattice` to `L.conjugate.lattice`. -/
def conjugateLatticeEquiv : L.lattice ≃ L.conjugate.lattice where
  toFun l := ⟨conj l, L.mem_conjugate_lattice.mpr (by simp [l.2])⟩
  invFun l' := ⟨conj l', L.mem_conjugate_lattice.mp l'.2⟩
  left_inv l := Subtype.ext (Complex.conj_conj (l : ℂ))
  right_inv l' := Subtype.ext (Complex.conj_conj (l' : ℂ))

/-! ### Behaviour of the Eisenstein sums `G n` -/

theorem G_smul (a : ℂˣ) (n : ℕ) : (a • L).G n = ((a : ℂ) ^ n)⁻¹ * L.G n := by
  simp only [G]
  rw [← (L.smulLatticeEquiv a).tsum_eq, ← tsum_mul_left]
  exact tsum_congr fun l => by
    rw [smulLatticeEquiv_apply_coe, mul_pow, mul_inv]

theorem G_conjugate (n : ℕ) : L.conjugate.G n = conj (L.G n) := by
  simp only [G]
  rw [Complex.conj_tsum, ← L.conjugateLatticeEquiv.tsum_eq]
  exact tsum_congr fun l => by
    rw [conjugateLatticeEquiv, map_inv₀, map_pow]
    ring_nf
    grind

/-- Eisenstein sums depend only on the lattice, not on the choice of periods. -/
theorem G_congr {L₁ L₂ : PeriodPair} (h : L₁.lattice = L₂.lattice) (n : ℕ) :
    L₁.G n = L₂.G n := by
  unfold G
  rw [h]

theorem g₂_congr {L₁ L₂ : PeriodPair} (h : L₁.lattice = L₂.lattice) : L₁.g₂ = L₂.g₂ := by
  unfold g₂
  rw [G_congr h]

theorem g₃_congr {L₁ L₂ : PeriodPair} (h : L₁.lattice = L₂.lattice) : L₁.g₃ = L₂.g₃ := by
  unfold g₃
  rw [G_congr h]

/-! ### Scaling and conjugation of `g₂`, `g₃` -/

theorem g₂_smul (a : ℂˣ) : (a • L).g₂ = ((a : ℂ) ^ 4)⁻¹ * L.g₂ := by
  simp only [g₂, G_smul]
  ring

theorem g₃_smul (a : ℂˣ) : (a • L).g₃ = ((a : ℂ) ^ 6)⁻¹ * L.g₃ := by
  simp only [g₃, G_smul]
  ring

theorem g₂_conjugate : L.conjugate.g₂ = conj L.g₂ := by
  simp only [g₂, G_conjugate, map_mul, map_ofNat]

theorem g₃_conjugate : L.conjugate.g₃ = conj L.g₃ := by
  simp only [g₃, G_conjugate, map_mul, map_ofNat]

/-! ### The discriminant and the `j`-invariant -/


-- these both exist elsewhere... and should be unified

/-- The discriminant `g₂³ - 27 g₃²` of a period lattice.
Classically this never vanishes; that fact is not yet in Mathlib, and is taken as a
hypothesis (`hΔ`) by the theorems below that need it. -/
def discriminant : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

/-- The `j`-invariant of a period lattice, `j = 1728 g₂³ / (g₂³ - 27 g₃²)`. -/
def j : ℂ := 1728 * L.g₂ ^ 3 / L.discriminant

theorem discriminant_smul (a : ℂˣ) :
    (a • L).discriminant = ((a : ℂ) ^ 12)⁻¹ * L.discriminant := by
  simp only [discriminant, g₂_smul, g₃_smul]
  ring

theorem discriminant_conjugate : L.conjugate.discriminant = conj L.discriminant := by
  simp only [discriminant, g₂_conjugate, g₃_conjugate, map_sub, map_mul, map_pow, map_ofNat]

theorem j_smul (a : ℂˣ) : (a • L).j = L.j := by
  have ha : ((a : ℂ) ^ 12)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ a.ne_zero)
  simp only [j, g₂_smul, discriminant_smul]
  rw [show 1728 * (((a : ℂ) ^ 4)⁻¹ * L.g₂) ^ 3
        = ((a : ℂ) ^ 12)⁻¹ * (1728 * L.g₂ ^ 3) by ring,
    mul_div_mul_left _ _ ha]

theorem j_conjugate : L.conjugate.j = conj L.j := by
  simp only [j, g₂_conjugate, discriminant_conjugate, map_div₀, map_mul, map_pow, map_ofNat]

theorem g₂_ne_zero_of_g₃_eq_zero (hΔ : L.discriminant ≠ 0) (h : L.g₃ = 0) : L.g₂ ≠ 0 :=
  fun h₂ => hΔ (by rw [discriminant, h, h₂]; ring)

theorem g₃_ne_zero_of_g₂_eq_zero (hΔ : L.discriminant ≠ 0) (h : L.g₂ = 0) : L.g₃ ≠ 0 :=
  fun h₃ => hΔ (by rw [discriminant, h, h₃]; ring)

theorem j_eq_1728_of_g₃_eq_zero (hΔ : L.discriminant ≠ 0) (h : L.g₃ = 0) : L.j = 1728 := by
  have hg₂ := L.g₂_ne_zero_of_g₃_eq_zero hΔ h
  rw [j, discriminant, h]
  rw [show (27 : ℂ) * 0 ^ 2 = 0 by ring, sub_zero, mul_div_assoc,
    div_self (pow_ne_zero 3 hg₂), mul_one]

theorem j_eq_zero_of_g₂_eq_zero (h : L.g₂ = 0) : L.j = 0 := by
  rw [j, h]
  simp

/-! ### Homotheties preserving the lattice -/

/-- The classical uniqueness theorem: a period lattice is determined by its invariants
`g₂`, `g₃`. Its formalization (via the Laurent expansion of `℘` and the recursion for the
`G`-sums induced by `℘'² = 4℘³ - g₂℘ - g₃`) is not yet in Mathlib, so results depending on it
take it as a hypothesis. -/
def InvariantsDetermineLattice : Prop :=
  ∀ L₁ L₂ : PeriodPair, L₁.g₂ = L₂.g₂ → L₁.g₃ = L₂.g₃ → L₁.lattice = L₂.lattice

theorem pow_four_eq_one_of_smul_lattice_eq {a : ℂˣ} (hg₂ : L.g₂ ≠ 0)
    (h : (a • L).lattice = L.lattice) : (a : ℂ) ^ 4 = 1 := by
  have e : ((a : ℂ) ^ 4)⁻¹ * L.g₂ = L.g₂ := by
    rw [← L.g₂_smul a]
    exact g₂_congr h
  have h1 := mul_right_cancel₀ hg₂ (e.trans (one_mul L.g₂).symm)
  rwa [inv_eq_one] at h1

theorem pow_six_eq_one_of_smul_lattice_eq {a : ℂˣ} (hg₃ : L.g₃ ≠ 0)
    (h : (a • L).lattice = L.lattice) : (a : ℂ) ^ 6 = 1 := by
  have e : ((a : ℂ) ^ 6)⁻¹ * L.g₃ = L.g₃ := by
    rw [← L.g₃_smul a]
    exact g₃_congr h
  have h1 := mul_right_cancel₀ hg₃ (e.trans (one_mul L.g₃).symm)
  rwa [inv_eq_one] at h1

/-- For a lattice with `g₂ ≠ 0` and `g₃ ≠ 0`, the only homotheties preserving it are `±1`. -/
theorem smul_lattice_eq_iff {a : ℂˣ} (hg₂ : L.g₂ ≠ 0) (hg₃ : L.g₃ ≠ 0) :
    (a • L).lattice = L.lattice ↔ (a : ℂ) = 1 ∨ (a : ℂ) = -1 := by
  constructor
  · intro h
    have h4 := L.pow_four_eq_one_of_smul_lattice_eq hg₂ h
    have h6 := L.pow_six_eq_one_of_smul_lattice_eq hg₃ h
    have h2 : (a : ℂ) ^ 2 = 1 := by
      have h42 : (a : ℂ) ^ 4 * (a : ℂ) ^ 2 = 1 := by
        rw [← pow_add]
        exact h6
      rwa [h4, one_mul] at h42
    have hfac : ((a : ℂ) - 1) * ((a : ℂ) + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact Or.inl (sub_eq_zero.mp h')
    · exact Or.inr (add_eq_zero_iff_eq_neg.mp h')
  · rintro (h | h)
    · ext x
      simp [mem_smul_lattice, h]
    · ext x
      rw [mem_smul_lattice, h]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [neg_one_mul] using neg_mem hy
      · intro hx
        exact ⟨-x, neg_mem hx, by ring⟩

/-- When `g₃ L = 0` (equivalently `j L = 1728`), the homotheties preserving the lattice are
exactly the fourth roots of unity. -/
theorem smul_lattice_eq_iff_of_g₃_eq_zero
    (hΔ : L.discriminant ≠ 0) {a : ℂˣ} (hg₃ : L.g₃ = 0) :
    (a • L).lattice = L.lattice ↔ (a : ℂ) ^ 4 = 1 := by
  refine ⟨L.pow_four_eq_one_of_smul_lattice_eq (L.g₂_ne_zero_of_g₃_eq_zero hΔ hg₃),
    fun h4 => ?_⟩
  refine invariantsDetermineLattice _ _ ?_ ?_
  · rw [L.g₂_smul a, h4, inv_one, one_mul]
  · rw [L.g₃_smul a, hg₃, mul_zero]

/-- When `g₂ L = 0` (equivalently `j L = 0`), the homotheties preserving the lattice are
exactly the sixth roots of unity. -/
theorem smul_lattice_eq_iff_of_g₂_eq_zero
    (hΔ : L.discriminant ≠ 0) {a : ℂˣ} (hg₂ : L.g₂ = 0) :
    (a • L).lattice = L.lattice ↔ (a : ℂ) ^ 6 = 1 := by
  refine ⟨L.pow_six_eq_one_of_smul_lattice_eq (L.g₃_ne_zero_of_g₂_eq_zero hΔ hg₂),
    fun h6 => ?_⟩
  refine invariantsDetermineLattice _ _ ?_ ?_
  · rw [L.g₂_smul a, hg₂, mul_zero]
  · rw [L.g₃_smul a, h6, inv_one, one_mul]

/-! ### Real lattices -/

/-- A period lattice is *real* if it is stable under complex conjugation. -/
def IsReal (L : PeriodPair) : Prop := L.conjugate.lattice = L.lattice

variable {L}

/-- The invariant `g₂` of a real lattice is fixed by conjugation (unconditional). -/
theorem IsReal.conj_g₂ (h : L.IsReal) : conj L.g₂ = L.g₂ := by
  rw [← L.g₂_conjugate]
  exact g₂_congr h

/-- The invariant `g₃` of a real lattice is fixed by conjugation (unconditional). -/
theorem IsReal.conj_g₃ (h : L.IsReal) : conj L.g₃ = L.g₃ := by
  rw [← L.g₃_conjugate]
  exact g₃_congr h

variable (L)

/-- A lattice is real iff its invariants are fixed by conjugation. The reverse direction
requires the classical uniqueness theorem, taken here as the hypothesis `huniq`. -/
theorem isReal_iff :
    L.IsReal ↔ conj L.g₂ = L.g₂ ∧ conj L.g₃ = L.g₃ := by
  refine ⟨fun h => ⟨h.conj_g₂, h.conj_g₃⟩, fun ⟨h₂, h₃⟩ => ?_⟩
  exact invariantsDetermineLattice _ _ (by rw [L.g₂_conjugate, h₂]) (by rw [L.g₃_conjugate, h₃])

/-- **A lattice is real iff `g₂` and `g₃` are real numbers.** -/
theorem isReal_iff_exists_real :
    L.IsReal ↔ (∃ r : ℝ, L.g₂ = r) ∧ ∃ r : ℝ, L.g₃ = r := by
  rw [L.isReal_iff, Complex.conj_eq_iff_real, Complex.conj_eq_iff_real]

end PeriodPair
