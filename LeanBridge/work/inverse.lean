import LeanBridge.work.addition

/-!
# Proposition 3.6(b), isomorphism part: inverting the uniformization map

`addition.lean` upgrades the uniformization map `φ : ℂ/Λ → E(ℂ)` to the group homomorphism
`PeriodPair.uniformizationHom`.  This file sets up its inverse, i.e. the remaining content of
Proposition 3.6(b): `φ` is an **isomorphism** `ℂ/Λ ≃+ E(ℂ)` (`PeriodPair.uniformizationEquiv`),
whose inverse `AddEquiv` is `PeriodPair.uniformizationEquiv.symm`.

## Structure of the proof

* **Injectivity is sorry-free**, and essentially free: `φ` is a group homomorphism (the addition
  theorem, proved in `addition.lean`/`addition_euler.lean`, is doing all the analytic work here),
  so injectivity reduces to triviality of the kernel — and by construction `φ` sends non-lattice
  points to *affine* points `(℘(z), ½℘'(z))`, never to the point at infinity `O`.  So
  `ker φ = Λ/Λ = 0` (`uniformization_injective`).

* **Surjectivity** reduces to a single analytic lemma, the only `sorry` in this file:

  > `exists_weierstrassP_eq`: `℘` attains every complex value at some `z ∉ Λ`.

  Classically: `℘ - c` is a nonconstant elliptic function; if it had no zero then `1/(℘ - c)`
  would be a lattice-periodic entire function, bounded on a period parallelogram hence bounded,
  hence constant by Liouville — contradiction.  Given this, surjectivity is sorry-free
  (`toPoint_surjective`): for an affine point `(x, y) ∈ E`, pick `z` with `℘(z) = x`; the curve
  equation forces `(½℘'(z))² = y²`, and replacing `z` by `-z` (`℘` even, `℘'` odd) fixes the sign.
-/

open Complex UpperHalfPlane EisensteinSeries ModularForm PeriodPair
open scoped UpperHalfPlane

noncomputable section

namespace PeriodPair

@[simp] lemma uniformizationHom_apply (L : PeriodPair) (q : ℂ ⧸ L.lattice.toAddSubgroup) :
    L.uniformizationHom q = L.uniformization q := rfl

/-! ### Injectivity (sorry-free) -/

/-- **Injectivity of `φ`.**  Since `φ` is a group homomorphism (the addition theorem), it
suffices that its kernel is trivial; and `φ(z) = O` forces `z ∈ Λ` by construction, because
non-lattice points map to affine points. -/
theorem uniformization_injective (L : PeriodPair) :
    Function.Injective L.uniformization := by
  have h := injective_iff_map_eq_zero L.uniformizationHom
  simp only [uniformizationHom_apply] at h
  rw [show L.uniformization = ⇑L.uniformizationHom from rfl] at h ⊢
  rw [h]
  intro q hq
  induction q using QuotientAddGroup.induction_on with
  | _ z =>
    rw [uniformizationHom_apply, uniformization_mk] at hq
    rw [QuotientAddGroup.eq_zero_iff, Submodule.mem_toAddSubgroup]
    by_contra hz
    rw [PeriodPair.toPoint, dif_neg hz] at hq
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ hq

/-! ### Surjectivity, reduced to `℘` attaining every value -/

/-- **The missing analytic input (the only `sorry`): `℘` attains every complex value.**

Proof sketch (Silverman VI.3.2 / Lang): if `℘ - c` had no zero off `Λ`, then `1/(℘ - c)` would
be holomorphic on all of `ℂ` (at lattice points `℘` has a pole, so `1/(℘ - c) → 0`), doubly
periodic, hence bounded (continuity on a closed period parallelogram), hence constant by
Liouville — contradicting nonconstancy of `℘`.  Available ingredients:
`differentiableOn_weierstrassP`, `weierstrassP_add_coe` (periodicity),
`not_continuousAt_weierstrassP` (the pole), and Liouville from Mathlib. -/
theorem exists_weierstrassP_eq (L : PeriodPair) (c : ℂ) :
    ∃ z : ℂ, z ∉ L.lattice ∧ ℘[L] z = c := by
  sorry

/-- **Surjectivity of the lift `toPoint : ℂ → E(ℂ)`**, given `exists_weierstrassP_eq`.  The point
at infinity is hit by `0 ∈ Λ`; an affine point `(x, y)` is hit by a `z` with `℘(z) = x`, up to
replacing `z` by `-z` to fix the sign of `½℘'(z) = ±y` (`toPoint_neg`). -/
theorem toPoint_surjective (L : PeriodPair) : Function.Surjective L.toPoint := by
  intro P
  cases P with
  | zero =>
    exact ⟨0, by simp only [PeriodPair.toPoint, dif_pos (zero_mem _)]; rfl⟩
  | some x y h =>
    obtain ⟨z, hz, hPz⟩ := L.exists_weierstrassP_eq x
    -- The curve equation at `(℘ z, ½℘' z)` and at `(x, y)` share the same right-hand side,
    -- so `(½℘' z)² = y²`.
    have hsq : ℘'[L] z / 2 = y ∨ ℘'[L] z / 2 = -y := by
      rw [← sq_eq_sq_iff_eq_or_eq_neg]
      have h1 := (WeierstrassCurve.Affine.equation_iff ..).mp (L.weierstrassCurve_equation hz)
      have h2 := (WeierstrassCurve.Affine.equation_iff ..).mp h.1
      simp only [PeriodPair.weierstrassCurve] at h1 h2
      rw [hPz] at h1
      linear_combination h1 - h2
    rcases hsq with hy | hy
    · -- `½℘'(z) = y`: `z` itself works.
      refine ⟨z, ?_⟩
      simp only [PeriodPair.toPoint, dif_neg hz]
      subst hPz hy
      rfl
    · -- `½℘'(z) = -y`: replace `z` by `-z`, using `℘(-z) = ℘(z)`, `℘'(-z) = -℘'(z)`.
      refine ⟨-z, ?_⟩
      rw [L.toPoint_neg]
      simp only [PeriodPair.toPoint, dif_neg hz, WeierstrassCurve.Affine.Point.neg_some]
      -- `congr 1` closes the `x`-coordinate goal `℘ z = x` from `hPz`; the `y`-coordinate remains.
      congr 1
      simp only [WeierstrassCurve.Affine.negY, PeriodPair.weierstrassCurve]
      rw [hy]
      ring

/-- **Surjectivity of `φ : ℂ/Λ → E(ℂ)`**, descended from `toPoint_surjective`. -/
theorem uniformization_surjective (L : PeriodPair) :
    Function.Surjective L.uniformization := fun P => by
  obtain ⟨z, hz⟩ := L.toPoint_surjective P
  exact ⟨QuotientAddGroup.mk z, hz⟩

/-! ### The isomorphism `ℂ/Λ ≃+ E(ℂ)` and its inverse -/

theorem uniformization_bijective (L : PeriodPair) :
    Function.Bijective L.uniformization :=
  ⟨L.uniformization_injective, L.uniformization_surjective⟩

/-- **Proposition 3.6(b), isomorphism form.**  The uniformization map `φ` as an additive group
isomorphism `ℂ/Λ ≃+ E(ℂ)`.  The inverse of `uniformizationHom` is `uniformizationEquiv.symm`. -/
def uniformizationEquiv (L : PeriodPair) :
    (ℂ ⧸ L.lattice.toAddSubgroup) ≃+ L.weierstrassCurve.toAffine.Point :=
  AddEquiv.ofBijective L.uniformizationHom L.uniformization_bijective

@[simp] lemma uniformizationEquiv_apply (L : PeriodPair) (q : ℂ ⧸ L.lattice.toAddSubgroup) :
    L.uniformizationEquiv q = L.uniformization q := rfl

@[simp] lemma uniformizationEquiv_symm_uniformization (L : PeriodPair)
    (q : ℂ ⧸ L.lattice.toAddSubgroup) :
    L.uniformizationEquiv.symm (L.uniformization q) = q :=
  L.uniformizationEquiv.symm_apply_apply q

@[simp] lemma uniformization_uniformizationEquiv_symm (L : PeriodPair)
    (P : L.weierstrassCurve.toAffine.Point) :
    L.uniformization (L.uniformizationEquiv.symm P) = P :=
  L.uniformizationEquiv.apply_symm_apply P

end PeriodPair
