import Mathlib

open PeriodPair

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (L : PeriodPair)


noncomputable abbrev WeierstrassP_cubic : Cubic ℂ :=
  ⟨4, 0, - L.g₂, - L.g₃⟩

lemma WeierstrassP_cubic_ne_zero : (WeierstrassP_cubic L).toPoly ≠ 0 :=
  Cubic.ne_zero_of_a_ne_zero (by norm_num)

abbrev ω₃ := L.ω₁ + L.2

lemma foo'' (a : L.lattice) : ℘'[L] (a / 2) = ℘'[L] (-(a/ 2)) := by
  simp_rw [show - (a / 2) = (a : ℂ) / 2 - a by ring, L.derivWeierstrassP_sub_coe ((a : ℂ) / 2) a]

lemma foo (a : L.lattice) : ℘'[L] (a / 2) = 0 :=
  CharZero.eq_neg_self_iff.mp (by simpa [derivWeierstrassP_neg] using foo'' L a)
