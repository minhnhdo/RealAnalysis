import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Rat.Init
import RealAnalysis.Rat.Defs

theorem Rat.abs_nonneg {q : ℚ} : 0 ≤ q.abs := by
  simp [Rat.abs]
  cases @Rat.le_total 0 q with
  | inl =>
    simp [*]
  | inr q_le_zero =>
    rw [le_iff_eq_or_lt] at q_le_zero
    cases q_le_zero with
    | inl =>
      simp [*]
    | inr q_lt_zero =>
      have not_zero_le_q : ¬0 ≤ q := by
        rw [← lt_iff_not_ge]
        assumption
      simp [*]
      rw [le_iff_eq_or_lt]
      right
      assumption

theorem Rat.abs_eq_zero {q : ℚ} : q.abs = 0 ↔ q = 0 := by
  simp [Rat.abs]
  constructor
  · intro h_abs_eq_zero
    by_cases h : 0 ≤ q
    · simp [h] at h_abs_eq_zero
      assumption
    · simp [h] at h_abs_eq_zero
      assumption
  · intro
    simp [*]
