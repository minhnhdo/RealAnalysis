import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Init
import RealAnalysis.Int.Lemmas
import RealAnalysis.Rat.Defs

theorem Rat.neg_eq_zero {q : ℚ} : -q = 0 ↔ q = 0 := by
  repeat rw [Rat.eq_iff_mul_eq_mul]
  rw [Rat.neg_den, Rat.neg_num, Rat.num_zero, Rat.den_zero]
  rw [Int.zero_mul, Int.ofNat_one]
  repeat rw [Int.mul_one]
  apply Int.neg_eq_zero


theorem Rat.neg_eq_self {q : ℚ} : -q = q ↔ q = 0 := by
  repeat rw [Rat.eq_iff_mul_eq_mul]
  rw [Rat.neg_den, Rat.neg_num, Rat.num_zero, Rat.den_zero]
  rw [Int.zero_mul, Int.ofNat_one, Int.mul_one, Int.mul_eq_mul_right_iff]
  · apply Int.neg_eq_self
  · simp

theorem Rat.mul_nonpos_nonneg {p q : ℚ} : p ≤ 0 → 0 ≤ q → p * q ≤ 0 := by
  intros
  rw [← Rat.zero_mul q]
  apply Rat.mul_le_mul_of_nonneg_right
  · assumption
  · assumption

theorem Rat.abs_eq_self {q : ℚ} : q.abs = q ↔ 0 ≤ q := by
  constructor
  · intro h_abs_eq_self
    by_cases h : 0 ≤ q
    · simp [h]
    · rw [Rat.not_le] at h
      simp [Rat.abs, h] at h_abs_eq_self
      rw [le_iff_eq_or_lt]
      left
      rw [Rat.neg_eq_self] at h_abs_eq_self
      rw [h_abs_eq_self]
  · intro h
    simp [Rat.abs, h]

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
