import Mathlib.Data.Int.Basic
import Mathlib.Tactic

theorem Int.lt_total {a b : ℤ} : a < b ∨ a = b ∨ b < a := by
  cases Int.le_total a b with
  | inl h_le =>
    rw [Int.le_iff_eq_or_lt] at h_le
    cases h_le with
    | inl =>
      right
      left
      assumption
    | inr =>
      left
      assumption
  | inr h_le =>
    rw [Int.le_iff_eq_or_lt] at h_le
    cases h_le with
    | inl h_eq =>
      symm at h_eq
      right
      left
      assumption
    | inr =>
      right
      right
      assumption

theorem Int.neg_eq_self {a : ℤ} : -a = a ↔ a = 0 := by
  constructor
  · intro h
    have h' := calc 0
      _ = a + a := by
        rw [← Int.add_left_neg a, Int.add_left_inj a]
        assumption
      _ = a * 2 := by
        rw [← Int.add_right_inj (-a), ← Int.add_assoc, Int.add_left_neg]
        rw [Int.zero_add, Int.add_comm, Int.add_neg_eq_sub]
        nth_rw 3 [← Int.mul_one a]
        rw [← Int.mul_sub a]
        simp
    symm at h'
    rw [Int.mul_eq_zero] at h'
    simp at h'
    assumption
  · intro
    simp [*]
