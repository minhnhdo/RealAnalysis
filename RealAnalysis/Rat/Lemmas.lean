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

theorem Rat.lt_total {a b : ℚ} : a < b ∨ a = b ∨ b < a := by
  cases Rat.le_total with
  | inl h_le =>
    rw [le_iff_eq_or_lt] at h_le
    cases h_le with
    | inl =>
      right
      left
      assumption
    | inr =>
      left
      assumption
  | inr h_le =>
    rw [le_iff_eq_or_lt] at h_le
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

theorem Rat.neg_neg_iff_pos {q : ℚ} : -q < 0 ↔ 0 < q := by
  rw [← Rat.num_pos, ← Rat.num_neg, Rat.num_neg_eq_neg_num]
  apply Int.neg_neg_iff_pos

theorem Rat.neg_add_neg {p q : ℚ} : p < 0 → q < 0 → p + q < 0 := by
  intros
  rw [← add_zero 0]
  apply add_lt_add_of_lt_of_lt
  · assumption
  · assumption

theorem Rat.pos_add_pos {p q : ℚ} : 0 < p → 0 < q → 0 < p + q := by
  intros
  rw [← add_zero 0]
  apply add_lt_add_of_lt_of_lt
  · assumption
  · assumption

theorem Rat.mul_nonpos_nonneg {p q : ℚ} : p ≤ 0 → 0 ≤ q → p * q ≤ 0 := by
  intros
  rw [← Rat.zero_mul q]
  apply Rat.mul_le_mul_of_nonneg_right
  · assumption
  · assumption

theorem Rat.lt_zero_mul_lt_zero {p q : ℚ} : p < 0 → q < 0 → 0 < p * q := by
  intros
  rw [← Rat.neg_neg_iff_pos, ← Rat.neg_mul, ← Rat.mul_zero (-p), Rat.mul_lt_mul_left]
  · assumption
  · rw [neg_pos]
    assumption

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

theorem Rat.abs_eq_neg {q : ℚ} : q.abs = -q ↔ q ≤ 0 := by
  constructor
  · by_cases h : 0 ≤ q
    · simp [Rat.abs, h]
      intro h'
      symm at h'
      rw [Rat.neg_eq_self] at h'
      rw [le_iff_eq_or_lt]
      left
      assumption
    · simp [Rat.abs, h]
      rw [Rat.not_le] at h
      rw [le_iff_lt_or_eq]
      left
      assumption
  · intro h
    rw [le_iff_eq_or_lt] at h
    cases h with
    | inl =>
      simp [Rat.abs, *]
    | inr h_neg =>
      rw [← Rat.not_le] at h_neg
      simp [Rat.abs, h_neg]

theorem Rat.le_abs {q : ℚ} : q ≤ q.abs := by
  cases @Rat.lt_total q 0 with
  | inl =>
    have : ¬0 ≤ q := by
      rw [not_le]
      assumption
    simp [Rat.abs, *]
    apply le_of_lt
    assumption
  | inr h_q_le_zero =>
    cases h_q_le_zero with
    | inl =>
      simp [Rat.abs, *]
    | inr =>
      have : 0 ≤ q := by
        apply le_of_lt
        assumption
      simp [Rat.abs, *]

theorem Rat.abs_zero : Rat.abs 0 = 0 := by simp [Rat.abs]

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

theorem Rat.abs_ne_zero {q : ℚ} : q.abs ≠ 0 ↔ q ≠ 0 := by
  constructor
  · intro
    by_cases q = 0
    · simp [*, Rat.abs_zero] at *
    · assumption
  · intro
    by_cases 0 ≤ q
    · simp [Rat.abs, *]
    · simp [Rat.abs, *]

theorem Rat.abs_pos {q : ℚ} : 0 < q.abs ↔ q ≠ 0 := by
  constructor
  · by_cases h : 0 ≤ q
    · simp [Rat.abs, *]
      intro h_pos
      obtain ⟨_, ne_zero⟩ := lt_iff_le_and_ne.mp h_pos
      symm at ne_zero
      assumption
    · simp [Rat.abs, *]
      intro h_neg
      obtain ⟨_, ne_zero⟩ := lt_iff_le_and_ne.mp h_neg
      assumption
  · intro h
    rw [← lt_or_lt_iff_ne] at h
    cases h with
    | inl h_neg =>
      rw [← not_le] at h_neg
      simp [Rat.abs, h_neg]
      rw [not_le] at h_neg
      assumption
    | inr h_pos =>
      have := h_pos
      apply le_of_lt at h_pos
      simp [Rat.abs, h_pos]
      assumption

theorem Rat.abs_nonpos {q : ℚ} : q.abs ≤ 0 ↔ q = 0 := by
  constructor
  · intro
    rw [← Rat.abs_eq_zero]
    apply le_antisymm
    · assumption
    · exact Rat.abs_nonneg
  · intro
    simp [Rat.abs, *]

theorem Rat.abs_add {p q : ℚ} : (p + q).abs ≤ p.abs + q.abs := by
  by_cases hpq : 0 ≤ p + q
  · rw [Rat.abs]
    simp [hpq]
    apply add_le_add
    · apply Rat.le_abs
    · apply Rat.le_abs
  · by_cases hp : 0 ≤ p
    · have hq : q.abs = -q := by
        rw [Rat.abs_eq_neg]
        apply (add_le_add_iff_right q).mpr at hp
        rw [Rat.zero_add] at hp
        apply le_trans hp
        apply le_of_lt
        rw [← not_le]
        assumption
      rw [hq]
      simp [Rat.abs, *]
    · by_cases 0 ≤ q
      · simp [Rat.abs, *]
      · simp [Rat.abs, *]

theorem Rat.abs_mul {p q : ℚ} : (p * q).abs = p.abs * q.abs := by
  by_cases hpq : 0 ≤ p * q
  · rw [Rat.abs]
    simp [hpq]
    rw [mul_nonneg_iff] at hpq
    cases hpq with
    | inl =>
      simp [Rat.abs, *]
    | inr h =>
      obtain ⟨hp, hq⟩ := h
      rw [le_iff_eq_or_lt] at hp
      cases hp with
      | inl =>
        simp [Rat.abs, *]
      | inr =>
        rw [le_iff_eq_or_lt] at hq
        cases hq with
        | inl =>
          simp [Rat.abs, *]
        | inr =>
          rw [← not_le] at *
          simp [Rat.abs, *]
  · rw [Rat.abs]
    simp [hpq]
    rw [not_le, mul_neg_iff] at hpq
    cases hpq with
    | inl h =>
      obtain ⟨hp, hq⟩ := h
      apply le_of_lt at hp
      rw [← not_le] at hq
      simp [Rat.abs, *]
    | inr h =>
      obtain ⟨hp, hq⟩ := h
      rw [← not_le] at hp
      apply le_of_lt at hq
      simp [Rat.abs, *]

instance : IsAbsoluteValue Rat.abs :=
  ⟨@Rat.abs_nonneg, @Rat.abs_eq_zero, @Rat.abs_add, @Rat.abs_mul⟩

theorem Rat.abs_neg {q : ℚ} : (-q).abs = q.abs := by
  by_cases h : 0 ≤ q
  · simp [Rat.abs, h]
    intro h'
    have := le_antisymm h' h
    simp [*]
  · simp [Rat.abs, h]
    rw [not_le] at h
    intro h'
    have := lt_trans h' h
    have := lt_irrefl 0
    contradiction
