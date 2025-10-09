import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Rat
import RealAnalysis.Rat.Lemmas
import RealAnalysis.Real.CauchySequence.Basic

theorem cauchy₂
  {f : ℕ → ℚ} (h_causeq : IsCauchySequence f) {ε : ℚ} (hε : 0 < ε)
  : ∃ i, ∀ j ≥ i, ∀ k ≥ i, (f j - f k).abs < ε := by
    obtain ⟨i, h⟩ := h_causeq (ε / 2) (half_pos hε)
    use i
    intros j hj k hk
    have hjε := h j hj
    have := h k hk
    rw [Rat.abs_sub] at hjε
    apply lt_of_le_of_lt (@Rat.abs_sub_le (f j) (f i) (f k))
    rw [← add_halves ε]
    apply add_lt_add_of_lt_of_lt
    · assumption
    · assumption
