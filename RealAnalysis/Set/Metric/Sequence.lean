import RealAnalysis.Set.Metric

universe u

variable {t : Type u} [MetricSpace t]

def Function.ConvergesTo (f : ℕ → t) (p : t) : Prop := ∀ e > 0, ∃ n, ∀ n' ≥ n, dist (f n') p < e

theorem unique_convergence (f : ℕ → t) (p p' : t)
  : f.ConvergesTo p → f.ConvergesTo p' → p = p' := by
    intro hp hp'
    by_cases h_dist : dist p p' > 0
    · obtain ⟨n, hn⟩ := hp (dist p p' / 2) (half_pos h_dist)
      obtain ⟨n', hn'⟩ := hp' (dist p p' / 2) (half_pos h_dist)
      have dist_p := hn (max n n') (le_max_left n n')
      have dist_p' := hn' (max n n') (le_max_right n n')
      have := calc dist (f (max n n')) p + dist (f (max n n')) p'
        _ < dist p p' / 2 + dist p p' / 2 := add_lt_add dist_p dist_p'
        _ = dist p p' := add_halves (dist p p')
      have : ¬dist (f (max n n')) p + dist (f (max n n')) p' < dist p p' := by
        rw [not_lt, MetricSpace.dist_comm (f (max n n'))]
        exact dist_triangle
      contradiction
    · rw [not_lt, le_iff_eq_or_lt] at h_dist
      cases h_dist with
      | inl =>
        rw [← dist_eq_zero]
        assumption
      | inr =>
        have : ¬dist p p' < 0 := by
          rw [not_lt]
          exact dist_nonneg
        contradiction
