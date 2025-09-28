import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Basic
import RealAnalysis.Bound.Basic

theorem Set.IsBoundedAbove_trans
  {t} [Preorder t]
  (s : Set t) (ub₁ ub₂ : t)
  (h_ub₁ : s.IsBoundedAbove ub₁)
  (h_ub₁_le_ub₂ : ub₁ ≤ ub₂)
  : s.IsBoundedAbove ub₂ := by
    simp [Set.IsBoundedAbove] at *
    intros x h_x_in_s
    have h_x_le_ub₁ := h_ub₁ x h_x_in_s
    apply le_trans h_x_le_ub₁
    assumption

theorem Set.Sup_le_ub_iff
  {t} [Preorder t]
  (s : Set t) (lub ub : t)
  (h_lub : s.Sup lub)
  :  lub ≤ ub ↔ s.IsBoundedAbove ub := by
    apply Iff.intro
    · exact s.IsBoundedAbove_trans lub ub h_lub.left
    · intro h_ub
      simp [Set.Sup] at *
      exact h_lub.right ub h_ub

theorem Set.Sup_le_bound_iff
  {t} [Preorder t]
  (s : Set t) (lub b : t) (h_lub : s.Sup lub)
  : (∀ x, x ∈ s → x ≤ b) ↔ lub ≤ b := by
    simp [Set.Sup] at *
    apply Iff.intro
    · intro h_b
      apply h_lub.right
      assumption
    · intros h_lub_le_b
      apply s.IsBoundedAbove_trans lub b
      · exact h_lub.left
      · assumption

theorem Set.lt_IsBoundedAbove
  {t} [Preorder t]
  (s : Set t) (b : t)
  : (∀ x, x ∈ s → x < b) → s.IsBoundedAbove b := by
    intros h_lt x h_x_in_s
    apply le_of_lt
    exact h_lt x h_x_in_s

theorem Set.lt_Sup_le
  {t} [Preorder t]
  (s : Set t) (lub b : t) (h_lub : s.Sup lub)
  : (∀ x, x ∈ s → x < b) → lub ≤ b := by
    intro h_lt
    apply h_lub.right
    exact s.lt_IsBoundedAbove b h_lt

theorem Set.lt_Sup
  {t} [Preorder t]
  (s : Set t) (b lub : t) (h_lub : s.Sup lub) (h_lt : b < lub)
  : ¬s.IsBoundedAbove b := by
    intro h_ub
    have h_lub_le_b := h_lub.right b h_ub
    have h_not_lub_le_b := LT.lt.not_ge h_lt
    contradiction

theorem Set.s_imp_Sup_le
  {t} [Preorder t]
  (s₁ s₂ : Set t) (lub₁ lub₂ : t)
  (h_lub₁ : s₁.Sup lub₁) (h_lub₂ : s₂.Sup lub₂) (h_subset : s₁ ⊆ s₂)
  : lub₁ ≤ lub₂ := by
    simp [Set.Sup] at *
    have s₁_bounded_by_lub₂ : s₁.IsBoundedAbove lub₂ := by
      intro _ h_x_in_s₁
      apply h_lub₂.left
      apply h_subset
      assumption
    exact h_lub₁.right lub₂ s₁_bounded_by_lub₂
