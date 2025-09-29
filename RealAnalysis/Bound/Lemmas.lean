import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Basic
import Mathlib.Order.Defs.PartialOrder
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
  : lub ≤ ub ↔ s.IsBoundedAbove ub := by
    constructor
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

theorem Set.subset_imp_Sup_le
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

theorem Set.Sup_unique
  {t} [PartialOrder t]
  (s : Set t) (lub₁ lub₂ : t) (h_lub₁ : s.Sup lub₁) (h_lub₂ : s.Sup lub₂)
  : lub₁ = lub₂ := by
    simp [Set.Sup] at *
    apply eq_of_le_of_ge
    · apply h_lub₁.right lub₂
      exact h_lub₂.left
    · apply h_lub₂.right lub₁
      exact h_lub₁.left

theorem Set.Inf_unique
  {t} [PartialOrder t]
  (s : Set t) (glb₁ glb₂ : t) (h_glb₁ : s.Inf glb₁) (h_glb₂ : s.Inf glb₂)
  : glb₁ = glb₂ := by
    simp [Set.Inf] at *
    apply eq_of_le_of_ge
    · apply h_glb₁.right glb₂
      exact h_glb₂.left
    · apply h_glb₂.right glb₁
      exact h_glb₁.left

theorem Set.Inf_le_Sup
  {t} [Preorder t]
  (s : Set t) (h_s_nonempty : s.Nonempty) (glb lub : t) (h_glb : s.Inf glb) (h_lub : s.Sup lub)
  : glb ≤ lub := by
    obtain ⟨x, h_x_in_s⟩ := h_s_nonempty
    have glb_le_x := by
      apply h_glb.left x
      assumption
    have x_le_lub := by
      apply h_lub.left x
      assumption
    apply le_trans glb_le_x
    assumption

theorem Set.Sup_alt
  {t} [LinearOrder t]
  (s : Set t) (lub : t)
  : s.Sup lub ↔ s.IsBoundedAbove lub ∧ ∀ x, x < lub → ∃ y, y ∈ s ∧ x < y := by
    constructor
    · intro h_lub
      constructor
      · exact h_lub.left
      · intros x h_x_lt_lub
        have not_s_bounded_by_x := s.lt_Sup x lub h_lub h_x_lt_lub
        simp [Set.IsBoundedAbove] at not_s_bounded_by_x
        assumption
    · intro ⟨h_lb, h₁⟩
      constructor
      · assumption
      · intros ub h_ub
        cases le_total lub ub with
        | inl =>
          assumption
        | inr ub_le_lub =>
          rw [le_iff_eq_or_lt] at *
          cases ub_le_lub with
          | inl ub_eq_lub =>
            left
            rw [ub_eq_lub]
          | inr ub_lt_lub =>
            obtain ⟨y, ⟨y_in_s, ub_lt_y⟩⟩ := h₁ ub ub_lt_lub
            have y_le_ub := h_ub y y_in_s
            have not_y_le_ub := LT.lt.not_ge ub_lt_y
            contradiction
