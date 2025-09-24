import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Order.Defs.LinearOrder
import RealAnalysis.Bound.Basic

class AxiomaticReal (t : Type _) extends Field t, LinearOrder t where
  add_preservation : ∀ x y z : t, x ≤ y → x + z ≤ y + z
  mul_preservation : ∀ x y : t, 0 ≤ x ∧ 0 ≤ y → 0 ≤ x * y
  completeness : ∀ (s : Set t) (ub : t), s.Nonempty ∧ s.BoundedAbove ub → ∃ lub, s.Sup lub

class TarskiReal (t : Type _) extends LT t, Add t where
  lt_asymm : ∀ x y : t, x < y → ¬y < x
  is_dense : ∀ x z : t, x < z → ∃ y, x < y ∧ y < z
  is_dedekind_complete : ∀ (X Y : Set t) (x y : t), x ∈ X ∧ y ∈ Y ∧ x < y →
    ∃ z, z ≠ x ∧ z ≠ y → x < z ∧ y < z
  add_assoc : ∀ x y z : t, x + (y + z) = (x + y) + z
  add_left : ∀ x y : t, ∃ z : t, x + z = y
  add_lt : ∀ x y z w : t, x + y < z + w → x < z ∨ y < w
  one : t
  one_lt_add : one < one + one
