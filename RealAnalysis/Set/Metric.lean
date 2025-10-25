import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel

universe u

@[ext]
class Dist (t : Type u) where
  dist : t → t → ℝ

export Dist (dist)

class MetricSpace (t : Type u) extends Dist t where
  dist_nonneg (p q : t) : 0 ≤ dist p q
  dist_eq_zero (p q : t) : dist p q = 0 ↔ p = q
  dist_comm (p q : t) : dist p q = dist q p
  dist_triangle (p q r : t) : dist p r ≤ dist p q + dist q r

instance : MetricSpace ℝ where
  dist p q := |p - q|
  dist_nonneg p q := by simp
  dist_eq_zero p q := by
    simp
    constructor
    · exact eq_of_sub_eq_zero
    · intro h
      rw [h]
      simp
  dist_comm p q := abs_sub_comm p q
  dist_triangle p q r := abs_sub_le p q r

variable {t : Type u} [MetricSpace t]

theorem dist_nonneg {p q : t} : 0 ≤ dist p q := MetricSpace.dist_nonneg p q

@[simp]
theorem dist_eq_zero {p q : t} : dist p q = 0 ↔ p = q := MetricSpace.dist_eq_zero p q

theorem dist_self {p : t} : dist p p = 0 := by simp

theorem dist_comm {p q : t} : dist p q = dist q p := MetricSpace.dist_comm p q

theorem dist_triangle {p q r : t} : dist p r ≤ dist p q + dist q r :=
  MetricSpace.dist_triangle p q r

def ball (x : t) (r : ℝ) : Set t := { y : t | dist x y < r }

@[simp]
alias openBall := ball

def closedBall (x : t) (r : ℝ) : Set t := { y : t | dist x y ≤ r }

theorem mem_closedBall_self {p : t} {r : ℝ} (h : r ≥ 0) : p ∈ closedBall p r := by
  have : dist p p = 0 := by rw [dist_eq_zero]
  simp [closedBall, *]

theorem nonneg_of_mem_closedBall {p q : t} {r : ℝ} (h : q ∈ closedBall p r) : 0 ≤ r :=
  le_trans dist_nonneg h

theorem nonempty_closedBall {p : t} {r : ℝ} : (closedBall p r).Nonempty ↔ 0 ≤ r := by
  constructor
  · intro h
    obtain ⟨_, h_mem⟩ := h
    apply nonneg_of_mem_closedBall h_mem
  · intro h
    use p
    apply mem_closedBall_self
    assumption

theorem closedBall_empty {r : ℝ} {p : t} : closedBall p r = ∅ ↔ r < 0 := by
  rw [← Set.not_nonempty_iff_eq_empty, nonempty_closedBall, not_le]

def AdherentPoint (p : t) (s : Set t) := ∀ r > 0, ∃ q ∈ ball p r, q ∈ s

def LimitPoint (p : t) (s : Set t) := ∀ r > 0, ∃ q ∈ ball p r, q ≠ p ∧ q ∈ s

theorem AdherentPoint_of_LimitPoint {p : t} {s : Set t} : LimitPoint p s → AdherentPoint p s := by
  intro h r hr
  obtain ⟨q, _, _, _⟩ := h r hr
  use q

def IsolatedPoint (p : t) (s : Set t) := p ∈ s ∧ ¬LimitPoint p s

def InteriorPoint (p : t) (s : Set t) := p ∈ s ∧ ∃ r > 0, ball p r ⊆ s

def Set.IsOpen (s : Set t) : Prop := ∀ p ∈ s, InteriorPoint p s

theorem empty_isOpen : (∅ : Set t).IsOpen := by simp [Set.IsOpen]

theorem univ_isOpen : (Set.univ : Set t).IsOpen := by
  intro p h
  constructor
  · assumption
  · use 1
    simp

theorem ball_isOpen {a : t} {r : ℝ} : (ball a r).IsOpen := by
  simp [Set.IsOpen, ball, InteriorPoint]
  intros b hab
  constructor
  · assumption
  · use r - dist a b
    constructor
    · rw [sub_pos]
      assumption
    · intro c hbc
      rw [lt_sub_iff_add_lt, add_comm] at hbc
      calc dist a c
        _ ≤ dist a b + dist b c := dist_triangle
        _ < r := hbc

def Set.IsClosed (s : Set t) : Prop := ∀ p, LimitPoint p s → p ∈ s

theorem empty_isClosed : (∅ : Set t).IsClosed := by
  intro p h
  obtain ⟨q, _, _, mem_empty⟩:= h 1 one_pos
  rw [Set.mem_empty_iff_false] at mem_empty
  contradiction

theorem univ_isClosed : (Set.univ : Set t).IsClosed := by simp [Set.IsClosed]

theorem closedBall_isClosed {a : t} {r : ℝ} : (closedBall a r).IsClosed := by
  intro b h
  by_cases hr : dist a b ≤ r
  · assumption
  · rw [not_le, ← sub_pos] at hr
    obtain ⟨c, _, _, _⟩ := h (dist a b - r) hr
    have prf₁ := calc dist a c ≤ r := by assumption
      _ < dist a b - dist b c := by
        rw [lt_sub_comm]
        assumption
    rw [lt_sub_iff_add_lt, ← not_le] at prf₁
    absurd prf₁
    rw [MetricSpace.dist_comm b c]
    exact dist_triangle

def Set.IsClopen (s : Set t) : Prop := s.IsOpen ∧ s.IsClosed

theorem empty_isClopen : (∅ : Set t).IsClopen := ⟨empty_isOpen, empty_isClosed⟩

theorem univ_isClopen : (Set.univ : Set t).IsClopen := ⟨univ_isOpen, univ_isClosed⟩

def Set.closure (s : Set t) : Set t := s ∪ {p | LimitPoint p s}

theorem Set.subset_closure {s : Set t} : s ⊆ s.closure := by
  intro _ _
  left
  assumption

theorem AdherentPoint_of_AdherentPoint_of_closure {p : t} {s : Set t}
  : AdherentPoint p s.closure → AdherentPoint p s := by
    intro h r hr
    obtain ⟨a, a_in_ball, a_in_closure⟩ := h r hr
    cases a_in_closure with
    | inl =>
      use a
    | inr a_is_limit_point =>
      obtain ⟨_, b, hb, ball'_subset_ball⟩ := ball_isOpen a a_in_ball
      obtain ⟨c, c_in_ball', _, _⟩ := a_is_limit_point b hb
      have := Set.mem_of_mem_of_subset c_in_ball' ball'_subset_ball
      use c

theorem AdherentPoint_of_LimitPoint_of_closure {p : t} {s : Set t}
  : LimitPoint p s.closure → AdherentPoint p s :=
    AdherentPoint_of_AdherentPoint_of_closure ∘ AdherentPoint_of_LimitPoint

theorem AdherentPoint_of_closure_of_AdherentPoint {p : t} {s : Set t}
  : AdherentPoint p s → AdherentPoint p s.closure := by
    intro h r hr
    obtain ⟨a, _, _⟩ := h r hr
    simp [Set.closure, Set.mem_union]
    use a
    constructor
    · assumption
    · left
      assumption

theorem AdherentPoint_of_closure_iff_AdherentPoint {p : t} {s : Set t}
  : AdherentPoint p s.closure ↔ AdherentPoint p s :=
    Iff.intro AdherentPoint_of_AdherentPoint_of_closure AdherentPoint_of_closure_of_AdherentPoint

theorem mem_closure_of_AdherentPoint {p : t} {s : Set t} : AdherentPoint p s → p ∈ s.closure := by
  intro h
  by_cases p ∈ s
  · left
    assumption
  · right
    intro r hr
    obtain ⟨q, _, q_in_s⟩ := h r hr
    have : q ≠ p := by
      apply ne_of_mem_of_not_mem q_in_s
      assumption
    use q

theorem AdherentPoint_of_mem_closure {p : t} {s : Set t} : p ∈ s.closure → AdherentPoint p s := by
  intro h
  cases h with
  | inl =>
    intro r _
    have : p ∈ ball p r := by
      simp [ball, dist_self]
      assumption
    use p
  | inr =>
    apply AdherentPoint_of_LimitPoint
    assumption

theorem points_of_closure {s : Set t} : {p | AdherentPoint p s} = s.closure := by
  apply subset_antisymm
  · intro
    exact mem_closure_of_AdherentPoint
  · intro
    exact AdherentPoint_of_mem_closure

theorem Set.closure_isClosed {s : Set t} : s.closure.IsClosed := by
  intro _ _
  apply mem_closure_of_AdherentPoint
  apply AdherentPoint_of_LimitPoint_of_closure
  assumption

theorem Set.IsClosed_iff {s : Set t} : s.IsClosed ↔ s = s.closure := by
  constructor
  · intro h
    apply subset_antisymm
    · exact Set.subset_closure
    · intro p h
      cases h with
      | inl =>
        assumption
      | inr h_limit_point =>
        exact h p h_limit_point
  · intro h
    rw [h]
    exact Set.closure_isClosed
