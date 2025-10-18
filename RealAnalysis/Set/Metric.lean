import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel

theorem add_self_eq_twice_self {a : ℝ} : a + a = 2 * a := by
  abel_nf
  simp

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

theorem dist_comm {p q : t} : dist p q = dist q p := MetricSpace.dist_comm p q

theorem dist_triangle {p q r : t} : dist p r ≤ dist p q + dist q r :=
  MetricSpace.dist_triangle p q r

def openBall (x : t) (r : ℝ) : Set t := { y : t | dist x y < r }

@[simp]
alias ball := openBall

def closedBall (x : t) (r : ℝ) : Set t := { y : t | dist x y ≤ r }

def AdherentPoint (p : t) (s : Set t) := ∀ r, ∃ q ∈ ball p r, q ∈ s

def LimitPoint (p : t) (s : Set t) := ∀ r, ∃ q ∈ ball p r, q ≠ p ∧ q ∈ s

theorem AdherentPoint_of_LimitPoint {p : t} {s : Set t} : LimitPoint p s → AdherentPoint p s := by
  intro h r
  obtain ⟨q, _, _, _⟩ := h r
  use q

def IsolatedPoint (p : t) (s : Set t) := p ∈ s ∧ ¬LimitPoint p s

def InteriorPoint (p : t) (s : Set t) := p ∈ s ∧ ∃ r, ball p r ⊆ s

theorem pos_of_mem_ball {r : ℝ} {p q : t} (h : q ∈ ball p r) : 0 < r :=
  lt_of_le_of_lt dist_nonneg h

theorem nonneg_of_mem_closedBall {r : ℝ} {p q : t} (h : q ∈ closedBall p r) : 0 ≤ r :=
  le_trans dist_nonneg h

def Set.IsOpen (s : Set t) : Prop := ∀ p ∈ s, InteriorPoint p s

theorem empty_isOpen : (∅ : Set t).IsOpen := by simp [Set.IsOpen]

theorem univ_isOpen : (Set.univ : Set t).IsOpen := by simp [Set.IsOpen, InteriorPoint]

theorem ball_isOpen {a : t} {r : ℝ} : (ball a r).IsOpen := by
  simp [Set.IsOpen, openBall, InteriorPoint]
  intros b hab
  constructor
  · assumption
  · use r - dist a b
    intro c hbc
    rw [lt_sub_iff_add_lt, add_comm] at hbc
    calc dist a c
      _ ≤ dist a b + dist b c := dist_triangle
      _ < r := hbc

def Set.IsClosed (s : Set t) : Prop := ∀ p, LimitPoint p s → p ∈ s

theorem empty_isClosed : (∅ : Set t).IsClosed := by simp [Set.IsClosed, LimitPoint]

theorem univ_isClosed : (Set.univ : Set t).IsClosed := by simp [Set.IsClosed]

theorem closedBall_isClosed {a : t} {r : ℝ} : (closedBall a r).IsClosed := by
  simp [Set.IsClosed, LimitPoint, closedBall, openBall]
  intro b hb
  obtain ⟨c, ⟨_, _, _⟩⟩ := hb (r - dist a b)
  have h := calc dist a b
    _ ≤ dist a c + dist c b := dist_triangle
    _ ≤ dist a c + dist b c := by nth_rw 2 [dist_comm]
    _ ≤ r + (r - dist a b) := by
      apply le_of_lt
      apply add_lt_add_of_le_of_lt
      · assumption
      · assumption
  rw [add_sub, le_sub_iff_add_le] at h
  repeat rw [add_self_eq_twice_self] at h
  apply le_of_mul_le_mul_left at h
  apply h
  exact two_pos

def Set.IsClopen (s : Set t) : Prop := s.IsOpen ∧ s.IsClosed

theorem empty_isClopen : (∅ : Set t).IsClopen := ⟨empty_isOpen, empty_isClosed⟩

theorem univ_isClopen : (Set.univ : Set t).IsClopen := ⟨univ_isOpen, univ_isClosed⟩

def Set.closure (s : Set t) : Set t := s ∪ {p | LimitPoint p s}

theorem AdherentPoint_of_AdherentPoint_of_closure {p : t} {s : Set t}
  : AdherentPoint p s.closure → AdherentPoint p s := by
    intro h r
    obtain ⟨a, a_in_ball, a_in_closure⟩ := h r
    cases a_in_closure with
    | inl =>
      use a
    | inr a_is_limit_point =>
      obtain ⟨_, b, ball'_subset_ball⟩ := ball_isOpen a a_in_ball
      obtain ⟨c, c_in_ball', _, _⟩ := a_is_limit_point b
      have := Set.mem_of_mem_of_subset c_in_ball' ball'_subset_ball
      use c

theorem AdherentPoint_of_LimitPoint_of_closure {p : t} {s : Set t}
  : LimitPoint p s.closure → AdherentPoint p s :=
    AdherentPoint_of_AdherentPoint_of_closure ∘ AdherentPoint_of_LimitPoint

theorem AdherentPoint_of_closure_of_AdherentPoint {p : t} {s : Set t}
  : AdherentPoint p s → AdherentPoint p s.closure := by
    intro h r
    obtain ⟨a, _, _⟩ := h r
    simp [Set.closure, Set.mem_union]
    use a
    constructor
    · assumption
    · left
      assumption

theorem AdherentPoint_of_closure_iff_AdherentPoint {p : t} {s : Set t}
  : AdherentPoint p s.closure ↔ AdherentPoint p s :=
    Iff.intro AdherentPoint_of_AdherentPoint_of_closure AdherentPoint_of_closure_of_AdherentPoint
