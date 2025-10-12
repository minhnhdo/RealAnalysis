import Mathlib.Data.Real.Basic

universe u

@[ext]
class Dist (t : Type u) where
  dist : t → t → ℝ

export Dist (dist)

class MetricSpace (t : Type u) extends Dist t where
  dist_nonneg (p q : t) : 0 ≤ dist p q
  dist_eq_zero (p q : t) : dist p q = 0 ↔ p = q
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
  dist_triangle p q r := abs_sub_le p q r

variable {t : Type u} [MetricSpace t]

theorem dist_nonneg {p q : t} : 0 ≤ dist p q := MetricSpace.dist_nonneg p q

@[simp]
theorem dist_eq_zero {p q : t} : dist p q = 0 ↔ p = q := MetricSpace.dist_eq_zero p q

theorem dist_triangle {p q r : t} : dist p r ≤ dist p q + dist q r :=
  MetricSpace.dist_triangle p q r

def openBall (x : t) (r : ℝ) : Set t := { y : t | dist x y < r }

@[simp]
alias ball := openBall

def closedBall (x : t) (r : ℝ) : Set t := { y : t | dist x y ≤ r }

def IsLimitPoint (p : t) (s : Set t) := ∀ r > 0, ∃ q ∈ ball p r, q ≠ p ∧ q ∈ s

def IsIsolatedPoint (p : t) (s : Set t) := p ∈ s ∧ ¬IsLimitPoint p s

def IsInteriorPoint (p : t) (s : Set t) := p ∈ s ∧ ∃ r, ball p r ⊆ s

theorem pos_of_mem_ball {r : ℝ} {p q : t} (h : q ∈ ball p r) : 0 < r := by
  simp [openBall] at *
  apply lt_of_le_of_lt (MetricSpace.dist_nonneg p q)
  assumption

def Set.IsOpen (s : Set t) : Prop := ∀ p ∈ s, IsInteriorPoint p s

example : (∅ : Set ℝ).IsOpen := by simp [Set.IsOpen]

example : (Set.univ : Set ℝ).IsOpen := by simp [Set.IsOpen, IsInteriorPoint]

theorem ball_is_open {a : t} {r : ℝ} : (ball a r).IsOpen := by
  simp [Set.IsOpen, openBall, IsInteriorPoint]
  intros b hab
  constructor
  · assumption
  · use r - dist a b
    intro c hbc
    rw [lt_sub_iff_add_lt, add_comm] at hbc
    calc dist a c
      _ ≤ dist a b + dist b c := dist_triangle
      _ < r := hbc
