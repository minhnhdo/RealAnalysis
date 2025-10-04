import Mathlib.Data.Rat.Init

def Rat.abs (q : ℚ) : ℚ := if 0 ≤ q then q else -q
