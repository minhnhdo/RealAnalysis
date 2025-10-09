import Mathlib.Data.Rat.Init
import RealAnalysis.Rat.Defs

def IsCauchySequence (f : ℕ → ℚ) :=
  ∀ ε > 0, ∃ i, ∀ j ≥ i, (f i - f j).abs < ε

def CauchySequence :=
  { f : ℕ → ℚ // IsCauchySequence f }

instance : CoeFun CauchySequence fun _ => ℕ → ℚ :=
  ⟨Subtype.val⟩

@[ext]
theorem ext {f g : CauchySequence} (h : ∀ i, f i = g i) : f = g := Subtype.eq (funext h)

theorem isCauchySequence (f : CauchySequence) : IsCauchySequence f := f.2
