structure Rational where
  numerator : Int
  denominator : Nat
  denominator_ne_zero : denominator ≠ 0

instance : Inhabited Rational where
  default := ⟨0, 1, by decide⟩

instance : OfNat Rational n where
  ofNat := ⟨n, 1, by decide⟩

instance : Neg Rational where
  neg q := ⟨-q.numerator, q.denominator, q.denominator_ne_zero⟩

instance : ToString Rational where
  toString q := s!"{q.numerator}/{q.denominator}"

@[simp]
def equivalent_relation (p q : Rational) : Prop :=
  p.numerator * q.denominator = p.denominator * q.numerator
  deriving Decidable

def Rational.addNumerator (p q : Rational) : Int :=
  p.numerator * q.denominator + p.denominator * q.numerator

def Rational.addDenominator (p q : Rational) : Nat :=
  p.denominator * q.denominator

def Rational.add (p q : Rational) : Rational :=
  let prf : p.denominator * q.denominator ≠ 0 := by
    apply Nat.mul_ne_zero
    exact p.denominator_ne_zero
    exact q.denominator_ne_zero
  ⟨p.addNumerator q, p.addDenominator q, prf⟩

instance : Add Rational where
  add := Rational.add
