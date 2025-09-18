structure Rational where
  numerator : Int
  denominator : Nat
  denominator_ne_zero : denominator ≠ 0

instance : Inhabited Rational where
  default := ⟨0, 1, by decide⟩

instance : OfNat Rational n where
  ofNat := ⟨n, 1, by decide⟩

protected def Rational.neg (q : Rational) : Rational :=
  ⟨-q.numerator, q.denominator, q.denominator_ne_zero⟩

instance : Neg Rational where
  neg := Rational.neg

instance : ToString Rational where
  toString q := s!"{q.numerator}/{q.denominator}"

@[simp]
protected def Rational.equivalent_relation (p q : Rational) : Prop :=
  p.numerator * q.denominator = p.denominator * q.numerator
  deriving Decidable

protected def Rational.addNumerator (p q : Rational) : Int :=
  p.numerator * q.denominator + p.denominator * q.numerator

protected def Rational.addDenominator (p q : Rational) : Nat :=
  p.denominator * q.denominator

protected def Rational.add (p q : Rational) : Rational :=
  let prf : p.denominator * q.denominator ≠ 0 := by
    apply Nat.mul_ne_zero
    exact p.denominator_ne_zero
    exact q.denominator_ne_zero
  ⟨p.addNumerator q, p.addDenominator q, prf⟩

instance : Add Rational where
  add := Rational.add

protected def Rational.sub (p q : Rational) : Rational :=
  p + (-q)

instance : Sub Rational where
  sub := Rational.sub

@[simp]
def Rational.isPositive (p : Rational) : Prop :=
  0 < p.numerator * p.denominator
  deriving Decidable

protected def Rational.lt : Rational → Rational → Prop
  | p, q => (q - p).isPositive
  deriving Decidable

instance : LT Rational where
  lt := Rational.lt
