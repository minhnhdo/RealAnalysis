structure PreRational where
  numerator : Int
  denominator : Nat
  denominator_ne_zero : denominator ≠ 0

instance : Inhabited PreRational where
  default := ⟨0, 1, by decide⟩

instance {n} : OfNat PreRational n where
  ofNat := ⟨n, 1, by decide⟩

protected def PreRational.neg (q : PreRational) : PreRational :=
  ⟨-q.numerator, q.denominator, q.denominator_ne_zero⟩

instance : Neg PreRational where
  neg := PreRational.neg

instance : ToString PreRational where
  toString q := s!"{q.numerator}/{q.denominator}"

@[simp]
protected def PreRational.equivalent_relation (p q : PreRational) : Prop :=
  p.numerator * q.denominator = p.denominator * q.numerator
  deriving Decidable

instance : HasEquiv PreRational := ⟨PreRational.equivalent_relation⟩

protected def PreRational.addNumerator (p q : PreRational) : Int :=
  p.numerator * q.denominator + p.denominator * q.numerator

protected def PreRational.addDenominator (p q : PreRational) : Nat :=
  p.denominator * q.denominator

protected def PreRational.add (p q : PreRational) : PreRational :=
  let prf : p.denominator * q.denominator ≠ 0 := by
    apply Nat.mul_ne_zero
    exact p.denominator_ne_zero
    exact q.denominator_ne_zero
  ⟨p.addNumerator q, p.addDenominator q, prf⟩

instance : Add PreRational where
  add := PreRational.add

protected def PreRational.sub (p q : PreRational) : PreRational :=
  p + (-q)

instance : Sub PreRational where
  sub := PreRational.sub

def PreRational.isPositive (p : PreRational) : Prop :=
  0 < p.numerator * p.denominator
  deriving Decidable

protected def PreRational.lt : PreRational → PreRational → Prop
  | p, q => (q - p).isPositive
  deriving Decidable

instance : LT PreRational where
  lt := PreRational.lt
