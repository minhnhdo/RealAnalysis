structure Rational where
  numerator : Int
  denominator : Nat
  denominator_not_zero : denominator ≠ 0

@[simp]
def equivalent_relation (p q : Rational) : Prop :=
  p.numerator * q.denominator = p.denominator * q.numerator

theorem equivalent_relation_refl : ∀ q, equivalent_relation q q := by
  intro
  simp
  rw [Int.mul_comm]

theorem equivalent_relation_symm : ∀ p q, equivalent_relation p q → equivalent_relation q p := by
  intros p q h_pq_equiv
  simp at h_pq_equiv
  simp
  rw [Int.mul_comm q.numerator p.denominator, Int.mul_comm q.denominator p.numerator, h_pq_equiv]

instance : OfNat Rational n where
  ofNat := ⟨n, 1, by decide⟩

instance : Neg Rational where
  neg q := ⟨-q.numerator, q.denominator, q.denominator_not_zero⟩

instance : ToString Rational where
  toString q := toString q.numerator ++ " /. " ++ toString q.denominator

#eval ([1, -1, 3] : List Rational)
