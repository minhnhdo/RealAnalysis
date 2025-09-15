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

#eval ([1, -1, 3] : List Rational)

@[simp]
def equivalent_relation (p q : Rational) : Prop :=
  p.numerator * q.denominator = p.denominator * q.numerator

theorem rational_denominator_int_not_zero {q : Rational} : (q.denominator : Int) ≠ 0 := by
    apply Int.ofNat_ne_zero.mpr
    exact q.denominator_ne_zero

theorem equivalent_relation_refl : ∀ q, equivalent_relation q q := by
  intro
  simp
  rw [Int.mul_comm]

theorem equivalent_relation_symm : ∀ p q, equivalent_relation p q → equivalent_relation q p := by
  intros p q h_pq_equiv
  simp at *
  rw [Int.mul_comm q.numerator p.denominator, Int.mul_comm q.denominator p.numerator, h_pq_equiv]

theorem equivalent_relation_trans : ∀ p q r, equivalent_relation p q → equivalent_relation q r → equivalent_relation p r := by
  intros p q r h_pq_equiv h_qr_equiv
  simp at *
  have q_denom_ne_zero : (q.denominator : Int) ≠ 0 := by apply rational_denominator_int_not_zero
  apply (Int.mul_eq_mul_left_iff q_denom_ne_zero).mp
  rw [←Int.mul_assoc, Int.mul_comm q.denominator, h_pq_equiv, Int.mul_assoc, h_qr_equiv, ←Int.mul_left_comm]
