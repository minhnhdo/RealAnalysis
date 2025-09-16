import RealAnalysis.Rational.Basic

theorem rational_denominator_int_ne_zero (q : Rational) : (q.denominator : Int) ≠ 0 := by
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
  apply (Int.mul_eq_mul_left_iff (rational_denominator_int_ne_zero q)).mp
  rw [←Int.mul_assoc, Int.mul_comm q.denominator, h_pq_equiv, Int.mul_assoc, h_qr_equiv, ←Int.mul_left_comm]

theorem add_well_defined : ∀ p q r s,
  equivalent_relation p q → equivalent_relation r s → equivalent_relation (p + r) (q + s) := by
    intros p q r s h_pq_equiv h_rs_equiv
    simp at *
    simp [HAdd.hAdd, Add.add, Rational.add, Rational.addDenominator]
    simp [Rational.addNumerator] -- this has to come after so that we don't unfold `@Add.add Int`
    rw [Int.mul_add, Int.add_mul]
    have pq_mul_rs_denom : p.numerator * r.denominator * (q.denominator * s.denominator) =
                            p.denominator * r.denominator * (q.numerator * s.denominator) := by
      repeat rw [Int.mul_assoc]
      repeat rw [Int.mul_comm r.denominator]
      repeat rw [←Int.mul_assoc]
      apply (Int.mul_eq_mul_right_iff (rational_denominator_int_ne_zero r)).mpr
      apply (Int.mul_eq_mul_right_iff (rational_denominator_int_ne_zero s)).mpr
      assumption
    have rs_mul_pq_denom : p.denominator * r.numerator * (q.denominator * s.denominator) =
                            p.denominator * r.denominator * (q.denominator * s.numerator) := by
      repeat rw [Int.mul_comm q.denominator]
      repeat rw [Int.mul_comm p.denominator]
      repeat rw [Int.mul_assoc]
      repeat rw [Int.mul_comm p.denominator]
      repeat rw [←Int.mul_assoc]
      apply (Int.mul_eq_mul_right_iff (rational_denominator_int_ne_zero p)).mpr
      apply (Int.mul_eq_mul_right_iff (rational_denominator_int_ne_zero q)).mpr
      assumption
    rw [pq_mul_rs_denom, Int.add_right_inj, rs_mul_pq_denom]
