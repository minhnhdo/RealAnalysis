import RealAnalysis.Rational.Basic

theorem Rational.denominator_int_ne_zero (q : Rational) : (q.denominator : Int) ≠ 0 := by
    apply Int.ofNat_ne_zero.mpr
    exact q.denominator_ne_zero

theorem Rational.equivalent_relation_refl (p : Rational) : p.equivalent_relation p := by
  simp
  rw [Int.mul_comm]

theorem Rational.equivalent_relation_symm (p q : Rational) (h_pq_equiv : p.equivalent_relation q) : q.equivalent_relation p := by
  simp at *
  rw [Int.mul_comm q.numerator p.denominator, Int.mul_comm q.denominator p.numerator, h_pq_equiv]

theorem Rational.equivalent_relation_trans (p q r : Rational) (h_pq_equiv : p.equivalent_relation q) (h_qr_equiv : q.equivalent_relation r) : p.equivalent_relation r := by
  simp at *
  apply (Int.mul_eq_mul_left_iff (Rational.denominator_int_ne_zero q)).mp
  rw [←Int.mul_assoc, Int.mul_comm q.denominator, h_pq_equiv, Int.mul_assoc, h_qr_equiv, ←Int.mul_left_comm]

theorem Rational.add_well_defined
  (p q r s : Rational)
  (h_pq_equiv : p.equivalent_relation q)
  (h_rs_equiv : r.equivalent_relation s) :
  (p + r).equivalent_relation (q + s) := by
    simp at *
    simp [HAdd.hAdd, Add.add, Rational.add, Rational.addDenominator]
    simp [Rational.addNumerator] -- this has to come after so that we don't unfold `@Add.add Int`
    rw [Int.mul_add, Int.add_mul]
    have pq_mul_rs_denom : p.numerator * r.denominator * (q.denominator * s.denominator) =
                            p.denominator * r.denominator * (q.numerator * s.denominator) := by
      repeat rw [Int.mul_assoc]
      repeat rw [Int.mul_comm r.denominator]
      repeat rw [←Int.mul_assoc]
      apply (Int.mul_eq_mul_right_iff (Rational.denominator_int_ne_zero r)).mpr
      apply (Int.mul_eq_mul_right_iff (Rational.denominator_int_ne_zero s)).mpr
      assumption
    have rs_mul_pq_denom : p.denominator * r.numerator * (q.denominator * s.denominator) =
                            p.denominator * r.denominator * (q.denominator * s.numerator) := by
      repeat rw [Int.mul_comm q.denominator]
      repeat rw [Int.mul_comm p.denominator]
      repeat rw [Int.mul_assoc]
      repeat rw [Int.mul_comm p.denominator]
      repeat rw [←Int.mul_assoc]
      apply (Int.mul_eq_mul_right_iff (Rational.denominator_int_ne_zero p)).mpr
      apply (Int.mul_eq_mul_right_iff (Rational.denominator_int_ne_zero q)).mpr
      assumption
    rw [pq_mul_rs_denom, rs_mul_pq_denom]
