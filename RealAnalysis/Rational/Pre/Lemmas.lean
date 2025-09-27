import RealAnalysis.Rational.Pre.Basic

theorem PreRational.zero_lt_denominator (p : PreRational): 0 < (p.denominator : Int) := by
  simp
  rw [Nat.pos_iff_ne_zero]
  exact p.denominator_ne_zero

theorem PreRational.denominator_int_ne_zero (q : PreRational) : (q.denominator : Int) ≠ 0 := by
    apply Int.ofNat_ne_zero.mpr
    exact q.denominator_ne_zero

theorem PreRational.equivalent_relation_refl (p : PreRational) : p ≈ p := by
  simp [HasEquiv.Equiv]
  rw [Int.mul_comm]

theorem PreRational.equivalent_relation_symm (p q : PreRational) (h_pq_equiv : p ≈ q) : q ≈ p := by
  simp [HasEquiv.Equiv] at *
  rw [Int.mul_comm q.numerator p.denominator, Int.mul_comm q.denominator p.numerator, h_pq_equiv]

theorem PreRational.equivalent_relation_trans (p q r : PreRational) (h_pq_equiv : p ≈ q) (h_qr_equiv : q ≈ r) : p ≈ r := by
  simp [HasEquiv.Equiv] at *
  apply (Int.mul_eq_mul_left_iff q.denominator_int_ne_zero).mp
  rw [← Int.mul_assoc, Int.mul_comm q.denominator, h_pq_equiv, Int.mul_assoc, h_qr_equiv, ← Int.mul_left_comm]

instance PreRational.instEquivalence : Equivalence PreRational.equivalent_relation where
  refl := PreRational.equivalent_relation_refl
  symm {p} {q} := PreRational.equivalent_relation_symm p q
  trans {p} {q} {r} := PreRational.equivalent_relation_trans p q r

instance PreRational.instSetoid : Setoid PreRational where
  r := PreRational.equivalent_relation
  iseqv := PreRational.instEquivalence

theorem PreRational.neg_numerator (p : PreRational) : (-p).numerator = -(p.numerator) := by rfl

theorem PreRational.neg_denominator (p : PreRational) : (-p).denominator = p.denominator := by rfl

theorem PreRational.neg_well_defined (p q : PreRational) (h_pq_equiv : p ≈ q) : -p ≈ -q := by
  simp [HasEquiv.Equiv, PreRational.neg_numerator, PreRational.neg_denominator] at *
  rw [Int.mul_neg, Int.neg_mul, Int.neg_eq_comm, Int.neg_neg, h_pq_equiv]

theorem PreRational.add_well_defined (p q r s : PreRational) (h_pr_equiv : p ≈ r) (h_qs_equiv : q ≈ s) : (p + q) ≈ (r + s) := by
    simp [HasEquiv.Equiv, HAdd.hAdd, Add.add, PreRational.add, PreRational.addDenominator]
    simp [PreRational.addNumerator] -- this has to come after so that we don't unfold `@Add.add Int`
    rw [Int.mul_add, Int.add_mul]
    have pq_mul_rs_denom : p.numerator * q.denominator * (r.denominator * s.denominator) =
                            p.denominator * q.denominator * (r.numerator * s.denominator) := by
      repeat rw [Int.mul_assoc]
      repeat rw [Int.mul_comm q.denominator]
      repeat rw [←Int.mul_assoc]
      apply (Int.mul_eq_mul_right_iff q.denominator_int_ne_zero).mpr
      apply (Int.mul_eq_mul_right_iff s.denominator_int_ne_zero).mpr
      assumption
    have rs_mul_pq_denom : p.denominator * q.numerator * (r.denominator * s.denominator) =
                            p.denominator * q.denominator * (r.denominator * s.numerator) := by
      repeat rw [Int.mul_comm r.denominator]
      repeat rw [Int.mul_comm p.denominator]
      repeat rw [Int.mul_assoc]
      repeat rw [Int.mul_comm p.denominator]
      repeat rw [←Int.mul_assoc]
      apply (Int.mul_eq_mul_right_iff p.denominator_int_ne_zero).mpr
      apply (Int.mul_eq_mul_right_iff r.denominator_int_ne_zero).mpr
      assumption
    rw [pq_mul_rs_denom, rs_mul_pq_denom]

theorem PreRational.isPositive_well_defined (p q : PreRational) (h_pq_equiv : p ≈ q) (h_p_isPositive : p.isPositive) : q.isPositive := by
    simp [HasEquiv.Equiv] at *
    apply @Int.pos_of_mul_pos_left (q.numerator * q.denominator) (p.denominator * p.denominator)
    . calc
        0 < p.numerator * p.denominator * q.denominator * q.denominator := by
          apply Int.mul_pos
          . apply Int.mul_pos h_p_isPositive
            simp
            rw [Nat.pos_iff_ne_zero]
            exact q.denominator_ne_zero
          . simp
            rw [Nat.pos_iff_ne_zero]
            exact q.denominator_ne_zero
        _ = p.denominator * p.numerator * q.denominator * q.denominator := by rw [Int.mul_comm p.numerator]
        _ = p.denominator * (p.numerator * q.denominator) * q.denominator := by rw [Int.mul_assoc p.denominator]
        _ = p.denominator * (p.denominator * q.numerator) * q.denominator := by rw [h_pq_equiv]
        _ = q.numerator * q.denominator * (p.denominator * p.denominator) := by
          rw [Int.mul_assoc p.denominator, Int.mul_comm, Int.mul_assoc p.denominator, Int.mul_comm p.denominator]
          rw [Int.mul_assoc (q.numerator * q.denominator)]
    . apply Int.mul_pos
      . simp
        rw [Nat.pos_iff_ne_zero]
        exact p.denominator_ne_zero
      . simp
        rw [Nat.pos_iff_ne_zero]
        exact p.denominator_ne_zero

theorem PreRational.sub_well_defined (p q r s : PreRational) (h_pq_equiv : p ≈ q) (h_rs_equiv : r ≈ s) : (p - r) ≈ (q - s) := by
    simp [HasEquiv.Equiv] at *
    simp [HSub.hSub, Sub.sub, PreRational.sub, HAdd.hAdd, Add.add, PreRational.add] at *
    simp [PreRational.addNumerator, PreRational.addDenominator] at *
    repeat rw [PreRational.neg_denominator, PreRational.neg_numerator]
    rw [Int.mul_neg p.denominator, Int.mul_neg q.denominator]
    calc (p.numerator * ↑r.denominator + -(↑p.denominator * r.numerator)) * (↑q.denominator * ↑s.denominator)
      _ = p.numerator * r.denominator * (q.denominator * s.denominator) +
          -(p.denominator * r.numerator) * (q.denominator * s.denominator) := by rw [Int.add_mul]
      _ = p.numerator * (q.denominator * s.denominator) * r.denominator +
          -(p.denominator * r.numerator) * (q.denominator * s.denominator) := by rw [Int.mul_right_comm]
      _ = p.numerator * q.denominator * s.denominator * r.denominator +
          -(p.denominator * r.numerator) * (q.denominator * s.denominator) := by rw [← Int.mul_assoc]
      _ = p.numerator * q.denominator * s.denominator * r.denominator +
          -(p.denominator * r.numerator * (q.denominator * s.denominator)) := by rw [Int.neg_mul]
      _ = p.numerator * q.denominator * s.denominator * r.denominator +
          -(p.denominator * (q.denominator * s.denominator) * r.numerator) := by rw [Int.mul_right_comm p.denominator]
      _ = p.numerator * q.denominator * s.denominator * r.denominator +
          -(p.denominator * q.denominator * s.denominator * r.numerator) := by rw [← Int.mul_assoc]
      _ = p.denominator * q.numerator * s.denominator * r.denominator +
          -(p.denominator * q.denominator * s.denominator * r.numerator) := by rw [h_pq_equiv]
      _ = p.denominator * (q.numerator * s.denominator) * r.denominator +
          -(p.denominator * q.denominator * s.denominator * r.numerator) := by rw [← Int.mul_assoc]
      _ = p.denominator * r.denominator * (q.numerator * s.denominator) +
          -(p.denominator * q.denominator * s.denominator * r.numerator) := by rw [Int.mul_right_comm]
      _ = p.denominator * r.denominator * (q.numerator * s.denominator) +
          -(p.denominator * q.denominator * (s.denominator * r.numerator)) := by rw [Int.mul_assoc (p.denominator * q.denominator)]
      _ = p.denominator * r.denominator * (q.numerator * s.denominator) +
          -(p.denominator * q.denominator * (r.numerator * s.denominator)) := by rw [Int.mul_comm s.denominator]
      _ = p.denominator * r.denominator * (q.numerator * s.denominator) +
          -(p.denominator * q.denominator * (r.denominator * s.numerator)) := by rw [h_rs_equiv]
      _ = p.denominator * r.denominator * (q.numerator * s.denominator) +
          -(p.denominator * q.denominator * r.denominator * s.numerator) := by rw [← Int.mul_assoc (p.denominator * q.denominator)]
      _ = p.denominator * r.denominator * (q.numerator * s.denominator) +
          -(p.denominator * (q.denominator * r.denominator) * s.numerator) := by rw [← Int.mul_assoc p.denominator]
      _ = p.denominator * r.denominator * (q.numerator * s.denominator) +
          -(p.denominator * (r.denominator * q.denominator) * s.numerator) := by rw [Int.mul_comm q.denominator]
      _ = p.denominator * r.denominator * (q.numerator * s.denominator) +
          -(p.denominator * r.denominator * q.denominator * s.numerator) := by rw [← Int.mul_assoc p.denominator]
      _ = p.denominator * r.denominator * (q.numerator * s.denominator) +
          -(p.denominator * r.denominator * (q.denominator * s.numerator)) := by rw [Int.mul_assoc (p.denominator * r.denominator )]
      _ = p.denominator * r.denominator * (q.numerator * s.denominator) +
          p.denominator * r.denominator * -(q.denominator * s.numerator) := by rw [Int.mul_neg]
      _ = p.denominator * r.denominator *
        ((q.numerator * s.denominator) + -(q.denominator * s.numerator)) := by rw [Int.mul_add]

theorem PreRational.lt_well_defined (p q r s: PreRational) (h_pr_equiv : p ≈ r) (h_qs_equiv : q ≈ s) (h_p_lt_r : p < q) : r < s := by
    simp [HasEquiv.Equiv, LT.lt] at *
    simp [PreRational.lt, HSub.hSub, Sub.sub, PreRational.sub, HAdd.hAdd, Add.add, PreRational.add] at *
    simp [PreRational.addNumerator, PreRational.addDenominator, PreRational.isPositive] at *
    rw [PreRational.neg_numerator, PreRational.neg_denominator] at *
    apply Int.mul_pos
    . apply @Int.pos_of_mul_pos_left (s.numerator * r.denominator + s.denominator * -r.numerator) p.denominator
      . apply @Int.pos_of_mul_pos_right q.denominator
        . rw [Int.add_mul, Int.mul_assoc s.denominator, Int.mul_comm (-r.numerator), Int.mul_neg, ← h_pr_equiv]
          rw [← Int.neg_mul, Int.mul_assoc, Int.mul_comm r.denominator, ← Int.mul_assoc, ← Int.mul_assoc]
          rw [← Int.add_mul, ← Int.mul_assoc, Int.mul_add, ← Int.mul_assoc, ← Int.mul_assoc, ← h_qs_equiv]
          rw [Int.mul_comm q.numerator, Int.mul_comm q.denominator, Int.mul_assoc, Int.mul_assoc, ← Int.mul_add]
          apply Int.mul_pos
          . apply Int.mul_pos
            . exact s.zero_lt_denominator
            . apply Int.pos_of_mul_pos_left h_p_lt_r
              apply Int.mul_pos
              . exact q.zero_lt_denominator
              . exact p.zero_lt_denominator
          . exact r.zero_lt_denominator
        . exact q.zero_lt_denominator
      . exact p.zero_lt_denominator
    . apply Int.mul_pos
      . exact s.zero_lt_denominator
      . exact r.zero_lt_denominator

theorem PreRational.lt_trans (p q r : PreRational) (h_p_lt_q : p < q) (h_q_lt_r : q < r) : p < r := by
    simp [LT.lt, PreRational.lt] at *
    simp [PreRational.isPositive, HSub.hSub, Sub.sub, PreRational.sub, HAdd.hAdd, Add.add, PreRational.add] at *
    simp [PreRational.addNumerator, PreRational.addDenominator] at *
    rw [PreRational.neg_numerator, PreRational.neg_denominator] at *
    apply Int.mul_pos
    . apply @Int.pos_of_mul_pos_right q.denominator
      . have h₁ : 0 < q.denominator * r.numerator * p.denominator + (-q.numerator) * r.denominator * p.denominator := by
          rw [Int.mul_comm (-q.numerator), ← Int.add_mul, Int.mul_comm q.denominator]
          apply Int.mul_pos
          . apply @Int.pos_of_mul_pos_left _ ((r.denominator : Int) * q.denominator)
            . assumption
            . apply Int.mul_pos
              . exact r.zero_lt_denominator
              . exact q.zero_lt_denominator
          . exact p.zero_lt_denominator
        have h₂ : 0 < q.numerator * r.denominator * p.denominator + q.denominator * r.denominator * (-p.numerator) := by
          rw [Int.mul_right_comm, Int.mul_right_comm q.denominator, ← Int.add_mul]
          apply Int.mul_pos
          . apply @Int.pos_of_mul_pos_left _ ((q.denominator : Int) * p.denominator)
            . assumption
            . apply Int.mul_pos
              . exact q.zero_lt_denominator
              . exact p.zero_lt_denominator
          . exact r.zero_lt_denominator
        calc
          0 < q.denominator * r.numerator * p.denominator + (-q.numerator) * r.denominator * p.denominator +
              (q.numerator * r.denominator * p.denominator + q.denominator * r.denominator * (-p.numerator)) := by apply Int.add_pos h₁ h₂
          _ = q.denominator * r.numerator * p.denominator + (-q.numerator) * r.denominator * p.denominator +
              (q.denominator * r.denominator * (-p.numerator) + q.numerator * r.denominator * p.denominator) := by rw [Int.add_comm (q.numerator * _ * _)]
          _ = q.denominator * r.numerator * p.denominator + ((-q.numerator) * r.denominator * p.denominator +
              (q.denominator * r.denominator * (-p.numerator) + q.numerator * r.denominator * p.denominator)) := by rw [Int.add_assoc]
          _ = q.denominator * r.numerator * p.denominator + (q.denominator * r.denominator * (-p.numerator) +
              ((-q.numerator) * r.denominator * p.denominator + q.numerator * r.denominator * p.denominator)) := by rw [← Int.add_left_comm (q.denominator * _ * _)]
          _ = q.denominator * r.numerator * p.denominator + (q.denominator * r.denominator * (-p.numerator) +
              ((-q.numerator) * (r.denominator * p.denominator) + q.numerator * r.denominator * p.denominator)) := by rw [← Int.mul_assoc (-q.numerator)]
          _ = q.denominator * r.numerator * p.denominator + (q.denominator * r.denominator * (-p.numerator) +
              ((-q.numerator) * (r.denominator * p.denominator) + q.numerator * (r.denominator * p.denominator))) := by rw [← Int.mul_assoc q.numerator]
          _ = q.denominator * r.numerator * p.denominator + (q.denominator * r.denominator * (-p.numerator) +
              ((-q.numerator + q.numerator) * (r.denominator * p.denominator))) := by rw [Int.add_mul]
          _ = q.denominator * r.numerator * p.denominator + (q.denominator * r.denominator * (-p.numerator) +
              (0 * (r.denominator * p.denominator))) := by rw [Int.add_left_neg]
          _ = q.denominator * r.numerator * p.denominator + (q.denominator * r.denominator * (-p.numerator) + 0) := by rw [Int.zero_mul]
          _ = q.denominator * r.numerator * p.denominator + q.denominator * r.denominator * (-p.numerator) := by rw [Int.add_zero]
          _ = q.denominator * (r.numerator * p.denominator) + q.denominator * (r.denominator * (-p.numerator)) := by repeat rw [Int.mul_assoc]
          _ = q.denominator * (r.numerator * p.denominator + r.denominator * (-p.numerator)) := by rw [Int.mul_add]
      . exact q.zero_lt_denominator
    . apply Int.mul_pos
      . exact r.zero_lt_denominator
      . exact p.zero_lt_denominator

theorem PreRational.lt_trichotomy (p q : PreRational) : p < q ∨ p ≈ q ∨ q < p := by
  simp [LT.lt, PreRational.lt, HasEquiv.Equiv]
  simp [PreRational.isPositive, HSub.hSub, Sub.sub, PreRational.sub, HAdd.hAdd, Add.add, PreRational.add]
  simp [PreRational.addNumerator, PreRational.addDenominator, PreRational.neg_denominator, PreRational.neg_numerator]
  match Int.lt_trichotomy 0 ((q.numerator * p.denominator + q.denominator * -p.numerator) * (q.denominator * p.denominator)) with
  | .inl _ =>
    left
    assumption
  | .inr (.inl prf) =>
    right
    left
    symm
    rw [Int.mul_comm, Int.mul_comm p.numerator, ← Int.sub_eq_zero, Int.sub_eq_add_neg, ← Int.neg_mul, Int.neg_mul_comm]
    symm at prf
    rw [Int.mul_eq_zero] at prf
    match prf with
    | .inl _ =>
      assumption
    | .inr prf =>
      have ne_prf : (q.denominator : Int) * p.denominator ≠ 0 := by
        apply Int.mul_ne_zero
        . exact q.denominator_int_ne_zero
        . exact p.denominator_int_ne_zero
      contradiction
  | .inr (.inr _) =>
    right
    right
    rw [← Int.neg_lt_zero_iff, ← Int.neg_mul, Int.mul_comm p.denominator q.denominator, Int.add_comm, Int.neg_add]
    rw [← Int.neg_mul, Int.neg_mul_neg, ← Int.neg_mul, Int.mul_comm p.denominator, Int.mul_comm (-p.numerator)]
    assumption
