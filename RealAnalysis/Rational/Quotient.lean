import RealAnalysis.Rational.Basic
import RealAnalysis.Rational.Lemmas

def Rational := Quotient (PreRational.instSetoid)

instance : Inhabited Rational := ⟨Quotient.mk' Inhabited.default⟩

instance {n} : OfNat Rational n := ⟨Quotient.mk' (OfNat.ofNat n)⟩

protected def Rational.negAux (p : PreRational) : Rational := Quotient.mk' (PreRational.neg p)

theorem Rational.negAux_lift (p q : PreRational) : p ≈ q → Rational.negAux p = Rational.negAux q := by
  intro
  apply Quotient.sound
  apply PreRational.neg_well_defined
  assumption

protected def Rational.neg (p : Rational) : Rational := Quotient.lift Rational.negAux Rational.negAux_lift p

instance : Neg Rational := ⟨Rational.neg⟩

protected def Rational.addAux (p q : PreRational) : Rational := Quotient.mk' (PreRational.add p q)

theorem Rational.addAux_lift (p q r s : PreRational) : p ≈ r → q ≈ s → Rational.addAux p q = Rational.addAux r s := by
  intros
  apply Quotient.sound
  apply PreRational.add_well_defined
  . assumption
  . assumption

protected def Rational.add (p q : Rational) : Rational := Quotient.lift₂ Rational.addAux Rational.addAux_lift p q

instance : Add Rational := ⟨Rational.add⟩

protected def Rational.subAux (p q : PreRational) : Rational := Quotient.mk' (PreRational.sub p q)

theorem Rational.subAux_lift (p q r s : PreRational) : p ≈ r → q ≈ s → Rational.subAux p q = Rational.subAux r s := by
  intros
  apply Quotient.sound
  apply PreRational.sub_well_defined
  . assumption
  . assumption

protected def Rational.sub (p q : Rational) : Rational := Quotient.lift₂ Rational.subAux Rational.subAux_lift p q

instance : Sub Rational := ⟨Rational.sub⟩
