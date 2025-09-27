import RealAnalysis.Rational.Pre.Basic
import RealAnalysis.Rational.Pre.Lemmas

def Rational := Quotient (PreRational.instSetoid)

instance : Inhabited Rational := ⟨Quotient.mk' Inhabited.default⟩

instance {n} : OfNat Rational n := ⟨Quotient.mk' (OfNat.ofNat n)⟩

def Rational.negAux (p : PreRational) : Rational := Quotient.mk' (PreRational.neg p)

theorem Rational.negAux_lift (p q : PreRational) : p ≈ q → Rational.negAux p = Rational.negAux q := by
  intro
  apply Quotient.sound
  apply PreRational.neg_well_defined
  assumption

def Rational.neg (p : Rational) : Rational := Quotient.lift Rational.negAux Rational.negAux_lift p

instance : Neg Rational := ⟨Rational.neg⟩

def Rational.addAux (p q : PreRational) : Rational := Quotient.mk' (PreRational.add p q)

theorem Rational.addAux_lift (p q r s : PreRational) : p ≈ r →  q ≈ s → Rational.addAux p q = Rational.addAux r s := by
  intros
  apply Quotient.sound
  apply PreRational.add_well_defined
  . assumption
  . assumption

def Rational.add (p q : Rational) : Rational := Quotient.lift₂ Rational.addAux Rational.addAux_lift p q

instance : Add Rational := ⟨Rational.add⟩
