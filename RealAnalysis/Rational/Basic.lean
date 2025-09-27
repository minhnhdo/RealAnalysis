import RealAnalysis.Rational.Pre.Basic
import RealAnalysis.Rational.Pre.Lemmas

def Rational := Quotient (PreRational.instSetoid)

def Rational.addAux (p q : PreRational) : Rational := Quotient.mk' (PreRational.add p q)

theorem Rational.addAux_lift
  (p q r s : PreRational)
  (h_pr_equiv : p ≈ r)
  (h_qs_equiv : q ≈ s)
  : Rational.addAux p q = Rational.addAux r s := by
    apply Quotient.sound
    exact PreRational.add_well_defined p q r s h_pr_equiv h_qs_equiv

def Rational.add (p q : Rational) : Rational := Quotient.lift₂ Rational.addAux Rational.addAux_lift p q
