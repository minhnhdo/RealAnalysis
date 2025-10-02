import RealAnalysis.Rational.Basic
import RealAnalysis.Rational.Lemmas

def RationalQuotient := Quotient Rational.instSetoid

instance : Inhabited RationalQuotient := ⟨Quotient.mk' Inhabited.default⟩

instance {n} : OfNat RationalQuotient n := ⟨Quotient.mk' (OfNat.ofNat n)⟩

protected def RationalQuotient.negAux (p : Rational) : RationalQuotient := Quotient.mk' (Rational.neg p)

theorem RationalQuotient.negAux_lift
  (p q : Rational)
  : p ≈ q → RationalQuotient.negAux p = RationalQuotient.negAux q := by
    intro
    apply Quotient.sound
    apply PreRational.neg_well_defined
    assumption

protected def RationalQuotient.neg (p : RationalQuotient) : RationalQuotient := Quotient.lift RationalQuotient.negAux RationalQuotient.negAux_lift p

instance : Neg RationalQuotient := ⟨RationalQuotient.neg⟩

protected def RationalQuotient.addAux (p q : Rational) : RationalQuotient := Quotient.mk' (Rational.add p q)

theorem RationalQuotient.addAux_lift
  (p q r s : Rational)
  : p ≈ r → q ≈ s → RationalQuotient.addAux p q = RationalQuotient.addAux r s := by
    intros
    apply Quotient.sound
    apply Rational.add_well_defined
    . assumption
    . assumption

protected def RationalQuotient.add (p q : RationalQuotient) : RationalQuotient :=
  Quotient.lift₂ RationalQuotient.addAux RationalQuotient.addAux_lift p q

instance : Add RationalQuotient := ⟨RationalQuotient.add⟩

protected def RationalQuotient.subAux (p q : Rational) : RationalQuotient :=
  Quotient.mk' (Rational.sub p q)

theorem RationalQuotient.subAux_lift
  (p q r s : Rational)
  : p ≈ r → q ≈ s → RationalQuotient.subAux p q = RationalQuotient.subAux r s := by
    intros
    apply Quotient.sound
    apply Rational.sub_well_defined
    . assumption
    . assumption

protected def RationalQuotient.sub (p q : RationalQuotient) : RationalQuotient :=
  Quotient.lift₂ RationalQuotient.subAux RationalQuotient.subAux_lift p q

instance : Sub RationalQuotient := ⟨RationalQuotient.sub⟩
