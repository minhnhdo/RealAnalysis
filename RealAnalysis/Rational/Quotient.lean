import RealAnalysis.Rational.Basic
import RealAnalysis.Rational.Lemmas

def RationalQuotient := Quotient (PreRational.instSetoid)

instance : Inhabited RationalQuotient := ⟨Quotient.mk' Inhabited.default⟩

instance {n} : OfNat RationalQuotient n := ⟨Quotient.mk' (OfNat.ofNat n)⟩

protected def RationalQuotient.negAux (p : PreRational) : RationalQuotient := Quotient.mk' (PreRational.neg p)

theorem RationalQuotient.negAux_lift
  (p q : PreRational)
  : p ≈ q → RationalQuotient.negAux p = RationalQuotient.negAux q := by
    intro
    apply Quotient.sound
    apply PreRational.neg_well_defined
    assumption

protected def RationalQuotient.neg (p : RationalQuotient) : RationalQuotient := Quotient.lift RationalQuotient.negAux RationalQuotient.negAux_lift p

instance : Neg RationalQuotient := ⟨RationalQuotient.neg⟩

protected def RationalQuotient.addAux (p q : PreRational) : RationalQuotient := Quotient.mk' (PreRational.add p q)

theorem RationalQuotient.addAux_lift
  (p q r s : PreRational)
  : p ≈ r → q ≈ s → RationalQuotient.addAux p q = RationalQuotient.addAux r s := by
    intros
    apply Quotient.sound
    apply PreRational.add_well_defined
    . assumption
    . assumption

protected def RationalQuotient.add (p q : RationalQuotient) : RationalQuotient :=
  Quotient.lift₂ RationalQuotient.addAux RationalQuotient.addAux_lift p q

instance : Add RationalQuotient := ⟨RationalQuotient.add⟩

protected def RationalQuotient.subAux (p q : PreRational) : RationalQuotient :=
  Quotient.mk' (PreRational.sub p q)

theorem RationalQuotient.subAux_lift
  (p q r s : PreRational)
  : p ≈ r → q ≈ s → RationalQuotient.subAux p q = RationalQuotient.subAux r s := by
    intros
    apply Quotient.sound
    apply PreRational.sub_well_defined
    . assumption
    . assumption

protected def RationalQuotient.sub (p q : RationalQuotient) : RationalQuotient :=
  Quotient.lift₂ RationalQuotient.subAux RationalQuotient.subAux_lift p q

instance : Sub RationalQuotient := ⟨RationalQuotient.sub⟩
