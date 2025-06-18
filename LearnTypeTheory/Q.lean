import LearnTypeTheory.SimplyTyped
import Mathlib.Tactic

open SimpleType
inductive QTerm :  SimpleType  → Type  where
| lam  {t: SimpleType} (l: STLambdaTerm t) : QTerm t
| eq  (t: SimpleType) :  QTerm (t ⟶  t ⟶ Ω)
| ι : QTerm ((ind ⟶ Ω ) ⟶ ind)
