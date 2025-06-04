import Mathlib.Tactic
open Classical
-- Defining Types from Scratch using only Pi types (no inductive types except for the info view)

universe u


-- BOOLEANS AS PI TYPE
def Bool_ :=  Π (α : Type u), α → α → α

def T : Bool_ := λ (α : Type u) (a: α ) (b:α ) => a
def F : Bool_ := λ (α : Type u) (a: α ) (b:α ) => b




instance : Repr Bool_ where
  reprPrec t _ := Repr.reprPrec (t Bool true false) 0

-- When condition is T, returns a, otherwise b
def elseIf  (condition: Bool_) : Bool_ := λ  (α : Type u) (a b: α )  =>  (condition α a) b

def and (p q: Bool_) : Bool_ :=
  elseIf p Bool_ (elseIf q Bool_ T F) F
-- "and" Truth table
#eval and T T
#eval and F T
#eval and T F
#eval and F F

def not (p: Bool_) : Bool_ := elseIf p Bool_ F T
-- "not" truth table
#eval not T
#eval not F


-- This example shows that in Lean's type system we can't actually assume parametricity since we can use the structure of the type α to define the function's behaiviour.
noncomputable def counter_example_to_parametricity : Bool_ :=
  λ (α : Type) (a : α) (b : α) =>
    if α = Bool then  a  -- If α is Bool, behave like T
    else b

-- This is false in Lean, but it would be true if Bool_ was parametric.
def boolEquiv : Bool_ ≃ Bool := {
  toFun (b: Bool_) : Bool :=  b Bool true false
  invFun (b: Bool):=
    if b = true
    then fun (α : Type)(t: α )(f:α ) => t
    else fun (α : Type) (t: α )(f:α ) => f
  left_inv := by
    intro x
    simp
    funext α a b
    by_cases h: x Bool true false = true
    · simp_all
      -- Can't prove it without paramatricity axiom?
      -- This demonstrates why we need inductive types
      sorry -- case pos
    · simp_all
      sorry -- case neg
  right_inv := by
    -- No problem proving it the other direction (from Bool to Bool_)
    intro b
    simp_all
    by_cases h: b = true
    · subst h
      simp_all only [↓reduceIte]
    · simp_all only [Bool.not_eq_true, Bool.false_eq_true, ↓reduceIte]
}


-- NATURAL NUMBERS AS PI TYPE

def Nat_ :=  Π (α : Type), α → (α → α) → α

instance : Repr Nat_ where
  reprPrec n _ := Repr.reprPrec (n Nat Nat.zero Nat.succ ) 0

def n0 : Nat_ := λ (α : Type) (zero: α ) (_: α → α ) => zero

#eval n0

def n1 : Nat_ := λ (α : Type) (zero: α ) (succ: α → α ) => succ zero
#eval n1

def n2 : Nat_ := λ (α : Type) (zero: α ) (succ: α → α ) => succ (succ zero)
#eval n2

def n3 : Nat_ :=
  λ (α : Type) (zero: α ) (succ: α → α ) => succ (succ (succ zero))
#eval n3

def succ_ (n : Nat_) : Nat_ :=
  λ α z s => s (n α z s)

#eval succ_ n3

def add (n m : Nat_) : Nat_ :=
  λ α zero succ =>
    let m_value : α  := m α zero succ -- We get the fully applied lambda term for b
    n α m_value succ -- We use m_value as the new "zero" for a this means that, if n applies succ, it will add additional layers of iteration on top of m_value

#eval add n3 (succ_ n3) -- 7


def mul (n m : Nat_) : Nat_ :=
  λ α zero succ =>
    n α                  -- run a times …
      zero                  -- starting from zero
      (λ (x:α) => m α x succ)   -- each addition “step” adds “run m starting from x”

#eval mul n2 n3 -- 6
#eval mul n3 (add n2 n3) -- 15

/-
See inside what's happening with mul n2 n3

def n2 : Nat_ := λ (α : Type) (zero: α ) (succ: α → α ) => succ (succ zero)

def n3 : Nat_ :=
  λ (α : Type) (zero: α ) (succ: α → α ) => succ (succ (succ zero))

def twoTimesThree :=  mul n2 m3

Beta reduction:
    n2 α zero (λ (x:α) => n3 α x succ) ((λ (x:α) => n3 α x succ) zero)
    n2 α zero (λ (x:α) => n3 α x succ) (n3 α zero succ)
    n2 α zero (λ (x:α) => n3 α x succ) (succ (succ (succ zero)))
    n2 α zero (n3 α (succ (succ (succ zero))) succ)
    n2 α zero succ (succ (succ (succ (succ (succ zero)))))
-/






def nat_iso_nat :   Nat_ ≃ Nat := by sorry
