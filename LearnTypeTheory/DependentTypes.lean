import Mathlib.Tactic
open Classical
-- Defining Types from Scratch using only Pi types (no inductive types except for the info view)
universe u

-- BOOLEANS AS PI TYPE
def Bool_ :=  Π (α : Type u), α → α → α
-- Display Bool_ using normal Bool
instance : Repr Bool_ where
  reprPrec t _ := Repr.reprPrec (t Bool true false) 0

def T : Bool_ := λ (α : Type u) (a: α ) (b:α ) => a
def F : Bool_ := λ (α : Type u) (a: α ) (b:α ) => b

-- When condition is T, returns a, otherwise b
-- Note, we don't have to use Lean's built-in if else statement since the logic is expressed by the combinators.
def ifElse  (condition: Bool_) : Bool_ := λ  (α : Type u) (a b: α )  =>  condition α a b

def and (p q: Bool_) : Bool_ :=
  ifElse p Bool_ (ifElse q Bool_ T F) F
-- "and" Truth table
#eval and T T -- true
#eval and F T -- false
#eval and T F -- false
#eval and F F -- false


def not (p: Bool_) : Bool_ := ifElse p Bool_ F T
-- "not" truth table
#eval not T -- false
#eval not F -- true


-- This example shows that in Lean's type system with Classical axioms violates parametricity since we can use the structure of the type α to define the function's behaiviour. However, without Classical axioms we don't have universal deciable equality for types so we can't case split on the unknown type α. Therefore, in the constructive fragment of Lean's type system, parametricity holds. However, proving this inside Lean is another issue.
-- See: https://cs.stackexchange.com/questions/169987/are-dependent-functions-and-pairs-in-lean-parametrically-polymorphic
noncomputable  def counter_example_to_parametricity : Bool_ :=
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
      -- I can't figure out how to prove it, might not be provable internally?
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

-- Display Nat_ using normal Nat
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
