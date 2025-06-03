import Mathlib.Tactic

inductive Variable
| mk (name: String)
deriving DecidableEq, Repr

def Variable.name (x: Variable):=
match x with
| mk name => name

open Variable


inductive LambdaTerm where
| varTerm (v: Variable)
| abstraction (x: Variable) (body: LambdaTerm)
| application (func: LambdaTerm) (argument: LambdaTerm)
deriving DecidableEq, Repr


-- Custom printer for lambda terms
def LambdaTerm.toString (t: LambdaTerm): String :=
  match t with
  | varTerm v => v.name
  | abstraction x body =>
    let bodyStr := toString body
    s!"λ{x.name}.{bodyStr}"
  | application func arg =>
    let funcStr := match func with
      | abstraction _ _ => s!"({toString func})"
      | _ => toString func
    let argStr := match arg with
      | abstraction _ _ => s!"({toString arg})"
      | application _ _ => s!"({toString arg})"
      | _ => toString arg
    s!"{funcStr} {argStr}"

instance : Repr LambdaTerm where
  reprPrec t _ := LambdaTerm.toString t


open LambdaTerm

-- postfix:80 "ᵒ" => converse -- \^o (hat and then letter)
-- postfix:80 "⁻" => complement -- \^- (hat dash)

prefix:70 "λ" => abstraction  -- \otimes
infixl:100 "∘" => application   -- \otimes

namespace Combinators

def x' : Variable := ⟨"x"⟩
def y' : Variable := ⟨"y"⟩
def z' : Variable := ⟨"z"⟩
def w' : Variable := ⟨"w"⟩
def x  := varTerm x'
def y  := varTerm y'
def z  := varTerm z'
def w  := varTerm w'

def A := (λx') ((λy') x∘y)
#eval A

def I := (λx') x -- Identity
#eval I

def K := (λx') ((λy') x) -- First projection
#eval K

def Ki := (λx') ((λy') y) -- Second projection
#eval Ki

def M := (λx') (x∘x)  -- Self-application
#eval M
-- λx.x x
-- (λx.x x) z
-- z z


-- (λx.x x) M
-- M M
-- (λx.x x) (λx.x x)
-- (λx.x x) (λx.x x)

end Combinators

-- A redex is a lambda term that consists of an abstraction applied to an argument
def Redex := {
  t: LambdaTerm //
  ∃ (x: Variable)(body: LambdaTerm)(argument: LambdaTerm), t = ((λx) body)∘argument
} deriving DecidableEq, Repr

-- Beta-reduction
-- (λx.λy.x) z
-- λy.z

-- (λx.λy.x)(λx.x z)
-- λy.x <-- (λx.x z)
-- λy.[*] <-- (λx.x z)
-- λy.[λx.x z]
-- λy.z

-- (λx.λy.x)(λx.x z)
-- (λx.λy.x)(z)
-- λy.z

-- (λx.λy.x) a b
-- (λy.a) b
-- a
-- First projection

-- (λx.λy.y) a b
-- b
-- Second projection


-- λy.x <-- (λx.x z)
-- λy.[*] <-- (λx.x z)
-- λy.[λx.x z]
-- λy.[z]

-- -- (λx.λy.x) y
-- λy.x <-- y
-- λw.y

-- abstracton lambdaTerm
  -- Redex

-- var var
-- var application

-- application abstraction
--


def rawSubstitution (target: LambdaTerm) (substitute: LambdaTerm ) (current: LambdaTerm)  : LambdaTerm :=
  match current with
  |  varTerm x => if varTerm x = target then substitute else varTerm x
  |  abstraction x body =>
    if body = target then
      abstraction x substitute
    else abstraction x (rawSubstitution target substitute body)
  | application func argument =>
    if func = target
      then application substitute (
        if argument = target then substitute else rawSubstitution target substitute argument
      )
      else application func (
        if argument = target then substitute else rawSubstitution target substitute argument
      )

-- Ignoring variable capture
def Redex.reduce (rx: Redex) : LambdaTerm :=
  match rx with
  | ⟨ application (abstraction x body) argument, φ   ⟩ =>
    rawSubstitution (varTerm x) argument body
  | ⟨t, φ⟩ => by cases t <;> aesop





namespace Combinators
#eval Redex.reduce  ⟨I∘y, by
  use x', x, y ; rfl⟩

-- This shows substitution for a variable nested under another lambda
#eval  Redex.reduce ⟨ (K∘w), by use x', ((λy') x), w ;rfl ⟩

-- This works

-- TODO
  -- Better printing of lambda terms (custom Repr)
  -- Make a single step version of beta reduce that searches for a single redex and reduces it.









-- def B := (λx') ((λy') ((λz') (x∘(y∘z))))   -- bluebird λxyz.x(yz)

-- def Bl -- Blackbird  λabcd.a(bcd)
-- def C  -- Cardinal  λabc.acb
-- def D -- Dove  λabcd.ab(cd)
-- def E -- Eagle λabcde.ab(cde)
-- def F --  Finch λabc.cba
-- def G -- Goldfinch λabcd.ad(bc)


/-
Simply Typed Lambda Calculus

 -/


-- Our simple types track which terms are functions

-- Have to start with one or more basic types
-- We can think of these as sets.

-- Let's say we have base types A B
-- For a free variable, it can be one of the base types.
--   x:A, y:B, y:A

-- A judgement
-- Context ⊢ LambdaTerm

-- Frege --  Premises ⊢ Conclusion

-- Context is a list of assignments of types to free variables.

-- x:A ⊢ x

-- A -> A
-- A -> (A -> A)
-- (A -> A) -> A

-- y:B ⊢ λ (x:A).y : A -> B


-- y:C ⊢ (λ (x:A).y)  : A -> C

-- t: β
-- (λx:α).t : α -> β



-- y:B ⊢ (λx:A).y : A -> B
--  ⊢ (λy:B).(λx:A).y : B -> A -> B


-- Deduction theorem

--    A, A→B  ⊢ B
--  A ⊢ (A→B) → B
--  ⊢ A → (A→B) → B

-- t: α -> β
-- s: α
-------------
-- t s: β


--  ⊢ λ(x:A). y:B

-- y:C, z:A ⊢ (λ (x:A).y) z : C

-- (λ (x).y) : A -> B

-- (λ (x).y) (z:A)    :   B
-- y:B

-- x:A ⊢ (λ(x:A).λ(x:B).x) x

-- λ(x).λ(x).x


-- def fn (x: str, y: list str) -> int


-- Dependency

-- Types
-- list[str]

-- Polymorphic types
-- list: Type -> Type

-- Ad-hoc polymorphic terms
-- identiy function

-- def(x: str) -> str:
--   x

-- def(x: int) -> int:
--   x

-- use the type of x to determine the type of the function.
--


-- If pigs fly then the sky is pink

---

-- Formation Rule
-- α  is a type
-- β  is a type
-----------
-- α -> β


-- product type
-- Formation Rule
-- α  is a type
-- β  is a type
-----------
-- α  x β

-- Introduction rule for products
-- Γ ⊢ t: α
-- Γ ⊢ s: β
------------
--  Γ ⊢ (s,t): α  x  β


-- Product Elimiations Rules
--  Γ ⊢ (s,t): α  x  β
---------------
--  Γ ⊢ s: α

--  Γ ⊢ (s,t): α  x  β
---------------
--  Γ ⊢ t: β

-- A ∧ B
---------
-- A

-- A ∧ B
---------
-- B


-- Computational Trinitarianism

--    Lambek  -        Curry     -     Howard
-- Categories -      Programs-Types  - Logic
-- Universal Properties - Types - Inference Rules

-- Dependant
-- A type that depends on a term.
-- Vector
-- List [1,2,3,56,7]
-- Vector in ℝ³ [1,2,4]
