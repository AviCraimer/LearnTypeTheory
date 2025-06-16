import Mathlib.Tactic

universe u v

inductive SimpleType :  Type  where
| ind  : SimpleType
| Ω  : SimpleType
| arrow   (dom: SimpleType)(cod: SimpleType) :  SimpleType
deriving DecidableEq, Repr

-- Interprets the expression t, with a non-empty type α as the type of individuals
@[simp]
def SimpleType.toType (t: SimpleType) (α : Type) [Nonempty α]  :=
match t with
| ind => α
| Ω => Bool
| arrow dom cod => dom.toType α  → cod.toType α

open SimpleType

structure  STLambdaTerm.Variable where
name: String
type: SimpleType
deriving DecidableEq, Repr
open STLambdaTerm

inductive STLambdaTerm : SimpleType → Type where
| varTerm (v: Variable) : STLambdaTerm v.type
| abstraction  {cod: SimpleType} (x: Variable) (body:  STLambdaTerm cod) : STLambdaTerm (arrow  x.type cod)

| application {dom cod: SimpleType}  (func: STLambdaTerm (arrow dom cod)) (argument: STLambdaTerm dom) : STLambdaTerm cod
deriving  Repr

@[simp]
def STLambdaTerm.type {t: SimpleType} (_: STLambdaTerm t)  (α : Type) [Nonempty α]  := t

@[simp]
def STLambdaTerm.toType {t: SimpleType} (_: STLambdaTerm t)  (α : Type) [Nonempty α]  := t.toType α

@[simp]
def STLambdaTerm.toFnType {t: SimpleType} (term: STLambdaTerm t)  (α : Type) [Nonempty α]  :=
match term with
| varTerm v  => (varTerm v).toType α → (varTerm v).toType α
| @abstraction cod x body  => x.type.toType α  → cod.toType α
| application  func arg    => (application  func arg ).toType α


def STLambdaTerm.Env (α : Type) [Nonempty α]  :=  (v: Variable) → v.type.toType α


-- The interpretation function `toLeanFun` takes an environment `env`,  which maps variables to their values.
def STLambdaTerm.toLeanFun {t: SimpleType} (term: STLambdaTerm t) (α : Type) [Nonempty α] (env: Env α ) : t.toType α :=
  match term with
  | varTerm v =>
      -- The interpretation of a variable is its value in the environment.
      env v
  | @abstraction cod v body =>
      -- The interpretation of a lambda abstraction is a Lean function.
      fun (y : v.type.toType α) =>
        -- To interpret the body, we use a new environment where `v` is
        -- mapped to the function's argument `y`.
        let new_env  : Env α := fun (v2 : Variable) =>
          if h: v2 = v
          then
            h ▸ y
          else env v2
        toLeanFun body α new_env
  | application func arg =>
      -- The interpretation of an application is the application of the
      -- interpreted function to the interpreted argument.
      let f := toLeanFun func α env
      let a := toLeanFun arg α env
      f a



--- TESTS

-- We'll use these variables in our examples.
def x_ind : Variable := { name := "x", type := ind }
def y_ind : Variable := { name := "y", type := ind }
def z_ind : Variable := { name := "z", type := ind }

def p_bool : Variable := { name := "p", type := Ω }

def ind_to_ind : SimpleType := arrow ind ind
def f_ind_to_ind : Variable := { name := "f", type := ind_to_ind }


def defaultValue (t: SimpleType) : t.toType Nat :=
  match t with
  | ind => (0:ℕ)
  | Ω   => false
  | arrow _ cod => fun _ => defaultValue cod

def empty_env : STLambdaTerm.Env Nat := fun v =>
  defaultValue v.type


-- Term: λx:ind. x
-- Type: ind → ind
def identity_fn_term : STLambdaTerm (arrow ind ind) :=
  abstraction x_ind (varTerm x_ind)

-- Interpretation:
def identity_fn_nat : Nat → Nat :=
  STLambdaTerm.toLeanFun identity_fn_term Nat empty_env

-- Let's test it:
#eval identity_fn_nat 5 -- Expected output: 5

#eval (varTerm x_ind).toLeanFun ℕ empty_env -- 0

-- Term: λf:(ind → ind). λx:ind. f (f x)
-- Type: (ind → ind) → (ind → ind)
def church_2_term : STLambdaTerm (arrow ind_to_ind ind_to_ind) :=
  abstraction f_ind_to_ind (
    abstraction x_ind (
      application
        (varTerm f_ind_to_ind)
        (application (varTerm f_ind_to_ind) (varTerm x_ind))
    )
  )

-- Interpretation (no free variables, so we can use an empty environment):
def church_2_nat : (Nat → Nat) → (Nat → Nat) :=
  STLambdaTerm.toLeanFun church_2_term Nat empty_env

-- Let's test it by giving it the successor function `Nat.succ` and the number 3.
-- The result should be Nat.succ(Nat.succ(3)).
#eval church_2_nat Nat.succ 3 -- Expected output: 5

-- Let's try another function, e.g., doubling.
def double (n:Nat) := n * 2
-- The result should be double(double(3)) = double(6) = 12.
#eval church_2_nat double 3 -- Expected output: 12
