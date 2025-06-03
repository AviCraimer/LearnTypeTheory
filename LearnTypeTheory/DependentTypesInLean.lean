
universe u v
open Lean


#check Type 2

def foo1 : Type (max 0 1) :=  Type 0 -> Bool
#check foo1

def foo2 := Bool -> Type 0
#check foo2

#check List



-- Add syntax for Pi type notation.
syntax:10 "Π" "(" ident (":" term) ")" "," term : term
macro_rules
  | `(Π ($param : $ty), $domain) => `(($param : $ty) → $domain)




-- Takes a natural number n and a type and returns the type of products of that type to the power n
@[simp]
def getPowerType (dimension:Nat) (α : Type u): Type u :=
  match dimension with
  | 1 => α -- We match 1 before zero to avoid adding the unit to every product type!
  | 0 => PUnit -- This case will only get triggered if zero is passed in non-recursively. This is mathematically sound since the product of zero arguments is the unit type.
  | n + 1 =>  α × (getPowerType n α) -- This case is triggered when we pass in a number greater than 1.

def Point3D := getPowerType 3 Float

#check Point3D
def f1: Float := 3.5

def testPoint1 : Float × Float × Float := (f1,f1, f1)
def testPoint2 : getPowerType 3 Float := (f1,f1, f1)
def testPoint4 : Point3D := (f1,f1,f1)

-- Dependent Sum  -- Dependent Pair

-- (a,b) : A x B

-- B: A -> Type

-- Σ (a:A), B a
-- ( a:Nat , _)
-- (3, b: B 3  )

-- Nat × Float
-- (3, 4.5)
def F (_:Nat) := Float
def NatFloatPair := Σ (n:Nat), F n
def NatFloatProduct := Nat × Float
def testnatfloat : NatFloatPair  := ⟨234234, (3.5:Float) ⟩


-- Using sigma types, we can avoid specifying the dimension of the vector as we did with Point3D. This gives us a type of ALL Float valued vectors.
def FloatVector  := Σ (n:Nat),  getPowerType n Float

def testPoint1b : FloatVector := ⟨3, testPoint1⟩

-- We get a type error if the number that is first in the pair does not match the dimension of the value in the second of the pair. e.g.,
-- def testPoint2b : FloatVector := ⟨4, testPoint1⟩ -- error!

-- However, we have still restricted our type to Float values. Can we define a type that encompases all possible types which the function getPowerType generates?

-- Yes, we simply add a nested Sigma pair with the type provided.
def Vect := Σ (n: Nat),( Σ (α : Type u), (getPowerType n α))

-- Compare these three ways to define the type for the value (1,2,3)

-- First we explicitly define the product type
def natTuple3DExplicit: Nat × Nat × Nat := (1,2,3)

-- Here we use a function that returns a type, the parameters are in the type signature
def NatTupel3D: getPowerType 3 Nat := natTuple3DExplicit

-- Finally, we use our Sigma type, now the parameters have moved from the type to the value
def NatVector3D : Vect := ⟨3, ⟨ Nat, natTuple3DExplicit ⟩  ⟩

-- So we see that the Sigma type constructor lets us take type constructor parameters out of our types and bring them into the value level.

---

-- Pi Types: Dependent Functions

-- Pi types give us dependent functions
-- where the return type can depend on the input value.

-- B: (a:A) -> Type
-- Π (x:A), B x
-- A -> B
-- (Π (x:Nat), (B x: Type)) : Type

-- Π : (B:A ->Type) -> Type

-- D -> Bool

-- Σ B
-- Π B

-- T0, T1, T2, T3, ...
-- f(0) => t0:T0
-- f(1) => t1:T1
-- f(3) => t3:T3

-- Dependent function that returns Float a vector filled with a single value :

@[simp]
theorem getPowerType.equals {α : Type u} {n: Nat} : (α × getPowerType n α) = (getPowerType (n + 1) α)  := by
  unfold getPowerType
  sorry


@[simp]
def fillFloatVector
  : Π (dimension: Nat),  Float → getPowerType dimension Float :=
  fun d  =>
  match d with
    | 1 => fun value =>  value
    | 0 => fun _ => PUnit.unit
    | n + 1 => fun value => (value, fillFloatVector n value)

-- Notice that our Π function returns a non-dependent function type. We can tell it is non-dependent because there is no parameter in the type signature for the Float argument. On the other hand, we use the value-level paremater "dimension" in the type signature to define the return type fo the non-dependent function.

#eval! fillFloatVector 3 (4.5: Float) -- (4.5, 4.5, 4.5): Float x Float x Float
#eval! fillFloatVector 5 (4.5: Float) -- (4.5, 4.5, 4.5, 4.5, 4.5) : Float^5






-- Notice how the return type changes based on the input:
#eval makeFloatVector 1 4.0  -- Float
#check makeFloatVector 2  -- Float × Float
#check makeFloatVector 3  -- Float × Float × Float

-- We can also create functions that work with our Sigma types:
def getVectorDimension : FloatVector → Nat :=
  fun v => v.1  -- Extract the first component (the dimension)

def extractVector : Π (v: FloatVector), getPowerType v.1 Float :=
  fun v => v.2  -- The return type depends on v's dimension!

-- Let's create a more interesting example - a function that creates identity matrices:
def makeIdentityVector : Π (n: Nat), getPowerType n Nat :=
  fun n => match n with
  | 0 => PUnit.unit
  | 1 => 1
  | n + 1 => (1, makeZeroVector n)
where makeZeroVector : Π (n: Nat), getPowerType n Nat :=
  fun n => match n with
  | 0 => PUnit.unit
  | 1 => 0
  | n + 1 => (0, makeZeroVector n)

-- The beautiful duality: Sigma types are to Pi types as pairs are to functions
-- Sigma packages dependent data, Pi consumes dependent data

-- We can even create functions that transform vectors of any type:
def mapVector : Π (n: Nat), Π (α β: Type u), (α → β) → getPowerType n α → getPowerType n β :=
  fun n α β f => match n with
  | 0 => fun _ => PUnit.unit
  | 1 => f
  | n + 1 => fun v => (f v.1, mapVector n α β f v.2)

-- Using our generic Vect type, we can write truly polymorphic operations:
def getVectLength : Vect → Nat :=
  fun v => v.1

def doubleNatVector : Π (v: Vect), v.2.1 = Nat → Vect :=
  fun v _ => ⟨v.1, ⟨Nat, mapVector v.1 Nat Nat (· * 2) v.2.2⟩⟩

-- Notice how Pi types allow us to express constraints and dependencies in the type system
-- The function doubleNatVector can only be called on Vect values whose type component is Nat

-- Compare these type signatures:
-- Non-dependent: Nat → Float  (all inputs map to Float)
-- Dependent: Π (n: Nat), getPowerType n Float  (each input n maps to a different type)

-- This shows the key insight: Pi types generalize function types by allowing the
-- output type to vary based on the input value, just as Sigma types generalize
-- product types by allowing the second component's type to depend on the first.


---
