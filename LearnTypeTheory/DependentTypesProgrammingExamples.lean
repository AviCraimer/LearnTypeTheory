import Mathlib.Tactic

inductive LiftProp : Prop -> Type where
| lift {p: Prop} (h: p) : LiftProp p

@[simp]
def String.tagToType (tag : String ) : Type :=
  match tag with
  | "Nat" => ℕ
  | "String" => String
  | "Bool" => Bool
  | _ => Empty

def TaggedValue := Σ (tag: String), tag.tagToType

def Nat.tagged (n: ℕ) : TaggedValue  := ⟨"Nat", n ⟩
def String.tagged (str: String) : TaggedValue  := ⟨"String", str ⟩
def Bool.tagged (b: Bool) : TaggedValue  := ⟨"Bool", b ⟩


def other_tagged!  : TaggedValue  := ⟨"other", true   ⟩ -- Error since the type of the second place is Empty no pair with a non-tag string can be constructed

-- Parsing
def natTaggedTuple (n: ℕ) : ℕ × String :=  (n, "Nat")
def stringTaggedTuple (str: String) : String × String :=  (str, "String")
def boolTaggedTuple (b: Bool ) : Bool × String :=  (b, "Bool")



def parseTagged {α : Type}
  (pair: α × String)
  (h: Option (LiftProp (α = pair.2.tagToType) ) := none ) : Option  pair.2.tagToType :=
 match h with
 | some (.lift h) =>
    match pair with
    | (n, "Nat") => some (h ▸ n)
    | (s, "String") => some (h ▸ s)
    | (b, "Bool") => some (h ▸ b)
    | _ => none
 | none  => none


def wrapProof {p:Prop} (h: p) : Option (LiftProp p) := (some (LiftProp.lift h ))

#eval parseTagged (4, "Nat") (wrapProof rfl)
#eval parseTagged (4, "cat")
#eval parseTagged ("Dog", "String") (wrapProof rfl)
#eval parseTagged ("Dog", "Nat")
