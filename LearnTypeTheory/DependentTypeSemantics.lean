import Mathlib.Tactic

universe u v
-- We lift propositions to Type to avoid Lean's built-in proof irrelevance for propositions. This is only for demonstration purposes to show how Sigma types work.
inductive LiftProp (p : Prop) : Type where
  | liftProp (h : p) : LiftProp p
deriving Repr
open LiftProp
def LiftProp.proof {p:Prop}(lifted: LiftProp p) := match lifted with | liftProp  h => h

inductive Material
  | cardboard (uid: String)
  | newsprint (uid: String)
  | ink (uid: String)
  | metal (uid: String)
deriving Repr
open Material

-- This is our type returing function B
@[simp]
def isCardBoard (c : Material) : Type :=
  LiftProp (∃ uid, cardboard uid = c)

-- Using Sigma types for sub-typing
def Cardboard := Σ(c: Material), (isCardBoard c)

-- Example Cardboard
def cardstockMaterial : Material := cardboard "some cardstock"

-- We prove that cardstock material is cardboard
def cardstockIsCardboardProof : isCardBoard cardstockMaterial := by
  simp
  constructor
  · use "some cardstock"
    rfl

-- The first element of the pair is the material, and the second element is a proof that the material is cardboard.
def cardstockIsCardboard : Cardboard := ⟨cardboard "some cardstock", cardstockIsCardboardProof  ⟩

#eval cardstockIsCardboard
-- First and second projections
#eval  cardstockIsCardboard.1 -- material
#eval  cardstockIsCardboard.2 -- proof



inductive CardSuit
  | hearts
  | diamonds
  | clubs
  | spades
deriving Repr, DecidableEq
open CardSuit

inductive CardRank
  | ace
  | two
  | three
  | four
  | five
  | six
  | seven
  | eight
  | nine
  | ten
  | jack
  | queen
  | king
deriving Repr, DecidableEq
open CardRank


-- ROLES / FUCTIONS
inductive PlayingCard
  | card (r: CardRank)(s: CardSuit)
deriving Repr, DecidableEq
open PlayingCard

def PlayingCard.rank (c: PlayingCard) :=
match c with | card r _ => r
def PlayingCard.suit (c: PlayingCard) :=
match c with | card _ s => s


-- Subtyping
def Queen := Σ (c: PlayingCard), LiftProp (c.rank = queen)
def HeartsCard := Σ (c: PlayingCard), LiftProp (c.suit = hearts)

-- Combining subtypes
-- This is our B function that returns a Type
@[simp]
def isQueenOfHearts  (queen: Queen)(hearts: HeartsCard)  : Type  := LiftProp (hearts.1 = queen.1)

-- Non-dependent pair
def QueenHeartsPair := Σ (_:Queen), HeartsCard

def QueenOfHearts := Σ(qh: QueenHeartsPair), isQueenOfHearts qh.1 qh.2

def qh : PlayingCard := card queen hearts

def qhIsQueen : Queen := ⟨qh, liftProp (by rfl) ⟩
def qhIsHearts : HeartsCard := ⟨qh, liftProp (by rfl) ⟩


def qhIsQueenOfHearts : QueenOfHearts := ⟨⟨qhIsQueen, qhIsHearts ⟩, (by  simp; constructor ; rfl  ) ⟩


-- One way to represent the Role Type for material as Queen.
def CardboardAsQueen := Σ (_:Cardboard), QueenOfHearts
-- Note since we dont use the _: Material in the second place, this is actually a non-dependent pair.

def cardstockAsQh : CardboardAsQueen := ⟨cardstockIsCardboard, qhIsQueenOfHearts ⟩

#eval cardstockAsQh.1.1

-- snd for queen of hearts, then first for the first in the queen/hearts pait, then first for the qhIsQueen
#eval cardstockAsQh.2.1.1 -- as queen
#eval cardstockAsQh.2.1.2 -- as hearts
#eval cardstockAsQh.2.1.1.1 -- Raw card
#eval cardstockAsQh.2.1.2.1 = cardstockAsQh.2.1.1.1 -- raw cards are the same





---
