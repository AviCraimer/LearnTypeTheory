import Mathlib.Tactic

-- Formal Implementation of paper
-- nADICO: A Nested Grammar of Instituations
-- By Chistopher Frantz, Martin K. Purvis, Mariusz Nowostawski, Bastin Tony Roy Savarimuthu


-- I model the OrElse as a logical operation rather than a constituent of the data.

-- Personally, I don't see the point of distinguishing between "may" and "none" but they do this in the literature to I've maintained that in the type below.
inductive Deontic
| none
| may
| must
| mustNot
deriving Repr



-- We similify by making the deontic mandatory, however since the values of Deontic include "may" we can still express situations without deontic constraints.
structure nADICData (People Action Situation: Type )  where
  A : People -> Prop
  I : Action -> Prop
  C : Situation -> Prop
  D : Deontic


structure Event (People Action Situation: Type) where
  person: People
  action: Action
  situation: Situation

-- Statement is applicable to the event
def nADICData.isSatisfied {People Action Situation: Type } (data: nADICData People Action Situation) (e: Event People Action Situation ) : Prop :=
  data.A e.person ∧ data.I e.action ∧ data.C e.situation

inductive nADICO (People Action Situation: Type )
-- Base case to wrap the nADIC data
| SIMPLE (S1: nADICData People Action Situation )

-- Attach statements together with OrElse
| ORELSE (monitored consequence: nADICO People Action Situation )

-- Boolean operations
| BoolAND (S1 S2: nADICO People Action Situation  )
| BoolOR (S1 S2: nADICO People Action Situation )
| BoolXOR (S1 S2: nADICO People Action Situation )

open nADICO

-- We use the "O" lollypop for the relaton of a statement S1 to it's ORELSE clause S2, i.e.
infixr:60 "-O" =>  ORELSE
infixr:100 "&" =>  BoolAND
infixr:70 "OR" =>  BoolOR
infixr:70 "XOR" => BoolXOR






-- A statement being satisfied by and event e. It is clear enough how to interpret a statemetn being satsified by e, for all by ORELSE statements. For SIMPLE statements, we evaluate the conjunction of the three predicates.  This means that the specified criteria for applicability of the statement have been met. For AND OR and XOR we use standard boolean operations.

-- The tricky question is ORELSE.
-- Suppose we have ORELSE chain
  -- A :=  (S1 -O S2) -O S3
  -- B := S1 -O (S2 -O S3)
-- Naively, to know if A is satisifed you'd need to check if S1 -O S2 is satisfied. But does this mean that both S1 and S2 must be satisifed. If so, it would break associativity since then B might be satisfied and not A.
-- So we define the head of an ORELSE as the first in the chain. The whole ORELSE statement is satisfied if the head is satified.
-- If we evaluate A this way, we take the head which is (S1 -O S2) and if it is satisfied, and then since it is also ORELSE we must take the head againt to evalutate if S1 is satisfied. If we look at B, we go directly to S1, so the result is the same, which should presever associativity.

-- But even determining the head is complicated by composition.
-- Suppose we have
-- ( (S1 -O S2) & (S3 -O S4) ) -O S5
  -- We could say that ( (S1 -O S2) & (S3 -O S4) ) is the head since it is the head of ORELSE chain starting from the main connective. However, I hope to show there is an isomorphism (S1 -O S2) & (S3 -O S4) ≅ (S1 & S3) -O (S3 & S4) in which case it could make sense to regard the "initial statement" in our original as (S1 & S3)

-- Get the first statement at the head of a nested ORELSE statement - As noted this may not enough. I'll leave it for now until I work out the distribution and normal forms.
def nADICO.head  {People Action Situation: Type } (S1: nADICO People Action Situation ) : nADICO People Action Situation :=
  match S1 with
  | .ORELSE  monitored _  =>  monitored.head
  | _   => S1


-- An event satisfies the three predicates in the AIC
def nADICO.isSatisfied {People Action Situation: Type} (n: nADICO People Action Situation )    (e: Event People Action Situation) :=
    match n with
    | SIMPLE data => data.isSatisfied e
    | n1 & n2 => n1.isSatisfied e ∧ n2.isSatisfied e
    | n1 OR n2 => n1.isSatisfied e ∨  n2.isSatisfied e
    | n1 XOR n2 => ¬ ((n1.isSatisfied e) ↔ (n2.isSatisfied e))
    | monitored -O _ => monitored.isSatisfied e



-- A statement is followed if the deontic is upheld in the apprirate way. It is trivially followed if there is no deontic or if the deontic is may.
def nADICO.isFollowed {People Action Situation: Type} (n: nADICO People Action Situation ) (e: Event People Action Situation) :=
  match n with
    | SIMPLE data =>
      match data.D with
      | .none => True
      | .may => True
      | .must => data.isSatisfied e
      | .mustNot => ¬ data.isSatisfied e
    | n1 &  n2 => n1.isFollowed e ∧ n2.isFollowed e
    | n1 OR n2 => n1.isFollowed e ∨  n2.isFollowed e
    | n1 XOR n2 => ¬ ((n1.isFollowed e) ↔ (n2.isFollowed e))
    | monitored -O _ => monitored.isFollowed e


@[simp] -- A statement is violated if it is not followed.
def nADICO.isViolated {People Action Situation: Type} (n: nADICO People Action Situation ) (e: Event People Action Situation) := ¬ n.isFollowed e


-- Two statements are equivalent under satisfaction when they satisfy all and only the same events.
def nADICO.equivSatisfied  {People Action Situation: Type}  (n1 n2: nADICO People Action Situation)  :=
  ∀ (e: Event People Action Situation ), n1.isSatisfied e ↔ n2.isSatisfied e

-- Two statements are equivalent under following when they are followed for all and only the same events.
def nADICO.equivFollowed  {People Action Situation: Type}  (n1 n2: nADICO People Action Situation)  :=
  ∀ (e: Event People Action Situation ), n1.isFollowed  e ↔ n2.isFollowed e

def nADICO.equivViolated  {People Action Situation: Type}  (n1 n2: nADICO People Action Situation)  :=
  ∀ (e: Event People Action Situation ), n1.isViolated  e ↔ n2.isViolated e

lemma nADICO.equiv_followed_imp_equiv_violated {People Action Situation: Type}  (n1 n2: nADICO People Action Situation)  (h: n1.equivFollowed n2)
  : ∀ (e: Event People Action Situation ), n1.isViolated e ↔ n2.isViolated e := by
  simp
  intro e
  have h1 := h e
  simp_all only

lemma nADICO.equiv_followed_imp_equiv_satisfied {People Action Situation: Type}  (n1 n2: nADICO People Action Situation)  (h: n1.equivFollowed n2) : n1.equivSatisfied n2 := by
  intro e
  have h_e := h e
  constructor
  · intro eSat



  · sorry



lemma forall_iff_iff_neg  {α β  : Type}{P : α → β → Prop} (a1 a2: α )  :  (∀(b: β  ), (P a1 b  ↔ P a2 b)) ↔ (∀(b: β  ), ( ¬ P a1 b  ↔ ¬ P a2 b)) := by
  constructor
  all_goals (intro h b ; have hb := h b ; tauto )

lemma nADICO.followed_equiv_eq_violated_equiv {People Action Situation: Type} (n1 n2: nADICO People Action Situation)  :  n1.equivFollowed n2 = n1.equivViolated n2 := by
  simp [equivViolated, equivFollowed]
  apply forall_iff_iff_neg

lemma nADICO.orelse_and_distrib1 {People Action Situation: Type}  (s1 s2 s3: nADICO People Action Situation)  :  (s1 -O (s2 & s3)).equivFollowed ((s1 -O s2) & (s1 -O s3))  := by
  simp_all [equivFollowed, isFollowed]

lemma nADICO.orelse_and_distrib2 {People Action Situation: Type}  (s1 s2 s3: nADICO People Action Situation)  :  ((s1 & s2) -O  s3).equivFollowed ((s1 -O s3) & (s2 -O s3))  := by
  simp_all [equivFollowed, isFollowed]


lemma nADICO.orelse_and_distrib3 {People Action Situation: Type}  (s1 s2 s3 s4: nADICO People Action Situation)  :  ((s1 -O s2) & (s3 -O s4)).equivFollowed ((s1 & s3) -O (s3 & s4))  := by
  simp_all [equivFollowed, isFollowed]

lemma orelse_assoc  {People Action Situation: Type}  (s1 s2 s3:   nADICO People Action Situation) :
  ((s1 -O s2) -O s3).equivFollowed  (s1 -O (s2 -O s3))  := by
  simp [equivFollowed, isFollowed]


---
-- Borneo Example

inductive  BPerson  where
| farmer
| govWorker
open BPerson

inductive  BAction where
-- Farmers
| overhavest
| plantDurian
| leaveForrest
| plantPalmOil

-- Gov Workers
| giveCarbonCredit
open BAction

inductive  BSituation where
| everywhereAlways
| havestSeason
| drought
| flooding
| durianYield (percentChange: Float) -- negative unit interval for decrease positive for increase
| landDegredation
| increasedIncome
| event (e: Event BPerson BAction BSituation)

open BSituation
open Deontic
def BorneoData := nADICData BPerson BAction BSituation
def Borneo := nADICO BPerson BAction BSituation
def BorneoEvent := Event BPerson BAction BSituation

def decreasingThreshold : Float := -0.2

def isFarmer (p: BPerson) := p = farmer
def isGovWorker  (p: BPerson) := p = govWorker

def forrestEvent : BorneoEvent := {
  person:= farmer,
  action:= leaveForrest,
  situation:= everywhereAlways
}

-- If there are decreasing durian yeilds, a farmer may plant palm oil
def palmOilStrategy : BorneoData := {
  A  := isFarmer,
  I (a: BAction) := a = plantPalmOil,
  C (s: BSituation) :  Prop := ∃ (f: Float), s = durianYield f  ∧ f ≤ decreasingThreshold
  D := none  -- It's not a norm, but a strategy
}


-- If your neighbor plants palm oil, your land becomes degraded, and you might decide to plant palm oil

-- A gov worker must gives carbon credit for leaving forrest stable.
def govCarbonCredit : BorneoData := {
  A  := isGovWorker,
  I (a: BAction) := a = giveCarbonCredit,
  C (s: BSituation) :  Prop := s = event forrestEvent
  D := must
}


-- Yeild for given farmer increases if all neighbors are planting durian or leave forrest. (less)
