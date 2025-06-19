import LearnTypeTheory.ADICO
import Mathlib.Tactic

---
-- Borneo Example

inductive  BPerson  where
| farmer
| govWorker
open BPerson

inductive  BAction where
| undergoes

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
| changeInIncome (percentChange: Float)

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

open nADICO



def palmOilStrategy (yield: Float) : BorneoData := {
  A  := isFarmer,
  I (a: BAction) := a = plantPalmOil,
  C (s: BSituation) :  Prop :=  s = durianYield yield  ∧ yield ≤ decreasingThreshold
  D := must
}

-- If there are decreasing durian yeilds a farmer must plant palm oil, or else the farmer undergoes a negative change in income proportional to the decrease in yield.
def palmOilStatment (yield: Float) (_: yield ≤ decreasingThreshold) : Borneo :=  (SIMPLE (palmOilStrategy yield)) -O (EVENT ({
  person:= farmer,
  action:= undergoes,
  situation:= changeInIncome yield
}))


-- If your neighbor plants palm oil, your land becomes degraded, and you might decide to plant palm oil

-- A gov worker must gives carbon credit for leaving forrest stable.
def govCarbonCredit : BorneoData := {
  A  := isGovWorker,
  I (a: BAction) := a = giveCarbonCredit,
  C (s: BSituation) :  Prop := s = event forrestEvent
  D := must
}


-- Yeild for given farmer increases if all neighbors are planting durian or leave forrest. (less)
