import LearnTypeTheory.ADICO
import Mathlib.Tactic

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
