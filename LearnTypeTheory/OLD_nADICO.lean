import Mathlib.Tactic

-- Formal Implementation of paper
-- nADICO: A Nested Grammar of Instituations
-- By Chistopher Frantz, Martin K. Purvis, Mariusz Nowostawski, Bastin Tony Roy Savarimuthu

inductive Deontic
| may
| must
| mustNot


inductive LogicOp (α : Type)  where
| SIMPLE (S1: α  )
| AND (S1 S2: α  )
| OR (S1 S2: α )
| XOR  (S1 S2: α )

mutual

-- We define DO together to ensure you cannot have O without D.
structure DO  (People Action Situation: Type )  where
  D: Deontic
  O: Option (LogicOp (nADICO People Action Situation))

structure nADICO   (People Action Situation: Type )  where
  A : People -> Prop
  I : Action -> Prop
  C : Situation -> Prop
  DO : Option (DO People Action Situation )
end



variable { People Action Situation : Type}

variable (S1 S2 S3 : nADICO People Action Situation )


@[simp]
def isAIC   (s: nADICO People Action Situation) : Prop :=  s.DO = none

-- What Ostrom terms a Shared Strategy
def AIC (People Action Situation: Type) := { s : nADICO People Action Situation | isAIC  s }

-- What original paper terms "A Norm" but Frantz et al revise this terminology so we'll just call it ADIC
@[simp]
def isADIC (n: nADICO People Action Situation) : Prop :=  (∃ (DOVal : DO People Action Situation),  n.DO = some DOVal   ∧  DOVal.O = none)

def ADIC (People Action Situation: Type) := { n : nADICO People Action Situation | isADIC n }

-- What the original paper calls "A Rule" but Frantz et al argue can be a norm or a rule. We call it ADICOFull to distinguish from nADICO which is the type that includes all variants.
@[simp]
def isADICOFull  (r: nADICO People Action Situation) : Prop :=
  (∃ (DOVal : DO People Action Situation),  r.DO = some DOVal  ∧
    (∃ (s: LogicOp (nADICO People Action Situation)),  DOVal.O = some s))

def ADICOFull (People Action Situation: Type) := { r : nADICO People Action Situation | isADICOFull  r }

-- Starting from a statement S1 which is ADIC, we can form a new statement which nests a statemet S2 under the O field of S1.
def verticalComposition (_: isADIC S1)(nS2 : LogicOp (nADICO People Action Situation)  ) : nADICO People Action Situation :=
  match S1.DO with
  | none => by
    exact S1 -- Returning this satisfies the type checker but it cannot happen since S1 is ADIC and thus has a non-none value for DO.
  | some DOVal  => {
    S1 with
    DO :=  some {D:= DOVal.D,  O:= some nS2}
  }

structure Event (People Action Situation: Type) where
  person: People
  action: Action
  situation: Situation

@[simp]
def Event' := Event People Action Situation

-- An event satisfies the three predicates in the AIC
def nADICO.isSatisfied {People Action Situation: Type} (n: nADICO People Action Situation ) (e: Event People Action Situation) := (n.A e.person ∧ n.I e.action ∧ n.C e.situation )

-- A statement is followed if the deontic is upheld in the apprirate way. It is trivially followed if there is no deontic or if the deontic is may.
def nADICO.isFollowed {People Action Situation: Type} (n: nADICO People Action Situation ) (e: Event People Action Situation) := match n.DO with
  | none => True -- Is trivially followed when there is no deontic
  | some DOVal => match DOVal.D with
    | .may => True -- Is trivially followed as "may" is permissive
    | .must => n.isSatisfied e
    | .mustNot => ¬ n.isSatisfied e


@[simp] -- A statement is violated if it is not followed.
def nADICO.isViolated {People Action Situation: Type} (n: nADICO People Action Situation ) (e: Event People Action Situation) := ¬ isFollowed n e



-- Define equivalence of

-- To define algebraic relationships we want to consider algebraic terms to be inside the type logic op. Note that we have a full copy of nADICO via the SIMPLE LogicOp constructor.
abbrev nADICOTerm (People Action Situation : Type) :=  LogicOp (nADICO People Action Situation)

def nADICOTerm.isSatisfied {People Action Situation: Type} (n: nADICOTerm People Action Situation ) (e: Event People Action Situation) :=
match n with
  | .SIMPLE n' => n'.isSatisfied e
  | .AND n1 n2 => n1.isSatisfied e ∧ n2.isSatisfied e
  | .OR n1 n2 => n1.isSatisfied e ∨  n2.isSatisfied e
  | .XOR n1 n2 => ¬ ((n1.isSatisfied e) ↔ (n2.isSatisfied e))


def nADICOTerm.isFollowed  {People Action Situation: Type} (n: nADICOTerm People Action Situation ) (e: Event People Action Situation) :=
match n with
  | .SIMPLE n' => n'.isFollowed  e
  | .AND n1 n2 => n1.isFollowed e ∧ n2.isFollowed e
  | .OR n1 n2 => n1.isFollowed e ∨  n2.isFollowed e
  | .XOR n1 n2 => ¬ ((n1.isFollowed e) ↔ (n2.isFollowed e))

@[simp]
def nADICOTerm.isViolated  {People Action Situation: Type} (n: nADICOTerm People Action Situation ) (e: Event People Action Situation) := ¬ n.isFollowed e


def nADICOTerm.equivSatisfied  {People Action Situation: Type} (n1: nADICOTerm People Action Situation )(n2: nADICOTerm People Action Situation )  := ∀ (e: Event People Action Situation ), n1.isSatisfied e ↔ n2.isSatisfied e


def nADICOTerm.equivFollowed  {People Action Situation: Type} (n1: nADICOTerm People Action Situation )(n2: nADICOTerm People Action Situation )  := ∀ (e: Event People Action Situation ), n1.isFollowed  e ↔ n2.isFollowed e

lemma nADICOTerm.equiv_followed_imp_equiv_violated {People Action Situation: Type} (n1: nADICOTerm People Action Situation )(n2: nADICOTerm People Action Situation )  (h: n1.equivFollowed n2) :∀ (e: Event People Action Situation ), n1.isViolated e ↔ n2.isViolated e := by
  simp
  intro e
  have h1 := h e
  simp_all only

lemma nADICOTerm.equiv_followed_imp_equiv_satisfied {People Action Situation: Type} (n1: nADICOTerm People Action Situation )(n2: nADICOTerm People Action Situation )  (h: n1.equivFollowed n2) : n1.equivSatisfied n2 := by
  intro e
  have h1 := h e
  simp_all [isFollowed, nADICO.isFollowed, isSatisfied, nADICO.isSatisfied]
  constructor
  · intro eSat
    sorry -- Think I need to use cases or induction on n1.

  · sorry


-- Possible algebraic laws

-- if ⟫ is for vertical comp
-- S2 ⟫ (S2 ∧ S3) ≃ (S1 ⟫ S2) ∧ (S1 ∧ S3)
