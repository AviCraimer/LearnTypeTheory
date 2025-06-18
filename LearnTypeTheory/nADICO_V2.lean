import Mathlib.Tactic

-- Formal Implementation of paper
-- nADICO: A Nested Grammar of Instituations
-- By Chistopher Frantz, Martin K. Purvis, Mariusz Nowostawski, Bastin Tony Roy Savarimuthu


-- I model the OrElse as a logical operation rather than a constituent of the data.

inductive Deontic
| may
| must
| mustNot




-- We similify by making the deontic mandatory, however since the values of Deontic include "may" we can still express situations without deontic constraints.
structure nADICData   (People Action Situation: Type )  where
  A : People -> Prop
  I : Action -> Prop
  C : Situation -> Prop
  D : Deontic


inductive nADICO (People Action Situation: Type )
-- Base case to wrap the nADIC data
| SIMPLE (S1: nADICData People Action Situation  )

-- Attach statements together with OrElse
| ORELSE (monitored consequence: nADICO People Action Situation )

-- Boolean operations
| AND (S1 S2: nADICO People Action Situation  )
| OR (S1 S2: nADICO People Action Situation )
| XOR  (S1 S2: nADICO People Action Situation )



-- Get the first statement at the head of a nested ORELSE statement
def nADICO.head  {People Action Situation: Type } (S1: nADICO People Action Situation ) : nADICO People Action Situation :=
  match S1 with
  | .ORELSE  monitored _  =>  monitored.head
  | _   => S1




-- Starting from a statement S1 which is ADIC, we can form a new statement which nests a statemet S2 under the O field of S1.
def  nADICO.verticalComposition  { People Action Situation : Type} (S1 : nADICO People Action Situation )(S2 : nADICO People Action Situation ) : nADICO People Action Situation  :=
  .ORELSE S1 S2



structure Event (People Action Situation: Type) where
  person: People
  action: Action
  situation: Situation

-- An event satisfies the three predicates in the AIC
def nADICO.isSatisfied {People Action Situation: Type} (n: nADICO People Action Situation )    (e: Event People Action Situation) :=

  let inner (n': nADICO People Action Situation ) :=
    match n' with
    | SIMPLE data => (data.A e.person ∧ data.I e.action ∧ data.C e.situation )
    | AND n1 n2 => n1.isSatisfied e ∧ n2.isSatisfied e
    | OR n1 n2 => n1.isSatisfied e ∨  n2.isSatisfied e
    | XOR n1 n2 => ¬ ((n1.isSatisfied e) ↔ (n2.isSatisfied e))
    | ORELSE n1 n2 =>
        n1.isSatisfied -- This goes up to the head. Do I want this or do I want to check that everything earlier in the chain is satisfied?
  inner n




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
