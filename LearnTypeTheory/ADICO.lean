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
open Deontic


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
| EVENT (e: Event People Action Situation)
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
-- For ORELSE to check if S1 -O S2 is satisfied, you only need to check if the monitored statement (S1) is satisfied.
def nADICO.isSatisfied {People Action Situation: Type} (n: nADICO People Action Situation )    (e: Event People Action Situation) :=
    match n with
    | SIMPLE data => data.isSatisfied e
    | EVENT e' => e = e'
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
    | EVENT e' => (EVENT e').isSatisfied e
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




@[simp]
def nADICO.isSimple  {People Action Situation: Type}  (n1: nADICO People Action Situation)  :=
  ∃ (x: nADICData People Action Situation), n1 =  SIMPLE x

@[simp]
def nADICO.hasDeontic   {People Action Situation: Type}  (n1: nADICO People Action Situation) (deontic: Deontic)  :=
  ∃ (x: nADICData People Action Situation), x.D = deontic ∧  n1 = SIMPLE x

-- lemma must_imp_must {People Action Situation: Type}  (n1 n2: nADICO People Action Situation) (hEquiv: n1.equivFollowed n2) (h1: n1.hasDeontic must) (h2: n2.isSimple) :   n2.hasDeontic must := by
--   simp_all
--   obtain ⟨data1, data1Must, data1Simple ⟩ := h1
--   obtain ⟨data2, data2Simple  ⟩ := h2
--   rw [data2Simple]
--   use data1
--   constructor
--   · exact data1Must
--   · sorry

--   induction n2 with
--     | SIMPLE data =>

--        have h2 (dataMust : data.D = Deontic.must):  (SIMPLE data).isSatisfied e ↔ n2.isSatisfied e := by
--         simp_all [nADICO.isSatisfied]
--         simp [isFollowed] at h_e
--         rw [dataMust] at h_e
--         simp at h_e




--     | ORELSE _  _ => sorry
--     | BoolAND _  _ => sorry
--     | BoolOR _  _ => sorry
--     | BoolXOR _  _ => sorry



-- Informal argument:
-- s1.equivFollowed s2 where s1 and s2 are simple statements, means that all simple statements with the must deontic are satisfied iff they are followed.
-- This is is enough to show
-- lemma nADICO.equiv_followed_imp_equiv_satisfied {People Action Situation: Type}  (n1 n2: nADICO People Action Situation) (h1: n1.isSimple )(h2: n2.isSimple )   (h: n1.equivFollowed n2) : n1.equivSatisfied n2 := by
--   intro e
--   have h_e := h e
--   induction n1 with
--     | SIMPLE data =>

--        have h2 (dataMust : data.D = Deontic.must):  (SIMPLE data).isSatisfied e ↔ n2.isSatisfied e := by
--         simp_all [nADICO.isSatisfied]
--         simp [isFollowed] at h_e
--         rw [dataMust] at h_e
--         simp at h_e




--     | ORELSE _  _ => sorry
--     | BoolAND _  _ => sorry
--     | BoolOR _  _ => sorry
--     | BoolXOR _  _ => sorry

--   constructor
--   · intro eSat
--     induction n1 with
--     | SIMPLE data =>

--        have h4: data.D = Deontic.must →
--     | ORELSE _  _ => sorry
--     | BoolAND _  _ => sorry
--     | BoolOR _  _ => sorry
--     | BoolXOR _  _ => sorry


lemma nADICO.equiv_followed_imp_equiv_satisfied {People Action Situation: Type}  (n1 n2: nADICO People Action Situation)  (h: n1.equivFollowed n2) : n1.equivSatisfied n2 := by sorry


-- lemma nADICO.equiv_followed_imp_equiv_satisfied {People Action Situation: Type}  (n1 n2: nADICO People Action Situation)  (h: n1.equivFollowed n2) : n1.equivSatisfied n2 := by
--   intro e
--   have h_e := h e
--   constructor
--   · intro eSat
--     have h2 := h_e.mp
--     by_cases h: n1.isFollowed e
--     · have h3 := h_e.mp h

--     .



--   · sorry



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
