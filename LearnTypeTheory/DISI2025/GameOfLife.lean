import Mathlib.Tactic
universe u v

class Comonad (W : Type u → Type u) extends Functor W where
  -- operations
  extract            : {α : Type u} → W α → α
  duplicate          : {α : Type u} → W α → W (W α)
  -- axioms
  extract_duplicate  : ∀ {α} (x : W α),        extract (duplicate x) = x
  duplicate_extract  : ∀ {α} (x : W α),
                        Functor.map extract (duplicate x) = x
  duplicate_duplicate :
    ∀ {α} (x : W α),
      duplicate (duplicate x) =
        Functor.map duplicate (duplicate x)

namespace Comonad

/-- “Extend” is definable from `duplicate` and `map`. -/
@[simp] def extend {W : Type u → Type u} [c : Comonad W]
    {α β : Type u} (f : W α → β) (x : W α) : W β :=
  Functor.map f (Comonad.duplicate x)
end Comonad

instance : Comonad Id where
  extract            := id
  duplicate          := id
  extract_duplicate  := by intro α x; rfl
  duplicate_extract  := by intro α x; rfl
  duplicate_duplicate := by intro α x; rfl

/-- Environment comonad `σ × _`. -/
instance {σ : Type u} : Comonad (fun α => σ × α) where
  extract             := Prod.snd
  duplicate           := fun ⟨e,a⟩ => (e, (e,a))
  map           {α β : Type u}  (f: α → β)  := fun ⟨e,a⟩ => (e, f a)
  extract_duplicate   := by intro α ⟨e,a⟩; rfl
  duplicate_extract   := by intro α ⟨e,a⟩; rfl
  duplicate_duplicate := by intro α ⟨e,a⟩; rfl

/-- A (possibly infinite) grid of values with a current focus. -/
structure Store (S : Type u) (α  : Type u) : Type u where
  peek : S → α
  focus  : S

instance Store.FunctorInst {S  : Type u} : Functor (Store S) where
  map f store := { store with peek := f ∘ store.peek }

instance Store.ComonadInst {S  : Type u} : Comonad (Store S) where
  extract   := fun store => store.peek store.focus
  duplicate := fun store =>
    {
      peek  := fun s' => { store with focus := s' },
      focus  := store.focus
    }
  -- proofs
  extract_duplicate := by
    intro α store; rfl
  duplicate_extract := by
    intro α store; rfl
  duplicate_duplicate := by
    intro α store; rfl

def Point := ℤ × ℤ
deriving BEq

inductive State
| alive
| dead
deriving BEq

open Comonad
abbrev Board : Type := Store Point State


-- Is this a coalgebra?
def neighbourhood : Point → List Point
  | (x,y) => [ (x-1,y-1), (x,y-1), (x+1,y-1),
               (x-1,y  ),           (x+1,y  ),
               (x-1,y+1), (x,y+1), (x+1,y+1) ]



open State

-- Conway Rules
-- Any live cell with fewer than two live neighbours dies, as if by underpopulation.
-- Any live cell with two or three live neighbours lives on to the next generation.
-- Any live cell with more than three live neighbours dies, as if by overpopulation.
-- Any dead cell with exactly three live neighbours becomes a live cell, as if by reproduction.
def nextCell (b : Board) : State :=
  let neighbours : List Point := (neighbourhood b.focus)
  let neighboursState : List State := neighbours.map (fun (p) => b.peek p)
  let liveCount :ℕ  := neighboursState.count alive
  match extract b with
  | State.alive => if liveCount = 2 || liveCount = 3 then dead else alive
  | State.dead  => if liveCount = 3 then alive else dead
