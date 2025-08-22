import Mathlib.Data.Set.Basic

/-- A pointed ordered domain is a partially ordered set with distinguished
    bottom (⊥) and top (⊤) elements -/
structure PointedOrderedDomain where
  carrier : Type u
  le : carrier → carrier → Prop
  le_refl : ∀ x, le x x
  le_trans : ∀ x y z, le x y → le y z → le x z
  le_antisymm : ∀ x y, le x y → le y x → x = y
  bot : carrier
  top : carrier
  bot_le : ∀ x, le bot x
  le_top : ∀ x, le x top

-- Create instances for LE notation
instance {D : PointedOrderedDomain} : LE D.carrier where
  le := D.le

instance {D : PointedOrderedDomain} : Inhabited D.carrier where
  default := D.bot

/-- A plausibility space consists of:
    - W: a set of worlds
    - D: a pointed ordered domain
    - Pl: a plausibility measure mapping sets to D

    Axiom A1: If A ⊆ B, then Pl(A) ≤ Pl(B) -/
structure PlausibilitySpace where
  W : Type u                          -- Set of worlds
  D : PointedOrderedDomain           -- Domain of plausibility values
  Pl : Set W → D.carrier              -- Plausibility measure
  monotone : ∀ (A B : Set W), A ⊆ B → D.le (Pl A) (Pl B)  -- Axiom A1
  empty_bot : Pl ∅ = D.bot           -- Pl(∅) = ⊥
  univ_top : Pl Set.univ = D.top     -- Pl(W) = ⊤
