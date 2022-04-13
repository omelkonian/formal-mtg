module Types where

open import Agda.Primitive using () renaming (Set to Type)
open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Semigroup
import Prelude.Maps.Concrete as M
open import Prelude.Maps.Concrete
import Prelude.Sets.Concrete as S
open import Prelude.Sets.Concrete

data Colour : Type where
  Red Green White Blue Black : Colour
unquoteDecl DecEq-Colour = DERIVE DecEq [ quote Colour , DecEq-Colour ]

-- Colour⁇ = Maybe Colour

pattern colorless = nothing
pattern colored x = just x
pattern R = colored Red
pattern G = colored Green
pattern W = colored White
pattern U = colored Blue
pattern B = colored Black
pattern C = colorless

Mana = Map⟨ Maybe Colour ↦ ℕ ⟩
ManaPool = Mana
ManaCost = Mana
CardCost = Set⁺⟨ ManaCost ⟩
ManaCostChoices = Map⟨ Set⟨ Maybe Colour ⟩ ↦ ℕ ⟩
private
  instance _ = Semigroup-ℕ-+

  m : Mana
  m = M.singleton (C , 2)
    ◇ M.singleton (W , 2)

  m′ : Mana
  m′ = M.singleton (C , 4)
     ◇ M.singleton (W , 2)

  -- _ : m ◇ M.singleton (C , 2) ≡ m′
  -- _ = ?

  _ : ManaPool
  _ = M.singleton (C , 2)
    ◇ M.singleton (W , 2)
    ◇ M.singleton (R , 1)

  -- 1BBB = ManaCost -- 1BBB
  --   ∋ singletonᵐ (C , 1) ∪ᵐ singletonᵐ (B , 3)
  -- 2WW = ManaCost -- 2WW
  --   ∋ singletonᵐ (C , 2) ∪ᵐ singletonᵐ (W , 2)
  -- 2WW/1BBB = CardCost -- 2WW/1BBB
  --   ∋ singleton 2WW ∪ singleton 1BBB
  --   , ?
  -- _ = CardCost -- 2WW(R|G)
  --   ∋ singleton (singleton (C , 2) ∪ singleton (W , 2) ∪ singleton (R , 1))
  --   ∪ singleton (singleton (C , 2) ∪ singleton (W , 2) ∪ singleton (G , 1))

-- unfold : ManaCostChoices →

-- Cost = ManaCost ⊎ SacrificeCost

-- data CardType : Type where
--   LandType CreatureType : CardType

-- data Card : Type where
--   Land : Colour → Card
--   Creature : ManaCost →  → Card

-- record Card : Type where
--   field
--     type : Set⁺⟨ CardType ⟩
--     manaCost

{- ** Parsing/pretty-printing: interface to the outside world.
  instance
    Parser ManaCost : String → Maybe ManaCost
    Show ManaCost : ManaCost → String

  -- Input —— parse ——→ Semiring/Monoid
  --                         ∣
  --                    -—  show
  --                      \  ∣
  --                       \ ↓
  --                         String

  0) Input: 5W(U|B)
  1) Parse: 5*Any ◇ 1*W ◇ 1*(U|B)
  2) ... analysis ...
  3) Show: 5W(U|B)

  1) Given a cost, 5*Any ◇ 1*W ◇ 1*(U|B) ◇ 1*W
  2) ... analysis ...
  3) Show: 5W(U|B)W or Show⁺⁺: 5W(U|B)
-}
