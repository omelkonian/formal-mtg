module Types where

open import Agda.Primitive using () renaming (Set to Type)
open import Prelude.Init
open import Prelude.General
open import Prelude.Semigroup
open import Prelude.DecEq
open import Prelude.Measurable
open import Prelude.Ord
open import Prelude.Functor
open import Prelude.Decidable
open import Prelude.Lists
open import Prelude.Listable
open import Prelude.DecLists
open import Prelude.Nary

data Colour : Type where
  Red Green White Blue Black : Colour
unquoteDecl DecEq-Colour = DERIVE DecEq [ quote Colour , DecEq-Colour ]

-- Colour⁇ = Maybe Colour

instance
  Listable-Colour : Listable Colour
  Listable-Colour = λ where
    .witness → ⟦ Red , Green , White , Blue , Black ⟧
    .finite  → λ where
      Red   → auto
      Green → auto
      White → auto
      Blue  → auto
      Black → auto

  Listable-Maybe : ∀ {X : Type} → ⦃ Listable X ⦄ → Listable (Maybe X)
  Listable-Maybe = λ where
    .witness → nothing ∷ (just <$> witness)
    .finite  → λ where
      nothing  → here refl
      (just x) → there (L.Mem.∈-map⁺ just (finite x))

pattern colorless = nothing
pattern colored x = just x
pattern R = colored Red
pattern G = colored Green
pattern W = colored White
pattern U = colored Blue
pattern B = colored Black
pattern C = colorless

{-
  -- T0D0: use a proper bag interface
  ManaPool = List (Maybe Colour)

  -- _≈_ : Rel₀ ManaPool
  -- s ≈ s′ = normalize s ≡ normalize s′

  instance
    Semigroup-ManaPool : Semigroup ManaPool
    Semigroup-ManaPool ._◇_ = _++_

  infix 10 _∗_
  _∗_ : ℕ → Maybe Colour → ManaPool
  _∗_ = L.replicate

  open MultiTest
  private
    _ = ManaPool
    ∋⋮ C ∷ C ∷ W ∷ W ∷ []
      ⋮ (C ∷ C ∷ []) ◇ (W ∷ W ∷ [])
      ⋮ 2 ∗ C ◇ 2 ∗ W
      ⋮∅
-}

import Prelude.Maps.Concrete as M
open import Prelude.Maps.Concrete
import Prelude.Sets.Concrete as S
open import Prelude.Sets.Concrete

Mana = Map⟨ Maybe Colour ↦ ℕ ⟩
ManaPool = Mana
ManaCost = Mana
CardCost = Set⁺⟨ ManaCost ⟩
ManaCostChoices = Map⟨ Set⟨ Maybe Colour ⟩ ↦ ℕ ⟩
private
  instance _ = Semigroup-ℕ-+

  _ : Mana
  _ = M.singleton (C , 2)
    ◇ M.singleton (W , 2)

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



-- _≤_ : Rel₀ ManaPool
-- consume⁺ : (m c : ManaPool) → .{ c ≤ m } → ManaPool

-- spend : ManaPool → Maybe Colour → Maybe ManaPool
-- spend m = λ where
--   colorless →
--     if colorless ∈ m (m′) then
--       just m′
--     else ...
--   (just _) → ?

-- data _≺_ : Rel₀ ManaPool where
--   base :
--     ────
--     [] ≺ m
--   step :
--     ?

-- spend∗ m (colorless ∷ c) = ?
--   let c∅ , c′ = filter Is-just c
--   m′ ← spend∗ m c′
--   c∅ <-> m′


-- spend∗ : ManaPool → ManaPool → Maybe ManaPool
-- spend∗ m [] = just m
-- spend∗ m (colorless ∷ c) = ?
--   let c∅ , c′ = filter Is-just c
--   m′ ← spend∗ m c′
--   c∅ <-> m′

-- e.g. calculate ℙ(ManaPool) and brute-force (mutanti mutandis)

-- spend∗ m (just base ∷ c) = ?
-- spend∗ m (x ∷ c) = do
--   m′ ← spend x m

-- consumeAuto : ManaPool → Cost → Maybe ManaPool
-- consumeAuto m c = consume m <$> makeChoice c


-- m = {1*(R⊎⋯⊎B)}⁺
-- c = {1*R} / ⋯ / {1*B} ≈ {1*C}


-- m  = {1*R}⁺ {1*C}⁺ ≈ {1*R}⁺ {1*(R⊎⋯⊎B)}⁺
-- c  = {1*R}⁻
-- m′ = {1*C}⁺

-- m  = {1*R}⁺ {1*C}⁺
-- c  = {1*C}⁻
-- m′ = {1*R}⁺ | {1*C}⁺

-- BASE := R | ⋯ | B

-- ∙ {n*<BASE>}⁺
-- ∙ n ≥ m
-- ∙ {m*<BASE>}⁻
--   ────────────────
--   (n-m)*<BASE>⁺

-- R ↝ R ⊎ G ↝ ⋯ ↝ C

-- ∙ {n*_}⁺
-- ∙ n ≥ m
-- ∙ {m*C}⁻
--   ────────────────
--   (n-m)*<BASE>⁺

-- [1*R,2*G,1*R,6*C, .... 1000 elements ...]
-- sieve 2*R ↝ [2*G,6*C.... 1000 elements ...]
-- [2*G,1*R,6*C,1*R]



-- ⟦_⟧ : ManaCost → Pred₀ (Multiset⟨ Land ⟩)


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
