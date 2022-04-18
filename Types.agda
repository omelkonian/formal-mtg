module Types where

open import Prelude.Init
open SetAsType
open import Prelude.DecEq
open import Prelude.Semigroup
-- import Prelude.Maps.Concrete as M
open import Prelude.Maps.Concrete
import Prelude.Sets.Concrete as S
-- open import Prelude.Sets.Concrete
-- open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.FromList
open import Prelude.ToList
open import Prelude.Nary
open import Prelude.Functor
open import Prelude.Decidable
open import Prelude.Ord
open import Prelude.Monoid

data Colour : Type where
  Red Green White Blue Black : Colour
unquoteDecl DecEq-Colour = DERIVE DecEq [ quote Colour , DecEq-Colour ]

Colour⁇ = Maybe Colour

pattern colorless = nothing
pattern colored x = just x
pattern R = colored Red
pattern G = colored Green
pattern W = colored White
pattern U = colored Blue
pattern B = colored Black
pattern C = colorless

Mana = Map⟨ Colour⁇ ↦ ℕ ⟩
ManaPool = Mana
ManaCost = Mana
CardCost = S.Set⟨ ManaCost ⟩
ManaCostChoices = Map⟨ S.Set⁺⟨ Colour⁇ ⟩ ↦ ℕ ⟩

instance _ = Semigroup-ℕ-+
instance _ = Monoid-ℕ-+

infix 10 _↦_
_↦_ = (Maybe Colour → ℕ → Mana) ∋ singleton ∘₂ _,_

calculateCost : ManaCostChoices → CardCost
calculateCost = go∗ ∘ _∙toList
  where
    go : List⁺ Colour⁇ → ℕ → CardCost
    go (x ∷ xs) n with xs
    ... | []     = S.singleton (x ↦ n)
    ... | y ∷ ys = S.singleton (x ↦ n) S.∪ go (y ∷ ys) n

    go∗ : List (S.Set⁺⟨ Colour⁇ ⟩ × ℕ) → CardCost
    go∗ = λ where
      [] → S.singleton (C ↦ 0)
      ((s⁺ , n) ∷ kvs) → fromList
                       $ L.concat
                       $ (_⊗ (go∗ kvs ∙toList))
                     <$> go (S.toList'⁺ s⁺) n ∙toList
        where
          _⊗_ : ManaCost → Op₁ (List ManaCost)
          m ⊗ cur = map (_◇ m) cur

private
  _ : Mana -- 0
  _ = ∅

  m : Mana
  m = C ↦ 2 ◇ W ↦ 2

  m′ : Mana
  m′ = C ↦ 4 ◇ W ↦ 2

  _ : m ◇ m′
    ≡ W ↦ 4 ◇ C ↦ 6
  _ = refl

  -- this is *not* setoid equality
  _ : m ◇ m′
    ≢ C ↦ 6 ◇ W ↦ 4
  _ = λ ()

  -- this *is* setoid equality
  _ : (m ◇ m′)
   ≈ᵐ (C ↦ 6 ◇ W ↦ 4)
  _ = auto

  _ : ManaPool
  _ = C ↦ 2 ◇ W ↦ 2 ◇ R ↦ 1

  1BBB = ManaCost -- 1BBB
    ∋ C ↦ 1 ◇ B ↦ 3
  2WW = ManaCost -- 2WW
    ∋ C ↦ 2 ◇ W ↦ 2
  2WW/1BBB = CardCost -- 2WW/1BBB
    ∋ fromList ⟦ 2WW , 1BBB ⟧

  _ = CardCost -- 2WW(R|G) aka 2WWR|2WWG)
    ∋ fromList
        ⟦ C ↦ 2 ◇ W ↦ 2 ◇ R ↦ 1
        , C ↦ 2 ◇ W ↦ 2 ◇ G ↦ 1
        ⟧

  _ = ManaCostChoices -- 2WW(R|G)
    ∋ singleton (S.fromList⁺ [ C ]     , 2)
    ◇ singleton (S.fromList⁺ [ W ]     , 2)
    ◇ singleton (S.fromList⁺ ⟦ R , G ⟧ , 1)

  _ : calculateCost ∅
    ≡ S.singleton (C ↦ 0)
  _ = refl

  _ : calculateCost (singleton (S.fromList⁺ [ C ] , 0))
    ≡ S.singleton (C ↦ 0)
  _ = refl

  _ : calculateCost (singleton (S.fromList⁺ [ R ] , 1))
    ≡ S.singleton (C ↦ 0 ◇ R ↦ 1)
  _ = refl

  _ : calculateCost (singleton (S.fromList⁺ (R ∷ G ∷ []) , 1))
    ≡   S.singleton (C ↦ 0 ◇ R ↦ 1)
    S.∪ S.singleton (C ↦ 0 ◇ G ↦ 1)
  _ = refl

  _ : calculateCost ( singleton (S.fromList⁺ [ C ] , 2)
                    ◇ singleton (S.fromList⁺ (R ∷ G ∷ []) , 1))
    ≡   S.singleton (R ↦ 1 ◇ C ↦ 2)
    S.∪ S.singleton (G ↦ 1 ◇ C ↦ 2)
  _ = refl

  _ : calculateCost ( singleton (S.fromList⁺ (B ∷ U ∷ []) , 1)
                    ◇ singleton (S.fromList⁺ (R ∷ G ∷ []) , 1))
    ≡   S.singleton (C ↦ 0 ◇ B ↦ 1 ◇ R ↦ 1)
    S.∪ S.singleton (C ↦ 0 ◇ B ↦ 1 ◇ G ↦ 1)
    S.∪ S.singleton (C ↦ 0 ◇ U ↦ 1 ◇ R ↦ 1)
    S.∪ S.singleton (C ↦ 0 ◇ U ↦ 1 ◇ G ↦ 1)
  _ = refl

  _ : calculateCost ( singleton (S.fromList⁺ (R ∷ U ∷ []) , 1)
                    ◇ singleton (S.fromList⁺ (R ∷ G ∷ []) , 1))
    ≡   S.singleton (C ↦ 0 ◇ R ↦ 2)
    S.∪ S.singleton (C ↦ 0 ◇ R ↦ 1 ◇ G ↦ 1)
    S.∪ S.singleton (C ↦ 0 ◇ U ↦ 1 ◇ R ↦ 1)
    S.∪ S.singleton (C ↦ 0 ◇ U ↦ 1 ◇ G ↦ 1)
  _ = refl

-- Cost = ManaCost ⊎ SacrificeCost

data CreatureType : Type where
  Human Soldier Dwarf Vampire Ogre Warrior : CreatureType
unquoteDecl DecEq-CreatureType = DERIVE DecEq [ quote CreatureType , DecEq-CreatureType ]

record CreatureStats : Type where
  constructor _/_
  field power     : ℕ
        toughness : ℕ
open CreatureStats public
unquoteDecl DecEq-CreatureStats = DERIVE DecEq [ quote CreatureStats , DecEq-CreatureStats ]

data Card : Type where
  BasicLand : Colour → Card
  Creature  : CardCost → S.Set⁺⟨ CreatureType ⟩ → CreatureStats → Card
unquoteDecl DecEq-Card = DERIVE DecEq [ quote Card , DecEq-Card ]

Mountain = BasicLand Red
Forest   = BasicLand Green
Plains   = BasicLand White
Island   = BasicLand Blue
Swamp    = BasicLand Black

GlorySeeker = Card ∋ Creature
  (S.singleton (C ↦ 1 ◇ W ↦ 1))
  (S.fromList⁺ ⟦ Human , Soldier ⟧)
  (2 / 2)

StaunchShieldmate = Card ∋ Creature
  (S.singleton (W ↦ 1))
  (S.fromList⁺ ⟦ Dwarf , Soldier ⟧)
  (1 / 3)

FalkenrathReaver = Card ∋ Creature
  (S.singleton (C ↦ 1 ◇ R ↦ 1))
  (S.fromList⁺ [ Vampire ])
  (2 / 2)

OnakkeOgre = Card ∋ Creature
  (S.singleton (C ↦ 2 ◇ R ↦ 1))
  (S.fromList⁺ ⟦ Ogre , Warrior ⟧)
  (4 / 2)

-- IsLand IsCreature : Pred₀ Card
-- IsLand = λ where
--   (BasicLand _) → ⊤
--   _ → ⊥
-- IsCreature = λ where
--   (Creature _ _ _) → ⊤
--   _ → ⊥

-- properties : Card → Type
-- properties = λ where
--   (BasicLand _) → LandProperties
--   (Creature _ _ _) → CreatureProperties

record CreatureProperties : Type where
  field
    summoningSickness : Bool
open CreatureProperties public

record CardInstance : Type where
  field
    card : Card
    tapped : Bool
    -- properties : properties card
    properties : case card of λ where
      (BasicLand _) → ⊤
      (Creature _ _ _) → CreatureProperties
open CardInstance public

goProps : Op₁ CreatureProperties
goProps ps = record ps {summoningSickness = false}

-- go : Op₁ CardInstance
-- go ci@(record {card = c; properties = ps})
--   with ci .card
-- ... | BasicLand _    = ci
-- ... | Creature _ _ _ = ? -- record ci {properties = goProps ps}


{-
Cards = List Card
Deck = Cards
Hand = Cards

record Player : Type where
  constructor mkPlayer
  field
    library : Cards
    hand : Hand
    graveyard : Cards
    exile : Cards
    life : ℕ
    control : List CardInstance
open Player public

removeSummoningSickness : Player → Player
removeSummoningSickness p = p {control = go <$> p .control}
  where
    goProps : Op₁ CreatureProperties
    goProps ps = record ps {summoningSickness = false}

    go : Op₁ CardInstance
    go ci@(record {card = c; properties = ps})
      with ci .card
    ... | BasicLand _    = ci
    ... | Creature _ _ _ = ? -- record ci {properties = goProps ps}
-}

-- data DRAW⟨_↝_⟩ : Player → Maybe Player → Type where

--   drawFail :

--     p .library ≡ []
--     ───────────────────
--     DRAW⟨ p ↝ nothing ⟩

--   drawSuccess :

--     p .library ≡ c ∷ cs
--     ─────────────────────────────────────────────────────────
--     DRAW⟨ p ↝ just (p { library = cs; hand = c ∷ p .hand } ⟩

-- data MAIN⟨_↝_⟩ : Player → Maybe Player → Type where

--    curState .players ≡ p ∷ ps
--   DRAW⟨ p ↝ nothing ⟩
--   ─────────────────────────────────────────────────────────
--   FinalState


-- data Outcome : Type where
--   draw firstWins secondWins : Outcome



-- record GameState : Type where
--   field
--     finished : Maybe Outcome
--     player₁  : Player
--     player₂  : Player


-- prepare : GameState → GameState
-- prepare st = st {players = removeSummoningSickness <$> st .players}
--   where


-- data _↝_ : Rel₀ GameState where

--   executeAllPhases :

--     ∙ DRAW⟨ st₀ ↝ st₁ ⟩
--     ∙ MAIN⟨ st₁ ↝ st₂ ⟩
--     ∙ ATTACK⟨ st₂ ↝ st₃ ⟩
--     -- ∙ POST⟨ st₃ ↝ st₄ ⟩
--     -- ∙ END⟨  ⟩
--       ─────────────────
--       st₀ ↝ st₄

-- _↝_ : Rel₀ GameState

-- _↝∗_ : Rel₀ GameState -- reflexive transitive _↝_

-- Game = ∃ λ s₀ sₙ → s₀ ↝∗ sₙ

-- _ : {players = ⟦ st₁ , st₂ ⟧}
--   ↝ {players = p₁{life=20}, p₂{life=2}}
--   ↝ { players = p₁{life=20}, p₂{life=0}
--     , outcome = just first wins
--     }
-- _ = drawSuccess , attack₁ , main₁ , drawSuccess , ...


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
  3) Show: 5W(U|B)W or Show⁺⁺: 5W(U|B)--
-}
