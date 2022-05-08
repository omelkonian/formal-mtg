module Types where

open import Prelude.Init
open SetAsType
open import Prelude.DecEq
open import Prelude.Semigroup
open import Prelude.Maps.Concrete
import Prelude.Sets.Concrete as S
open import Prelude.DecLists
open import Prelude.FromList
open import Prelude.ToList
open import Prelude.Nary
open import Prelude.Functor
open import Prelude.Decidable
open import Prelude.Ord
open import Prelude.Monoid
open import Prelude.InferenceRules
open import Prelude.Closures

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

private variable c c′ c″ : Card

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

IsLand IsCreature : Pred₀ Card
IsLand = λ where
  (BasicLand _) → ⊤
  _ → ⊥
IsCreature = λ where
  (Creature _ _ _) → ⊤
  _ → ⊥

LandProperties = ⊤

record CreatureProperties : Type where
  field summoningSickness : Bool
open CreatureProperties public

Properties : Card → Type
Properties = λ where
  (BasicLand _)    → LandProperties
  (Creature _ _ _) → CreatureProperties

record CardInstance : Type where
  field
    card : Card
    tapped : Bool
    properties : Properties card
open CardInstance public

private
  unsummon : Op₁ CreatureProperties
  unsummon ps = record ps {summoningSickness = false}

  liftProp : Op₁ CreatureProperties → Op₁ (Properties c)
  liftProp {c = c} go ps with c
  ... | BasicLand _    = ps
  ... | Creature _ _ _ = go ps

  liftProp′ : Op₁ CardInstance
  liftProp′ ci@(record {card = c; tapped = tp; properties = ps})
    = record {card = c; tapped = tp; properties = liftProp unsummon ps}

Cards = List Card
Deck = Cards
Hand = Cards

private variable
  cs cs′ cs″ : Cards
  d d′ d″ : Deck
  h h′ h″ : Hand

record Player : Type where
  constructor mkPlayer
  field
    name : String
    library : Cards
    hand : Hand
    graveyard : Cards
    exile : Cards
    life : ℕ
    control : List CardInstance
open Player public

record GameState : Type where
  field
    -- finished : Maybe Outcome
    player₁  : Player
    player₂  : Player
open GameState public
private variable s s′ s″ : GameState

_∙𝕃 = player₁
_∙ℝ = player₂

_∙𝕃=_ _∙ℝ=_ : GameState → Player → GameState
s ∙𝕃= p = record s {player₁ = p}
s ∙ℝ= p = record s {player₂ = p}

-- _∙𝕃↝_ _∙ℝ↝_ : GameState → Op₁ Player → GameState
-- s ∙𝕃↝ f = record s {player₁ = f (s .player₁)}
-- s ∙ℝ↝ f = record s {player₂ = f (s .player₂)}

Getter : Op₂ Type
Getter X Y = X → Y

Setter : Op₂ Type
Setter X Y = X → Y → X

record Lens (X Y : Type) : Type where
  field
    getter : Getter X Y
    setter : Setter X Y

  modify : X → Op₁ Y → X
  -- modify : (x : X)
            -- → (f : (y : Y) → y ≡ x .getter → Y)
            -- → Σ (x′ : X). x′ .getter ≡ f (x .getter) refl
  modify s f = s .setter (f $ s .getter)
open Lens public

𝕃 ℝ : Lens GameState Player
𝕃 = record {getter = _∙𝕃; setter = _∙𝕃=_}
ℝ = record {getter = _∙ℝ; setter = _∙ℝ=_}

defᵖ : Player
defᵖ = λ where
  .name → ""
  .library → []
  .hand → []
  .graveyard → []
  .exile → []
  .life → 0
  .control → []

def : GameState
def = record {player₁ = defᵖ; player₂ = defᵖ}

toControl : ∀ c → Properties c
toControl = λ where
  (BasicLand _)    → tt
  (Creature _ _ _) → record {summoningSickness = true}

defInstance : Card → CardInstance
defInstance c = record {card = c; tapped = false; properties = toControl c}

open import Prelude.Lists
open import Prelude.Membership

infix 4 _↝_
data _↝_ : Rel₀ GameState where

  PlayLand : ∀ (player : Lens GameState Player) →
    let p   = player .getter s
        p=_ = player .setter s
        p↝_ = modify player s

        ctrl = p .control
        h    = p .hand
    in
    (c∈ : c ∈ h) →
    IsLand c →
    ─────────────────────────────────
    s ↝ p↝
      ∙p=
      λ p → record p
        { control = defInstance c ∷ ctrl
        ; hand    = remove h (L.Any.index c∈)
        }
   = record s { x = s .x; y = s .y; ⋯ 100 fields ⋯
              ; p = f (s .p) }
   = s ∙p↝ f

-- playCard ...

open ReflexiveTransitiveClosure _↝_ public
  using (begin_; _∎)
  renaming (_—→⟨_⟩_ to _↝⟨_⟩_; _—↠_ to _↝∗_)

private
  S  = record { player₁ = record defᵖ {name = "Orestis"; hand = [ Forest ]}
              ; player₂ = record defᵖ {name = "Kokos"}
              }
  S′ = record S
    { player₁ = record (S .player₁)
      { hand = []
      ; control = [ defInstance Forest ]
      } }

  _ : S ↝∗ S′
  _ = begin
      S
    ↝⟨ PlayLand 𝕃 auto auto ⟩
      S′
    ∎

  .player ≔ ....
  ∧ .hand ≔


-- T0D0: simple game with only lands & creatures
{-

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
