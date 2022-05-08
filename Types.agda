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
open import Prelude.Lenses
open import Prelude.Default hiding (Default-→)
open import Prelude.Lists hiding (_↦_)
open import Prelude.Membership
open import Prelude.Show


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
unquoteDecl $name _∙name _∙name=_ _∙name↝_
            $library _∙library _∙library=_ _∙library↝_
            $hand _∙hand _∙hand=_ _∙hand↝_
            $graveyard _∙graveyard _∙graveyard=_ _∙graveyard↝_
            $exile _∙exile _∙exile=_ _∙exile↝_
            $life _∙life _∙life=_ _∙life↝_
            $control _∙control _∙control=_ _∙control↝_
  = deriveLenses (quote Player)
  ( ($name , _∙name , _∙name=_ , _∙name↝_)
  ∷ ($library , _∙library , _∙library=_ , _∙library↝_)
  ∷ ($hand , _∙hand , _∙hand=_ , _∙hand↝_)
  ∷ ($graveyard , _∙graveyard , _∙graveyard=_ , _∙graveyard↝_)
  ∷ ($exile , _∙exile , _∙exile=_ , _∙exile↝_)
  ∷ ($life , _∙life , _∙life=_ , _∙life↝_)
  ∷ ($control , _∙control , _∙control=_ , _∙control↝_)
  ∷ [])
infixl 10
  _∙name=_ _∙name↝_
  _∙library=_ _∙library↝_
  _∙hand=_ _∙hand↝_
  _∙graveyard=_ _∙graveyard↝_
  _∙exile=_ _∙exile↝_
  _∙life=_ _∙life↝_
  _∙control=_ _∙control↝_

data Turn : Type where
  on-the-play on-the-draw : Turn

data Phase : Type where
  draw main : Phase

data Outcome : Type where
  DRAW 𝟙-WINS 𝟚-WINS : Outcome

record GameState : Type where
  field
    player₁  : Player
    player₂  : Player

    curTurn : Turn
    turnTrans : Op₁ Turn

    curPhase : Phase
    phaseTrans : Phase → Phase

    hasPlayedLand : Bool
    outcome : Maybe Outcome

open GameState public
private variable s s′ s″ : GameState

unquoteDecl 𝕃 _∙l _∙l=_ _∙l↝_
            ℝ _∙r _∙r=_ _∙r↝_
            $curTurn _∙curTurn _∙curTurn=_ _∙curTurn↝_
            $turnTrans _∙turnTrans _∙turnTrans=_ _∙turnTrans↝_
            $curPhase _∙curPhase _∙curPhase=_ _∙curPhase↝_
            $phaseTrans _∙phaseTrans _∙phaseTrans=_ _∙phaseTrans↝_
            $hasPlayedLand _∙hasPlayedLand _∙hasPlayedLand=_ _∙hasPlayedLand↝_
            $outcome _∙outcome _∙outcome=_ _∙outcome↝_
  = deriveLenses (quote GameState)
    ( (𝕃 , _∙l , _∙l=_ , _∙l↝_)
    ∷ (ℝ , _∙r , _∙r=_ , _∙r↝_)
    ∷ ($curTurn , _∙curTurn , _∙curTurn=_ , _∙curTurn↝_)
    ∷ ($turnTrans , _∙turnTrans , _∙turnTrans=_ , _∙turnTrans↝_)
    ∷ ($curPhase , _∙curPhase , _∙curPhase=_ , _∙curPhase↝_)
    ∷ ($phaseTrans , _∙phaseTrans , _∙phaseTrans=_ , _∙phaseTrans↝_)
    ∷ ($hasPlayedLand , _∙hasPlayedLand , _∙hasPlayedLand=_ , _∙hasPlayedLand↝_)
    ∷ ($outcome , _∙outcome , _∙outcome=_ , _∙outcome↝_)
    ∷ [])
infixl 10
  _∙l=_ _∙l↝_
  _∙r=_ _∙r↝_
  _∙curTurn=_ _∙curTurn↝_
  _∙turnTrans=_ _∙turnTrans↝_
  _∙curPhase=_ _∙curPhase↝_
  _∙phaseTrans=_ _∙phaseTrans↝_
  _∙hasPlayedLand=_ _∙hasPlayedLand↝_
  _∙outcome=_ _∙outcome↝_

_∙curPlayer _∙otherPlayer : GameState → Player
s ∙curPlayer = case s ∙curTurn of λ where
  on-the-play → s ∙l
  on-the-draw → s ∙r
s ∙otherPlayer = case s ∙curTurn of λ where
  on-the-play → s ∙r
  on-the-draw → s ∙l

instance
  Default-Player : Default Player
  Default-Player .def = λ where
    .name → ""
    .library → []
    .hand → []
    .graveyard → []
    .exile → []
    .life → 0
    .control → []

  Default-Turn : Default Turn
  Default-Turn .def = on-the-play

  Default-TurnTrans : Default (Op₁ Turn)
  Default-TurnTrans .def = λ where
    on-the-draw → on-the-play
    on-the-play → on-the-draw

  Default-Phase : Default Phase
  Default-Phase .def = draw

  Default-PhaseTrans : Default (Op₁ Phase)
  Default-PhaseTrans .def = λ where
    draw → main
    main → draw

  Default-GameState : Default GameState
  Default-GameState .def = λ where
    .player₁ → def
    .player₂ → def
    .curTurn → def
    .turnTrans → Default-TurnTrans .def
    .curPhase → def
    .phaseTrans → Default-PhaseTrans .def
    .hasPlayedLand → false
    .outcome → nothing

instance
  Show-Player : Show Player
  Show-Player .show p =
    "{name: " ◇ show (p ∙name) ◇ "," ◇
    "life: " ◇ show (p ∙life) ◇ "}"
    -- "hand: " ◇

  Show-Turn : Show Turn
  Show-Turn .show = λ where
    on-the-play → "on-the-play"
    on-the-draw → "on-the-draw"

  Show-Phase : Show Phase
  Show-Phase .show = λ where
    draw → "draw"
    main → "main"

  Show-GameState : Show GameState
  Show-GameState .show s =
    "player₁: " ◇ show (s ∙l) ◇ "\n" ◇
    "player₂: " ◇ show (s ∙r) ◇ "\n" ◇
    "curTurn: " ◇ show (s ∙curTurn) ◇ "\n" ◇
    "curPhase: " ◇ show (s ∙curPhase) ◇ "\n"

p₁≢p₂ : player₁ ≢ player₂
p₁≢p₂ eq =
  case cong (_∙name)
     $ cong (_$ def ∙r↝ (_∙name= "sth")) eq
  of λ ()

𝕃≢ℝ : 𝕃 ≢ ℝ
𝕃≢ℝ = p₁≢p₂ ∘ cong get

mkWin : Turn → Outcome
mkWin = λ where
  on-the-play → 𝟙-WINS
  on-the-draw → 𝟚-WINS

toControl : ∀ c → Properties c
toControl = λ where
  (BasicLand _)    → tt
  (Creature _ _ _) → record {summoningSickness = true}

defInstance : Card → CardInstance
defInstance c = record {card = c; tapped = false; properties = toControl c}

infix 4 _↝_
data _↝_ : Rel₀ GameState where

  DrawLose :
    ∙ Is-nothing (s ∙outcome)
    ∙ (s ∙curPhase ≡ draw)
    ∙ (s ∙curPlayer ∙library ≡ [])
      ─────────────────────────────────
      s ↝ s ∙outcome= just (mkWin (s ∙curTurn) )

  -- Draw : ∀ (player : Lens GameState Player) →
  --   let p   = player .get s
  --       p=_ = player .set s
  --       p↝_ = (player ∙modify) s

  --       lib = p ∙library
  --   in
  --   (lib≡ : lib ≡ c ∷ lib′) →
  --   IsLand c →
  --   -- ¬ T (s ∙hasPlayedLand)
  --   ─────────────────────────────────
  --   s ↝ p↝ ( _∙hand↝ (c ∷_)
  --          ∘ _∙lib=  lib′
  --          )

  PlayLand : ∀ (player : Lens GameState Player) →
    let p   = player .get s
        p=_ = player .set s
        p↝_ = (player ∙modify) s

        h   = p ∙hand
    in
    (c∈ : c ∈ h) →
    IsLand c →
    -- ¬ T (s ∙hasPlayedLand)
    ─────────────────────────────────
    s ↝ p↝ ( _∙control↝ (defInstance c ∷_)
           ∘ _∙hand=    remove h (L.Any.index c∈)
           )
        -- ∙hasPlayedLand= true

  -- PlayCreature : ∀ (player : Lens GameState Player) →
  --   let p   = player .get s
  --       p=_ = player .set s
  --       p↝_ = (player ∙modify) s

  --       h    = p ∙hand
  --   in
  --   (c∈ : c ∈ h) →
  --   IsCreature c →
  --   c ∙cost ≤ curManaPool →
  --   ─────────────────────────────────
  --   s ↝ p↝ ( _∙control↝ (defInstance c ∷_)
  --          ∘ _∙hand=    remove h (L.Any.index c∈)
  --          )

open ReflexiveTransitiveClosure _↝_ public
  using (begin_; _∎)
  renaming (_—→⟨_⟩_ to _↝⟨_⟩_; _—↠_ to _↝∗_)

private
  S  = def ∙l↝ ( _∙name= "Orestis"
               ∘ _∙hand= [ Forest ] )
           ∙r↝ (_∙name= "Kokos")
  S′ = S ∙l↝ ( _∙hand=    []
             ∘ _∙control= [ defInstance Forest ] )

  _ : S ↝∗ S′
  _ = begin
      S
    ↝⟨ PlayLand 𝕃 auto auto ⟩
      S′
    ∎

  -- _ : S ↝∗ S′
  -- _ = begin
  --     ...
  --   ↝⟨ PlayLand 𝕃 auto auto ⟩
  --     ...
  --   ↝⟨ PlayLand ℝ auto auto ⟩
  --     ...
  --   ∎

  -- _ : S ↝∗ S′
  -- _ = begin
  --     ...
  --   ↝⟨ PlayLand 𝕃 auto auto ⟩
  --   ↝⟨ PlayLand 𝕃 auto auto ⟩
  --     ...
  --   ∎

  -- _ : S ↝∗ S′
  -- _ = begin
  --   {S}
  --   --TURNS
  --   𝕃: --PHASES
  --     {S}
  --     DRAW: Forest
  --     {S₁}
  --     MAIN:
  --       ∙ play land (Forest)
  --     {S₂}
  --   ℝ:
  --     {S₂}
  --     DRAW: ToxicGnarler
  --     {S₃}
  --     MAIN:
  --       ∙ play land (Mountain)
  --     {S₄}
  --   𝕃:
  --     {S₄}
  --     DRAW: TreeHugger
  --     {S₅}
  --     MAIN:
  --       ∙ play creature (TreeHugger)
  --     {S₆}
  --   ℝ:
  --     DRAW: Mountain
  --     MAIN:
  --       ∙ play land (Mountain)
  --       ∙ play creature (ToxicGnarler)
  --   {S′}
  --   ∎

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

-- prepare : GameState → GameState
-- prepare st = st {players = removeSummoningSickness <$> st .players}

--   executeAllPhases :
--     ∙ DRAW⟨ st₀ ↝ st₁ ⟩
--     ∙ MAIN⟨ st₁ ↝ st₂ ⟩
--     ∙ ATTACK⟨ st₂ ↝ st₃ ⟩
--     -- ∙ POST⟨ st₃ ↝ st₄ ⟩
--     -- ∙ END⟨  ⟩
--       ─────────────────
--       st₀ ↝ st₄

{- ** Parsing/pretty-printing: interface to the outside world.
  instance
    Parser ManaCost : String → Maybe ManaCost
    Show ManaCost : ManaCost → String

  Input —— parse ——→ Semiring/Monoid
                          ∣
                     -—  show
                       \  ∣
                        \ ↓
                          String

  0) Input: 5W(U|B)
  1) Parse: 5*Any ◇ 1*W ◇ 1*(U|B)
  2) ... analysis ...
  3) Show: 5W(U|B)

  1) Given a cost, 5*Any ◇ 1*W ◇ 1*(U|B) ◇ 1*W
  2) ... analysis ...
  3) Show: 5W(U|B)W or Show⁺⁺: 5W(U|B)----
-}
