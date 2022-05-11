module Types where

open import Prelude.Init
open SetAsType
open L using (_[_]%=_)
open import Prelude.DecEq
open import Prelude.Semigroup
open import Prelude.Maps.Concrete
open import Prelude.Sets.Concrete using (_∈ˢ_)
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
private variable
  mp mp′ : ManaPool
  mc mc′ : ManaCost
  cc cc′ : CardCost
  mcc mcc′ : ManaCostChoices

instance _ = Semigroup-ℕ-+
instance _ = Monoid-ℕ-+

_─ᵐ_ : Mana → Mana → Maybe Mana
_─ᵐ_ = _-ᵐ_ _∸_

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

-- T0D0 lenses for Cards?
_∙cost : Card → CardCost
_∙cost = λ where
  (BasicLand _)    → S.∅
  (Creature c _ _) → c

_∙mana : Card → Mana
_∙mana = λ where
  (BasicLand c)    → just c ↦ 1
  (Creature _ _ _) → ∅

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
  _∙card = card
open CardInstance public
-- unquoteDecl DecEq-CardInstance = DERIVE DecEq [ quote CardInstance , DecEq-CardInstance ]
private variable ci ci′ : CardInstance

_∙tap _∙untap : Op₁ CardInstance
ci ∙tap = record ci {tapped = true}
ci ∙untap = record ci {tapped = false}

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
Library = Cards
Hand = Cards

private variable
  cs cs′ cs″ : Cards
  d d′ d″ : Deck
  lib lib′ lib″ : Library
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
    manaPool : ManaPool
open Player public
unquoteDecl $name _∙name _∙name=_ _∙name↝_
            $library _∙library _∙library=_ _∙library↝_
            $hand _∙hand _∙hand=_ _∙hand↝_
            $graveyard _∙graveyard _∙graveyard=_ _∙graveyard↝_
            $exile _∙exile _∙exile=_ _∙exile↝_
            $life _∙life _∙life=_ _∙life↝_
            $control _∙control _∙control=_ _∙control↝_
            $manaPool _∙manaPool _∙manaPool=_ _∙manaPool↝_
  = deriveLenses (quote Player)
  ( ($name , _∙name , _∙name=_ , _∙name↝_)
  ∷ ($library , _∙library , _∙library=_ , _∙library↝_)
  ∷ ($hand , _∙hand , _∙hand=_ , _∙hand↝_)
  ∷ ($graveyard , _∙graveyard , _∙graveyard=_ , _∙graveyard↝_)
  ∷ ($exile , _∙exile , _∙exile=_ , _∙exile↝_)
  ∷ ($life , _∙life , _∙life=_ , _∙life↝_)
  ∷ ($control , _∙control , _∙control=_ , _∙control↝_)
  ∷ ($manaPool , _∙manaPool , _∙manaPool=_ , _∙manaPool↝_)
  ∷ [])
infixl 10
  _∙name=_ _∙name↝_
  _∙library=_ _∙library↝_
  _∙hand=_ _∙hand↝_
  _∙graveyard=_ _∙graveyard↝_
  _∙exile=_ _∙exile↝_
  _∙life=_ _∙life↝_
  _∙control=_ _∙control↝_
  _∙manaPool=_ _∙manaPool↝_

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
    nextTurn : Op₁ Turn

    curPhase : Phase
    nextPhase : Op₁ Phase

    hasPlayedLand : Bool
    outcome : Maybe Outcome

open GameState public
private variable s s′ s″ : GameState

unquoteDecl 𝕃 _∙l _∙l=_ _∙l↝_
            ℝ _∙r _∙r=_ _∙r↝_
            $curTurn _∙curTurn _∙curTurn=_ _∙curTurn↝_
            $nextTurn _∙nextTurn _∙nextTurn=_ _∙nextTurn↝_
            $curPhase _∙curPhase _∙curPhase=_ _∙curPhase↝_
            $nextPhase _∙nextPhase _∙nextPhase=_ _∙nextPhase↝_
            $hasPlayedLand _∙hasPlayedLand _∙hasPlayedLand=_ _∙hasPlayedLand↝_
            $outcome _∙outcome _∙outcome=_ _∙outcome↝_
  = deriveLenses (quote GameState)
    ( (𝕃 , _∙l , _∙l=_ , _∙l↝_)
    ∷ (ℝ , _∙r , _∙r=_ , _∙r↝_)
    ∷ ($curTurn , _∙curTurn , _∙curTurn=_ , _∙curTurn↝_)
    ∷ ($nextTurn , _∙nextTurn , _∙nextTurn=_ , _∙nextTurn↝_)
    ∷ ($curPhase , _∙curPhase , _∙curPhase=_ , _∙curPhase↝_)
    ∷ ($nextPhase , _∙nextPhase , _∙nextPhase=_ , _∙nextPhase↝_)
    ∷ ($hasPlayedLand , _∙hasPlayedLand , _∙hasPlayedLand=_ , _∙hasPlayedLand↝_)
    ∷ ($outcome , _∙outcome , _∙outcome=_ , _∙outcome↝_)
    ∷ [])
infixl 9.9
  _∙l
  _∙r
  _∙curTurn
  _∙nextTurn
  _∙curPhase
  _∙nextPhase
  _∙hasPlayedLand
  _∙outcome
infixl 10
  _∙l=_ _∙l↝_
  _∙r=_ _∙r↝_
  _∙curTurn=_ _∙curTurn↝_
  _∙nextTurn=_ _∙nextTurn↝_
  _∙curPhase=_ _∙curPhase↝_
  _∙nextPhase=_ _∙nextPhase↝_
  _∙hasPlayedLand=_ _∙hasPlayedLand↝_
  _∙outcome=_ _∙outcome↝_

  _∘curPlayer↝_ _∘otherPlayer↝_
  _∙curPlayer=_ _∙otherPlayer=_

_∘curPlayer _∘otherPlayer : GameState → Lens GameState Player
s ∘curPlayer = case s ∙curTurn of λ where
  on-the-play → 𝕃
  on-the-draw → ℝ
s ∘otherPlayer = case s ∙curTurn of λ where
  on-the-play → ℝ
  on-the-draw → 𝕃

_∘curPlayer↝_ _∘otherPlayer↝_ : Modifier GameState Player
s ∘curPlayer↝   f = ((s ∘curPlayer)   ∙modify) s f
s ∘otherPlayer↝ f = ((s ∘otherPlayer) ∙modify) s f

_∙curPlayer=_ _∙otherPlayer=_ : Setter GameState Player
s ∙curPlayer=   p = (s ∘curPlayer)   .set s p
s ∙otherPlayer= p = (s ∘otherPlayer) .set s p

_∙curPlayer _∙otherPlayer : Getter GameState Player
s ∙curPlayer = case s ∙curTurn of λ where
  on-the-play → s ∙l
  on-the-draw → s ∙r
s ∙otherPlayer = case s ∙curTurn of λ where
  on-the-play → s ∙r
  on-the-draw → s ∙l

infix 9.9 _∙proceedTurn
_∙proceedTurn : Op₁ GameState
s ∙proceedTurn = reset $ s ∙curTurn↝ (s ∙nextTurn)
  where
    reset : Op₁ GameState
    reset s = s ∙hasPlayedLand= false
             -- ∙nextPhase= (Default-NextPhase .def)
             -- ∙nextTurn= (Default-TurnPhase .def)
                ∘curPlayer↝   (_∙control↝ map _∙untap)
                ∘otherPlayer↝ (_∙control↝ map _∙untap)

infix 9.9 _∙proceedPhase
_∙proceedPhase : Op₁ GameState
s ∙proceedPhase = s ∙curPhase↝ (s ∙nextPhase)
                    ∘curPlayer↝   (_∙manaPool= ∅)
                    ∘otherPlayer↝ (_∙manaPool= ∅)
proceedPhase = _∙proceedPhase

instance
  Default-Player : Default Player
  Default-Player .def = λ where
    .name → ε
    .library → ε
    .hand → ε
    .graveyard → ε
    .exile → ε
    .life → ε
    .control → ε
    .manaPool → ∅

  Default-Turn : Default Turn
  Default-Turn .def = on-the-play

  Default-NextTurn : Default (Op₁ Turn)
  Default-NextTurn .def = λ where
    on-the-draw → on-the-play
    on-the-play → on-the-draw

  Default-Phase : Default Phase
  Default-Phase .def = draw

  Default-NextPhase : Default (Op₁ Phase)
  Default-NextPhase .def = λ where
    draw → main
    main → draw

  Default-GameState : Default GameState
  Default-GameState .def = λ where
    .player₁ → def
    .player₂ → def
    .curTurn → def
    .nextTurn → Default-NextTurn .def
    .curPhase → def
    .nextPhase → Default-NextPhase .def
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

mkLose mkWin : Turn → Outcome
mkLose = λ where
  on-the-play → 𝟚-WINS
  on-the-draw → 𝟙-WINS
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

  EndTurn :
    ∙ Is-nothing (s ∙outcome)
    ∙ (s ∙curPhase ≡ main)
      ─────────────────────────────────
      s ↝ (s ∙proceedPhase) ∙proceedTurn

  DrawLose :
    ∙ Is-nothing (s ∙outcome)
    ∙ (s ∙curPhase ≡ draw)
    ∙ (s ∙curPlayer ∙library ≡ [])
      ─────────────────────────────────
      s ↝ s ∙outcome= just (mkLose (s ∙curTurn))

  Draw :
    ∙ Is-nothing (s ∙outcome)
    ∙ (s ∙curPhase ≡ draw)
    ∙ (s ∙curPlayer ∙library ≡  c ∷ lib)
      ─────────────────────────────────
      s ↝ s ∘curPlayer↝ ( _∙hand↝    (c ∷_)
                        ∘ _∙library= lib )
            ∙proceedPhase -- T0D0: factor out to accommodate instants

  PlayLand : let h = s ∙curPlayer ∙hand in
    Is-nothing (s ∙outcome) →
    (s ∙curPhase ≡ main) →
    ¬ T (s ∙hasPlayedLand) →
    (c∈ : c ∈ h) →
    IsLand c →
    ─────────────────────────────────
    s ↝ s ∘curPlayer↝ ( _∙control↝ (defInstance c ∷_)
                      ∘ _∙hand=    remove h (L.Any.index c∈) )
          ∙hasPlayedLand= true

  PlayCreature : let h = s ∙curPlayer ∙hand in
    Is-nothing (s ∙outcome) →
    (s ∙curPhase ≡ main) →
    (c∈ : c ∈ h) →
    IsCreature c →
    (mc ∈ˢ (c ∙cost)) →
    ((s ∙curPlayer) ∙manaPool) ─ᵐ mc ≡ just mp →
    ─────────────────────────────────────────────────────────
    s ↝ s ∘curPlayer↝ ( _∙control↝  (defInstance c ∷_)
                      ∘ _∙hand=     remove h (L.Any.index c∈)
                      ∘ _∙manaPool= mp )

  TapLand : let ctrl = s ∙curPlayer ∙control in
    Is-nothing (s ∙outcome) →
    (s ∙curPhase ≡ main) →
    (c∈ : ci ∈ ctrl) → let c = ci ∙card in
    IsLand c →
    ──────────────────────────────────────────────────────────────────
    s ↝ s ∘curPlayer↝ ( _∙control=  (ctrl [ L.Any.index c∈ ]%= _∙tap)
                      ∘ _∙manaPool↝ (_◇ (c ∙mana)) )

open ReflexiveTransitiveClosure _↝_ public
  using (begin_; _∎)
  renaming (_—→⟨_⟩_ to _↝⟨_⟩_; _—↠_ to _↝∗_)

private
  S  = def ∙l↝ ( _∙name= "Orestis"
               ∘ _∙library= [ Mountain ]
               )
           ∙r↝ (_∙name= "Kokos"
               ∘ _∙library= [ Forest ]
               )

  S′ = def ∙outcome= just 𝟚-WINS
           ∙l↝ ( _∙name= "Orestis"
               ∘ _∙control= [ defInstance Mountain ]
               )
           ∙r↝ (_∙name= "Kokos"
               ∘ _∙control= [ defInstance Forest ]
               )

  _ : S ↝∗ S′
  _ = begin
      S
    ↝⟨ Draw auto refl refl ⟩
      (S ∙l↝ ( _∙library= []
             ∘ _∙hand=    [ Mountain ] )
         ∙curPhase= main
      )
    ↝⟨ PlayLand auto refl auto auto auto ⟩
      (S ∙l↝ ( _∙library= []
             ∘ _∙control= [ defInstance Mountain ]
             )
         ∙curPhase= main
         ∙hasPlayedLand= true
      )
    ↝⟨ EndTurn auto refl ⟩
      (S ∙l↝ ( _∙library= []
             ∘ _∙control= [ defInstance Mountain ] )
         ∙curTurn=  on-the-draw
         ∙curPhase= draw
      )
    ↝⟨ Draw auto refl refl ⟩
      (S ∙l↝ ( _∙library= []
             ∘ _∙control= [ defInstance Mountain ] )
         ∙r↝ ( _∙library= []
             ∘ _∙hand= [ Forest ] )
         ∙curTurn=  on-the-draw
         ∙curPhase= main
      )
    ↝⟨ PlayLand auto refl auto auto auto ⟩
      (S ∙l↝ ( _∙library= []
             ∘ _∙hand= []
             ∘ _∙control= [ defInstance Mountain ] )
         ∙r↝ ( _∙library= []
             ∘ _∙control= [ defInstance Forest ] )
         ∙curTurn=  on-the-draw
         ∙curPhase= main
         ∙hasPlayedLand= true
      )
    ↝⟨ TapLand auto refl (here refl) auto ⟩
      (S ∙l↝ ( _∙library= []
             ∘ _∙hand= []
             ∘ _∙control= [ defInstance Mountain ] )
         ∙r↝ ( _∙library= []
             ∘ _∙control= [ defInstance Forest ∙tap ]
             ∘ _∙manaPool= (G ↦ 1) )
         ∙curTurn=  on-the-draw
         ∙curPhase= main
         ∙hasPlayedLand= true
      )
    ↝⟨ EndTurn auto refl ⟩
      (S ∙l↝ ( _∙library= []
             ∘ _∙hand= []
             ∘ _∙control= [ defInstance Mountain ] )
         ∙r↝ ( _∙library= []
             ∘ _∙control= [ defInstance Forest ] )
         ∙curTurn=  on-the-play
         ∙curPhase= draw
      )
    ↝⟨ DrawLose auto refl refl ⟩
      S′
    ∎

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
