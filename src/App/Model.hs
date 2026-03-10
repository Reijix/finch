{- |
Module      : App.Model
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (GHCJS)

This module defines the application 'Model'.
-}
module App.Model where

import Fitch.Proof
import Fitch.Unification
import Miso (
  DOMRef,
  MisoString,
  URI,
 )
import Miso.CSS qualified as CSS
import Miso.Lens (Lens, lens, use, (%=), (.=), (<~))
import Miso.Lens.TH (makeLenses)
import Miso.Svg.Element qualified as S
import Miso.Svg.Property qualified as SP
import Relude.Extra.Map (DynamicMap (insert), (!?))
import Relude.Extra.Newtype

-----------------------------------------------------------------------------

-- * Types

data DropLocation where
  LineAddr :: NodeAddr -> DropLocation
  LocationBin :: DropLocation
  deriving (Show, Eq)

data SpawnType where
  SpawnLine :: SpawnType
  SpawnProof :: SpawnType
  deriving (Show, Eq)

canSpawnIn :: NodeAddr -> SpawnType -> Bool
canSpawnIn (NAProof n na) st = canSpawnIn na st
canSpawnIn (NALine{}; NAAssumption{}; NAConclusion; NAAfterConclusion) SpawnLine = True
canSpawnIn (NALine{}; NAConclusion) SpawnProof = True
canSpawnIn _ _ = False

data Action where
  InitMathJAX :: DOMRef -> Action
  PopOpen :: MisoString -> Bool -> Action
  ToggleSidebar :: Action
  PopClose :: MisoString -> Action
  SetProof :: Proof -> Action
  PopState :: URI -> Action
  Setup :: Action
  Blur :: Either NodeAddr NodeAddr -> Action
  Input :: MisoString -> DOMRef -> Action
  Change :: Action
  ProcessInput :: MisoString -> Int -> Int -> Either NodeAddr NodeAddr -> Action
  FocusInput :: Either NodeAddr NodeAddr -> Action
  Drop :: DropLocation -> Action
  DragEnter :: NodeAddr -> Action
  DragLeave :: Action
  DragOver :: Action
  DragStart :: Either NodeAddr ProofAddr -> Action
  SpawnStart :: SpawnType -> Action
  DragEnd :: Action
  Drag :: Action
  Nop :: Action

-----------------------------------------------------------------------------

type Pos = Int

data Model = Model
  { _focusedLine :: Maybe (Either NodeAddr NodeAddr)
  -- ^ the line that is currently focused
  , _exampleProofs :: [(Text, Proof)]
  , _emptyProof :: Proof
  , _emptyDerivation :: Derivation
  , _proof :: Proof
  -- ^ the current proof
  , _sidebarToggle :: Bool
  , _dragTarget :: Maybe (Either NodeAddr ProofAddr)
  -- ^ the element that is currently being dragged
  , _spawnType :: Maybe SpawnType
  -- ^ the type of element that is currently being spawned
  , _currentHoverLine :: Maybe NodeAddr
  -- ^ the line before which the user currently hovers
  , _dragging :: Bool
  -- ^ denotes whether the user is currently dragging an element
  , _operators :: [(Text, Text, Int)]
  {- ^ list of operators, consisting of (alias, symbol, arity)
  where alias is an alternative notation for the symbol
  -}
  , _infixPreds :: [(Text, Text)]
  , _quantifiers :: [(Text, Text)]
  {- ^ list of quantifiers, consisting of (alias, symbol)
  where alias is an alternative notation for the symbol
  -}
  , _functionSymbols :: Map Text (Int, Pos)
  {- ^ Collected function symbols consisting of
  * name :: Text
  * arity :: Int
  * first occurence :: Pos
  -}
  , _predicateSymbols :: Map Text (Int, Pos)
  {- ^ Collected predicate symbols consisting of
  * name :: Text
  * arity :: Int
  * first occurence :: Pos
  -}
  , _rules :: Map Name RuleSpec
  -- ^ A map that contains all rules, mapping their names to their specification
  , _uri :: URI
  }
  deriving (Show, Eq)

$(makeLenses ''Model)

-- * Initial constructors
initialModel ::
  -- | Empty proof, for the new proof button
  Proof ->
  -- | Empty derivation, used for inserting lines and 'SubProof's
  Derivation ->
  -- | Initial proof
  Proof ->
  -- | Example proofs
  [(Text, Proof)] ->
  -- | A list of operators (alias, operator, arity)
  [(Text, Text, Int)] ->
  -- | A list of quantifiers (alias, quantifier)
  [(Text, Text)] ->
  -- | A list of infix predicates (alias, predicate name)
  [(Text, Text)] ->
  -- | The map of rules
  Map Name RuleSpec ->
  URI ->
  Model
initialModel emptyP emptyD initialP ps operators infixPreds quantifiers rules uri =
  Model
    { _focusedLine = Nothing
    , _exampleProofs = ps
    , _emptyProof = emptyP
    , _emptyDerivation = emptyD
    , _proof = initialP
    , _sidebarToggle = False
    , _dragTarget = Nothing
    , _spawnType = Nothing
    , _currentHoverLine = Nothing
    , _dragging = False
    , _operators = operators
    , _infixPreds = infixPreds
    , _quantifiers = quantifiers
    , _functionSymbols = mempty
    , _predicateSymbols = mempty
    , _rules = rules
    , _uri = uri
    }
