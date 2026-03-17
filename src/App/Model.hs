{- |
Module      : App.Model
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (ghc-wasm-meta)

This module defines the application t'Model'.
-}
module App.Model where

import Fitch.Proof
import Miso (DOMRef, MisoString, URI)
import Miso.Lens (Lens, lens)
import Miso.Lens.TH (makeLenses)
import Specification.Types

------------------------------------------------------------------------------------------

-- * Data Types

{- | Specifies the location where a t'Assumption', t'Derivation' or
t'Proof' has been dropped.
-}
data DropLocation where
  -- | Dropped __before__ a t'NodeAddr'.
  LineAddr :: NodeAddr -> DropLocation
  -- | Dropped in the bin.
  LocationBin :: DropLocation
  deriving (Show, Eq)

-- | Specifies whether a t'Assumption', t'Derivation' or a t'Proof' should be spawned.
data SpawnType where
  -- | Spawn a t'Assumption' or t'Derivation'
  SpawnLine :: SpawnType
  -- | Spawn a t'Proof'
  SpawnProof :: SpawnType
  deriving (Show, Eq)

-- | Enumeration of Logics that the app supports.
data Logic = Prop | FOL deriving (Show, Eq)

{- | Returns whether a given t'SpawnType' can be spawned __before__ a t'NodeAddr'.
For example, a t'Proof' can be spawned before a 'NAConclusion',
but not before a 'NAAssumption'.
-}
canSpawnBefore :: NodeAddr -> SpawnType -> Bool
canSpawnBefore (NAProof n na) st = canSpawnBefore na st
canSpawnBefore (NALine{}; NAAssumption{}; NAConclusion; NAAfterConclusion) SpawnLine =
  True
canSpawnBefore (NALine{}; NAConclusion) SpawnProof = True
canSpawnBefore _ _ = False

-- | The actions of the application.
data Action where
  -- | Start MathJAX on the given t'DOMRef'
  InitMathJAX :: DOMRef -> Action
  {- | Open a @popover@ element with given @id@. Takes a t'Bool',
  that turns the action into a Noop, when 'False'.
  -}
  PopOpen :: MisoString -> Bool -> Action
  -- | Close a @popover@ element with given @id@.
  PopClose :: MisoString -> Action
  -- | Toggle the sidebar.
  ToggleSidebar :: Action
  -- | Update the t'Proof'.
  SetProof :: Proof -> Action
  {- | Pop a state of the history,
  see <https://developer.mozilla.org/en-US/docs/Web/API/History_API>.
  -}
  PopState :: URI -> Action
  -- | Setup directly called after application is mounted.
  Setup :: Action
  -- | Focus a t'Formula' or t'RuleApplication' @<input>@ field.
  Focus :: Either NodeAddr NodeAddr -> Action
  -- | Blur a t'Formula' or t'RuleApplication' @<input>@ field.
  Blur :: Either NodeAddr NodeAddr -> Action
  -- | Handle input text to @<input>@ field.
  Input :: MisoString -> DOMRef -> Action
  -- | Same as v'Input' but with more information.
  ProcessInput :: MisoString -> Int -> Int -> Either NodeAddr NodeAddr -> Action
  -- | Handle changes to @<input>@ field, triggers only, after field loses focus.
  Change :: Action
  -- | Drop currently dragged element into t'DropLocation'
  Drop :: DropLocation -> Action
  -- | Called when the drop-zone at a t'NodeAddr' is entered.
  DragEnter :: NodeAddr -> Action
  -- | Called when a drop-zone is left.
  DragLeave :: Action
  -- | Called when dragging of a t'Assumption', t'Derivation' or t'Proof' begins.
  DragStart :: Either NodeAddr ProofAddr -> Action
  -- | Called when dragging ends.
  DragEnd :: Action
  -- | Called when spawning starts with given t'SpawnType'.
  SpawnStart :: SpawnType -> Action
  -- Navigate forward in the history
  NavigateForward :: Action
  -- | Navigate backward in the history
  NavigateBackward :: Action
  -- | No op.
  Nop :: Action

-- | Type for position information.
type Pos = Int

------------------------------------------------------------------------------------------

-- * Model

-- | The t'Model' of the application.
data Model = Model
  { _focusedLine :: Maybe (Either NodeAddr NodeAddr)
  -- ^ Currently focused line.
  , _exampleProofs :: [(Text, Proof)]
  -- ^ List of example t'Proof's.
  , _emptyDerivation :: Derivation
  -- ^ Empty t'Derivation' as a dummy for inserting.
  , _proof :: Proof
  -- ^ Current t'Proof' of the application.
  , _sidebarToggle :: Bool
  -- ^ v'True' if the sidebar is open.
  , _dragTarget :: Maybe (Either NodeAddr ProofAddr)
  -- ^ t'Assumption', t'Derivation' or t'Proof' that is currently being dragged.
  , _spawnType :: Maybe SpawnType
  -- ^ Type of element to be spawned.
  , _currentHoverLine :: Maybe NodeAddr
  -- ^ Line before which the user currently hovers.
  , _dragging :: Bool
  -- ^ v'True' if the user is currently dragging an element.
  , _operators :: [(Text, Text, Int)]
  {- ^ List of operators, consisting of (alias, operator, arity),
  where alias is an alternative notation for the operator.
  -}
  , _infixPreds :: [(Text, Text)]
  {- ^ List of infix predicates, consisting of (alias, predicate),
  where alias is an alternative notation for the predicate.
  -}
  , _quantifiers :: [(Text, Text)]
  {- ^ List of quantifiers, consisting of (alias, quantifier),
  where alias is an alternative notation for the quantifier.
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
  -- ^ A map that contains all rules, mapping their t'Name' to their t'RuleSpec'.
  , _uri :: URI
  -- ^ t'URI' of the application.
  , _logic :: Logic
  -- ^ t'Logic' that the app currently uses.
  }
  deriving (Eq)

-- | Generates an initial t'Model' for pre-filling some fields (mostly with v'Nothing').
initialModel ::
  {- | Empty t'Derivation', used for inserting t'Assumption's, t'Derivation's and
  t'Proof's.
  -}
  Derivation ->
  -- | Initial t'Proof'.
  Proof ->
  -- | Example t'Proof's.
  [(Text, Proof)] ->
  -- | A list of operators (alias, operator, arity)
  [(Text, Text, Int)] ->
  -- | A list of quantifiers (alias, quantifier)
  [(Text, Text)] ->
  -- | A list of infix predicates (alias, predicate)
  [(Text, Text)] ->
  -- | The map of rules
  Map Name RuleSpec ->
  -- | The current t'URI'
  URI ->
  -- | Logic that the app uses.
  Logic ->
  -- | initial state of '_sidebarToggle'
  Bool ->
  -- | Initial t'Model' with sensible defaults
  Model
initialModel emptyD initialP ps operators infixPreds quantifiers rules uri logic sidebarToggle =
  Model
    { _focusedLine = Nothing
    , _exampleProofs = ps
    , _emptyDerivation = emptyD
    , _proof = initialP
    , _sidebarToggle = sidebarToggle
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
    , _logic = logic
    }

-- * Lenses

{- $makeLensesParagraph
Generated using 'makeLenses'.
-}

$(makeLenses ''Model)
