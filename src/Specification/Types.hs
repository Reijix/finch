{- |
Module      : Specification.Types
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (ghc-wasm-meta)

This module defines specification types that mirror t'Term', t'Formula',
t'Assumption' and t'Proof' for describing Fitch proof rules.
-}
module Specification.Types where

import Data.Text qualified as T
import Fitch.Proof

------------------------------------------------------------------------------------------

-- * Rule specifications

{- | Specification of a referenced t'Proof' premise,
containing the specification of its t'Assumption's and its conclusion.
-}
type ProofSpec = ([AssumptionSpec], FormulaSpec)

-- | The specification of a Fitch rule.
data RuleSpec
  = {- | A t'RuleSpec' consists of
    a list of t'FormulaSpec' premises, a list of t'ProofSpec' premises, and a conclusion.
    -}
    RuleSpec
      -- | t'Formula' premises.
      [FormulaSpec]
      -- | t'Proof' premises.
      [ProofSpec]
      -- | The conclusion derived by the rule.
      FormulaSpec
  deriving (Show, Eq)

-- | Renders a t'RuleSpec' as TeX for displaying via MathJAX.
ruleSpecTex :: RuleSpec -> Text
ruleSpecTex (RuleSpec fs ps conclusion) =
  "\\frac{"
    <> showFsPs
    <> "}{"
    <> prettyPrint conclusion
    <> "}"
 where
  formulaSpecTex :: FormulaSpec -> Text
  formulaSpecTex = prettyPrint
  proofSpecTex :: ProofSpec -> Text
  proofSpecTex (as, f) =
    "\\begin{array}{|l}"
      <> showAs
      <> "\\\\ \\hline \\vdots \\\\ "
      <> prettyPrint f
      <> "\\end{array}"
   where
    showAs = T.intercalate "\\;" (map assumptionSpecTex as)
    assumptionSpecTex :: AssumptionSpec -> Text
    assumptionSpecTex (FFreshVar v) = "\\boxed{" <> v <> "}"
    assumptionSpecTex (AssumptionSpec frm) = formulaSpecTex frm
  showFsPs = T.intercalate "\\quad " (map formulaSpecTex fs <> map proofSpecTex ps)

------------------------------------------------------------------------------------------

-- * Term and Formula specifications

-- | A substitution of a named placeholder by some value.
data Subst a
  = -- | @v'Subst' name value@ replaces the placeholder @name@ with @value@.
    Subst Name a
  deriving (Show, Eq)

infixl 9 ~>

-- | Smart constructor for t'Subst'.
(~>) :: Name -> a -> Subst a
(~>) = Subst

-- | A t'Term' specification used in t'RuleSpec' specifications.
data TermSpec
  = -- | A term variable.
    TVar Name
  | -- | A function application.
    TFun Name [TermSpec]
  | -- | A placeholder for t'Term's @T@.
    TPlaceholder Name
  deriving (Eq, Show)

instance PrettyPrint TermSpec where
  prettyPrint :: TermSpec -> Text
  prettyPrint (TVar n) = n
  prettyPrint (TFun f ts) = f <> "(" <> T.intercalate "," (map prettyPrint ts) <> ")"
  prettyPrint (TPlaceholder n) = n

-- | A t'Formula' specification used in t'RuleSpec' specifications.
data FormulaSpec
  = -- | A substitution @φ[n ↦ t]@: formula @φ@ with variable @n@ replaced by term @t@.
    FSubst Name (Subst Name)
  | -- | A placeholder for t'Formula'e @φ@.
    FPlaceholder Name
  | -- | A predicate.
    FPred Name [TermSpec]
  | -- | An infix predicate.
    FInfixPred Name TermSpec TermSpec
  | -- | An n-ary operator.
    FOpr Text [FormulaSpec]
  | -- | A quantifier @∀x.φ@.
    FQuantifier Name Name FormulaSpec
  deriving (Eq, Show)

-- | An t'Assumption' specification used in t'RuleSpec' specifications.
data AssumptionSpec
  = -- | Regular t'FormulaSpec'.
    AssumptionSpec FormulaSpec
  | -- | A fresh-variable constraint @[c]@.
    FFreshVar Name
  deriving (Eq, Show)

instance PrettyPrint FormulaSpec where
  prettyPrint :: FormulaSpec -> Text
  prettyPrint f = go False f
   where
    go :: Bool -> FormulaSpec -> Text
    go _ (FPred p []) = p
    go _ (FPred p ts) = p <> "(" <> T.intercalate "," (map prettyPrint ts) <> ")"
    go _ (FPlaceholder n) = n
    go _ (FSubst f (Subst n t)) = f <> "[" <> n <> " ↦ " <> t <> "]"
    go True f = "(" <> go False f <> ")"
    go False (FInfixPred p t1 t2) = prettyPrint t1 <> " " <> p <> " " <> prettyPrint t2
    go False (FOpr op []) = op
    go False (FOpr op [f]) = op <> go True f
    go False (FOpr op [f1, f2]) = go True f1 <> " " <> op <> " " <> go True f2
    go False (FOpr op fs) = op <> "(" <> T.intercalate "," (map prettyPrint fs) <> ")"
    go False (FQuantifier q v f) = q <> " " <> v <> ". " <> prettyPrint f

instance PrettyPrint AssumptionSpec where
  prettyPrint :: AssumptionSpec -> Text
  prettyPrint (AssumptionSpec fSpec) = prettyPrint fSpec
  prettyPrint (FFreshVar n) = "[" <> n <> "]"

------------------------------------------------------------------------------------------
