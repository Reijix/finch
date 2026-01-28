module Specification.FOL where

import Fitch.Proof (
  FormulaSpec (
    FFreshVar,
    FOpr,
    FPlaceholder,
    FPred,
    FQuantifier,
    FSubst
  ),
  RuleSpec (..),
  TermSpec (TPlaceholder, TVar),
  (~>),
 )
import Specification.Prop

operatorsFOL :: [(Text, Text, Int)]
operatorsFOL = operatorsProp

infixPredsFOL :: [(Text, Text)]
infixPredsFOL = [("", "=")]

quantifiersFOL :: [(Text, Text)]
quantifiersFOL = [("forall", "∀"), ("exists", "∃")]

rulesFOL :: Map Text RuleSpec
rulesFOL =
  rulesProp
    <> [ ("=I", RuleSpec [] [] (FPred "=" [TPlaceholder "E", TPlaceholder "E"]))
       ,
         ( "=E"
         , RuleSpec
             [ FSubst "φ" ("x" ~> "E")
             , FPred "=" [TPlaceholder "E", TPlaceholder "D"]
             ]
             []
             (FSubst "φ" ("x" ~> "D"))
         )
       , ("∀E", RuleSpec [FQuantifier "∀" "x" phi] [] (FSubst "φ" ("x" ~> "E")))
       ,
         ( "∀I"
         , RuleSpec
             []
             [([FFreshVar "c"], FSubst "φ" ("x" ~> "c"))]
             (FQuantifier "∀" "x" phi)
         )
       , ("∃I", RuleSpec [FSubst "φ" ("x" ~> "E")] [] (FQuantifier "∃" "x" phi))
       , ("∃E", RuleSpec [FQuantifier "∃" "x" phi] [([FFreshVar "c", FSubst "φ" ("x" ~> "c")], psi)] psi)
       ]
 where
  phi = FPlaceholder "φ"
  psi = FPlaceholder "ψ"