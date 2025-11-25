{-# LANGUAGE CPP #-}

module Main where

import App.Runner
import Fitch.Proof

-----------------------------------------------------------------------------
main :: IO ()
main = runApp exProof ["~"] ["/\\", "\\/", "->"]

-----------------------------------------------------------------------------
exProof :: Proof
exProof = SubProof [Parsed "A" $ Predicate "A" []] [] (Derivation (Parsed "A" $ Predicate "A" []) (Parsed "Re" $ RuleApplication (Rule "Re" [] (Predicate "A" [])) []))

-- SubProof
--   [formula "Formula", formula "Formula"]
--   [ ProofLine (Derivation (formula "Formula") (rule "rule" [])),
--     SubProof [formula "Formula"] [ProofLine (Derivation (formula "Formula") (rule "rule" []))] (Derivation (formula "Formula") (rule "rule" [])),
--     SubProof [formula "Formula"] [ProofLine (Derivation (formula "Formula") (rule "rule" []))] (Derivation (formula "Formula") (rule "rule" []))
--   ]
--   (Derivation (formula "Formula") (rule "rule" []))

-----------------------------------------------------------------------------
