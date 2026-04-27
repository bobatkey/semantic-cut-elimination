{-# OPTIONS --postfix-projections --safe #-}

module MIPL.Formula {a} (Atom : Set a) where

data formula : Set a where
  `atom : Atom → formula
  _`⇒_  : formula → formula → formula
  _`∧_  : formula → formula → formula
  `⊤    : formula
