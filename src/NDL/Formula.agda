{-# OPTIONS --postfix-projections --safe #-}

module NDL.Formula {a} (Atom : Set a) where

data formula : Set a where
  `atom : Atom → formula
  _`∧_  : formula → formula → formula
  _`∨_  : formula → formula → formula
  `⊤    : formula
  `⊥    : formula
