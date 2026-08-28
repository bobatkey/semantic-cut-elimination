{-# OPTIONS --postfix-projections --safe #-}

module IPL.Formula {a} (Atom : Set a) where

data formula : Set a where
  `atom : Atom → formula
  _`⇒_  : formula → formula → formula
  _`∧_  : formula → formula → formula
  _`∨_  : formula → formula → formula
  `⊤    : formula
  `⊥    : formula

infixr 30 _`⇒_
