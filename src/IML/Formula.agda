{-# OPTIONS --postfix-projections --safe #-}

module IML.Formula {a} (Atom : Set a) where

data formula : Set a where
  `atom : Atom → formula
  `◯    : formula → formula
  _`⇒_  : formula → formula → formula
  _`∧_  : formula → formula → formula
  _`∨_  : formula → formula → formula
  `⊤    : formula
  `⊥    : formula
