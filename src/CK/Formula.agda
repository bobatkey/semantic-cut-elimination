{-# OPTIONS --postfix-projections --safe #-}

module CK.Formula {a} (Atom : Set a) where

data formula : Set a where
  `atom : Atom → formula
  `□    : formula → formula
  `◇    : formula → formula
  _`⇒_  : formula → formula → formula
  _`∧_  : formula → formula → formula
  _`∨_  : formula → formula → formula
  `⊤    : formula
  `⊥    : formula
