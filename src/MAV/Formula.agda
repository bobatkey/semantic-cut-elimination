{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.Formula (At : Set) where

infixr 20 `+_ 
infixr 20 `-_ 
infixr 10 _`⅋_
infixr 10 _`⊗_
infixr 10 _`&_
infixr 10 _`⊕_
infixr 10 _`▷_

data Formula : Set where
  `I   : Formula
  `+_  : At → Formula
  `-_  : At → Formula
  _`⅋_ : Formula → Formula → Formula
  _`⊗_ : Formula → Formula → Formula
  _`&_ : Formula → Formula → Formula
  _`⊕_ : Formula → Formula → Formula
  _`▷_ : Formula → Formula → Formula

`¬ : Formula → Formula
`¬ `I = `I
`¬ (`+ a) = `- a
`¬ (`- a) = `+ a
`¬ (p `⅋ q) = `¬ p `⊗ `¬ q
`¬ (p `⊗ q) = `¬ p `⅋ `¬ q
`¬ (p `& q) = `¬ p `⊕ `¬ q
`¬ (p `⊕ q) = `¬ p `& `¬ q
`¬ (p `▷ q) = `¬ p `▷ `¬ q
