{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.Formula (At : Set) where

infix 20 `+_ 
infix 20 `-_ 
infix 15 `¬_
infix 10 _`⅋_
infix 10 _`⊗_
infix 10 _`&_
infix 10 _`⊕_
infix 10 _`▷_

data Formula : Set where
  `I   : Formula
  `+_  : At → Formula
  `-_  : At → Formula
  _`⅋_ : Formula → Formula → Formula
  _`⊗_ : Formula → Formula → Formula
  _`&_ : Formula → Formula → Formula
  _`⊕_ : Formula → Formula → Formula
  _`▷_ : Formula → Formula → Formula

`¬_ : Formula → Formula
`¬ `I = `I
`¬ (`+ a) = `- a
`¬ (`- a) = `+ a
`¬ (p `⅋ q) = `¬ p `⊗ `¬ q
`¬ (p `⊗ q) = `¬ p `⅋ `¬ q
`¬ (p `& q) = `¬ p `⊕ `¬ q
`¬ (p `⊕ q) = `¬ p `& `¬ q
`¬ (p `▷ q) = `¬ p `▷ `¬ q
