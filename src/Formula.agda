{-# OPTIONS --postfix-projections --safe --without-K #-}

module Formula (At : Set) where

data Formula : Set where
  `I : Formula
  +at -at : At → Formula
  _`⅋_ _`⊗_ _`&_ _`⊕_ _`▷_ : Formula → Formula → Formula

`¬ : Formula → Formula
`¬ `I = `I
`¬ (+at a) = -at a
`¬ (-at a) = +at a
`¬ (p `⅋ q) = `¬ p `⊗ `¬ q
`¬ (p `⊗ q) = `¬ p `⅋ `¬ q
`¬ (p `& q) = `¬ p `⊕ `¬ q
`¬ (p `⊕ q) = `¬ p `& `¬ q
`¬ (p `▷ q) = `¬ p `▷ `¬ q
