{-# OPTIONS --postfix-projections --safe --without-K #-}

module fmla (At : Set) where

data fmla : Set where
  `I : fmla
  +at -at : At → fmla
  _`⅋_ _`⊗_ _`&_ _`⊕_ _`▷_ : fmla → fmla → fmla

`¬ : fmla → fmla
`¬ `I = `I
`¬ (+at a) = -at a
`¬ (-at a) = +at a
`¬ (p `⅋ q) = `¬ p `⊗ `¬ q
`¬ (p `⊗ q) = `¬ p `⅋ `¬ q
`¬ (p `& q) = `¬ p `⊕ `¬ q
`¬ (p `⊕ q) = `¬ p `& `¬ q
`¬ (p `▷ q) = `¬ p `▷ `¬ q
