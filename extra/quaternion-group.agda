{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.quaternion-group where

open import book public

--------------------------------------------------------------------------------

-- We define the abstract group Q8

data Q8 : UU lzero where
  e-Q8  : Q8
  -e-Q8 : Q8
  i-Q8  : Q8
  -i-Q8 : Q8
  j-Q8  : Q8
  -j-Q8 : Q8
  k-Q8  : Q8
  -k-Q8 : Q8

mul-Q8 : Q8 → Q8 → Q8
mul-Q8 e-Q8 e-Q8 = e-Q8
mul-Q8 e-Q8 -e-Q8 = -e-Q8
mul-Q8 e-Q8 i-Q8 = i-Q8
mul-Q8 e-Q8 -i-Q8 = -i-Q8
mul-Q8 e-Q8 j-Q8 = j-Q8
mul-Q8 e-Q8 -j-Q8 = -j-Q8
mul-Q8 e-Q8 k-Q8 = k-Q8
mul-Q8 e-Q8 -k-Q8 = -k-Q8
mul-Q8 -e-Q8 e-Q8 = -e-Q8
mul-Q8 -e-Q8 -e-Q8 = e-Q8
mul-Q8 -e-Q8 i-Q8 = -i-Q8
mul-Q8 -e-Q8 -i-Q8 = i-Q8
mul-Q8 -e-Q8 j-Q8 = -j-Q8
mul-Q8 -e-Q8 -j-Q8 = j-Q8
mul-Q8 -e-Q8 k-Q8 = -k-Q8
mul-Q8 -e-Q8 -k-Q8 = k-Q8
mul-Q8 i-Q8 e-Q8 = i-Q8
mul-Q8 i-Q8 -e-Q8 = -i-Q8
mul-Q8 i-Q8 i-Q8 = -e-Q8
mul-Q8 i-Q8 -i-Q8 = e-Q8
mul-Q8 i-Q8 j-Q8 = k-Q8
mul-Q8 i-Q8 -j-Q8 = -k-Q8
mul-Q8 i-Q8 k-Q8 = -j-Q8
mul-Q8 i-Q8 -k-Q8 = j-Q8
mul-Q8 -i-Q8 e-Q8 = -i-Q8
mul-Q8 -i-Q8 -e-Q8 = i-Q8
mul-Q8 -i-Q8 i-Q8 = e-Q8
mul-Q8 -i-Q8 -i-Q8 = -e-Q8
mul-Q8 -i-Q8 j-Q8 = -k-Q8
mul-Q8 -i-Q8 -j-Q8 = k-Q8
mul-Q8 -i-Q8 k-Q8 = j-Q8
mul-Q8 -i-Q8 -k-Q8 = -j-Q8
mul-Q8 j-Q8 e-Q8 = j-Q8
mul-Q8 j-Q8 -e-Q8 = -j-Q8
mul-Q8 j-Q8 i-Q8 = -k-Q8
mul-Q8 j-Q8 -i-Q8 = k-Q8
mul-Q8 j-Q8 j-Q8 = -e-Q8
mul-Q8 j-Q8 -j-Q8 = e-Q8
mul-Q8 j-Q8 k-Q8 = i-Q8
mul-Q8 j-Q8 -k-Q8 = -i-Q8
mul-Q8 -j-Q8 e-Q8 = -j-Q8
mul-Q8 -j-Q8 -e-Q8 = j-Q8
mul-Q8 -j-Q8 i-Q8 = k-Q8
mul-Q8 -j-Q8 -i-Q8 = -k-Q8
mul-Q8 -j-Q8 j-Q8 = e-Q8
mul-Q8 -j-Q8 -j-Q8 = -e-Q8
mul-Q8 -j-Q8 k-Q8 = -i-Q8
mul-Q8 -j-Q8 -k-Q8 = i-Q8
mul-Q8 k-Q8 e-Q8 = k-Q8
mul-Q8 k-Q8 -e-Q8 = -k-Q8
mul-Q8 k-Q8 i-Q8 = j-Q8
mul-Q8 k-Q8 -i-Q8 = -j-Q8
mul-Q8 k-Q8 j-Q8 = -i-Q8
mul-Q8 k-Q8 -j-Q8 = i-Q8
mul-Q8 k-Q8 k-Q8 = -e-Q8
mul-Q8 k-Q8 -k-Q8 = e-Q8
mul-Q8 -k-Q8 e-Q8 = -k-Q8
mul-Q8 -k-Q8 -e-Q8 = k-Q8
mul-Q8 -k-Q8 i-Q8 = -j-Q8
mul-Q8 -k-Q8 -i-Q8 = j-Q8
mul-Q8 -k-Q8 j-Q8 = i-Q8
mul-Q8 -k-Q8 -j-Q8 = -i-Q8
mul-Q8 -k-Q8 k-Q8 = e-Q8
mul-Q8 -k-Q8 -k-Q8 = -e-Q8

inv-Q8 : Q8 → Q8
inv-Q8 e-Q8 = e-Q8
inv-Q8 -e-Q8 = -e-Q8
inv-Q8 i-Q8 = -i-Q8
inv-Q8 -i-Q8 = i-Q8
inv-Q8 j-Q8 = -j-Q8
inv-Q8 -j-Q8 = j-Q8
inv-Q8 k-Q8 = -k-Q8
inv-Q8 -k-Q8 = k-Q8

left-unit-law-mul-Q8 : (x : Q8) → Id (mul-Q8 e-Q8 x) x
left-unit-law-mul-Q8 e-Q8 = refl
left-unit-law-mul-Q8 -e-Q8 = refl
left-unit-law-mul-Q8 i-Q8 = refl
left-unit-law-mul-Q8 -i-Q8 = refl
left-unit-law-mul-Q8 j-Q8 = refl
left-unit-law-mul-Q8 -j-Q8 = refl
left-unit-law-mul-Q8 k-Q8 = refl
left-unit-law-mul-Q8 -k-Q8 = refl

right-unit-law-mul-Q8 : (x : Q8) → Id (mul-Q8 x e-Q8) x
right-unit-law-mul-Q8 e-Q8 = refl
right-unit-law-mul-Q8 -e-Q8 = refl
right-unit-law-mul-Q8 i-Q8 = refl
right-unit-law-mul-Q8 -i-Q8 = refl
right-unit-law-mul-Q8 j-Q8 = refl
right-unit-law-mul-Q8 -j-Q8 = refl
right-unit-law-mul-Q8 k-Q8 = refl
right-unit-law-mul-Q8 -k-Q8 = refl

associative-mul-Q8 :
  (x y z : Q8) → Id (mul-Q8 (mul-Q8 x y) z) (mul-Q8 x (mul-Q8 y z))
associative-mul-Q8 e-Q8 e-Q8 e-Q8 = refl
associative-mul-Q8 e-Q8 e-Q8 -e-Q8 = refl
associative-mul-Q8 e-Q8 e-Q8 i-Q8 = refl
associative-mul-Q8 e-Q8 e-Q8 -i-Q8 = refl
associative-mul-Q8 e-Q8 e-Q8 j-Q8 = refl
associative-mul-Q8 e-Q8 e-Q8 -j-Q8 = refl
associative-mul-Q8 e-Q8 e-Q8 k-Q8 = refl
associative-mul-Q8 e-Q8 e-Q8 -k-Q8 = refl
associative-mul-Q8 e-Q8 -e-Q8 e-Q8 = refl
associative-mul-Q8 e-Q8 -e-Q8 -e-Q8 = refl
associative-mul-Q8 e-Q8 -e-Q8 i-Q8 = refl
associative-mul-Q8 e-Q8 -e-Q8 -i-Q8 = refl
associative-mul-Q8 e-Q8 -e-Q8 j-Q8 = refl
associative-mul-Q8 e-Q8 -e-Q8 -j-Q8 = refl
associative-mul-Q8 e-Q8 -e-Q8 k-Q8 = refl
associative-mul-Q8 e-Q8 -e-Q8 -k-Q8 = refl
associative-mul-Q8 e-Q8 i-Q8 e-Q8 = refl
associative-mul-Q8 e-Q8 i-Q8 -e-Q8 = refl
associative-mul-Q8 e-Q8 i-Q8 i-Q8 = refl
associative-mul-Q8 e-Q8 i-Q8 -i-Q8 = refl
associative-mul-Q8 e-Q8 i-Q8 j-Q8 = refl
associative-mul-Q8 e-Q8 i-Q8 -j-Q8 = refl
associative-mul-Q8 e-Q8 i-Q8 k-Q8 = refl
associative-mul-Q8 e-Q8 i-Q8 -k-Q8 = refl
associative-mul-Q8 e-Q8 -i-Q8 e-Q8 = refl
associative-mul-Q8 e-Q8 -i-Q8 -e-Q8 = refl
associative-mul-Q8 e-Q8 -i-Q8 i-Q8 = refl
associative-mul-Q8 e-Q8 -i-Q8 -i-Q8 = refl
associative-mul-Q8 e-Q8 -i-Q8 j-Q8 = refl
associative-mul-Q8 e-Q8 -i-Q8 -j-Q8 = refl
associative-mul-Q8 e-Q8 -i-Q8 k-Q8 = refl
associative-mul-Q8 e-Q8 -i-Q8 -k-Q8 = refl
associative-mul-Q8 e-Q8 j-Q8 e-Q8 = refl
associative-mul-Q8 e-Q8 j-Q8 -e-Q8 = refl
associative-mul-Q8 e-Q8 j-Q8 i-Q8 = refl
associative-mul-Q8 e-Q8 j-Q8 -i-Q8 = refl
associative-mul-Q8 e-Q8 j-Q8 j-Q8 = refl
associative-mul-Q8 e-Q8 j-Q8 -j-Q8 = refl
associative-mul-Q8 e-Q8 j-Q8 k-Q8 = refl
associative-mul-Q8 e-Q8 j-Q8 -k-Q8 = refl
associative-mul-Q8 e-Q8 -j-Q8 e-Q8 = refl
associative-mul-Q8 e-Q8 -j-Q8 -e-Q8 = refl
associative-mul-Q8 e-Q8 -j-Q8 i-Q8 = refl
associative-mul-Q8 e-Q8 -j-Q8 -i-Q8 = refl
associative-mul-Q8 e-Q8 -j-Q8 j-Q8 = refl
associative-mul-Q8 e-Q8 -j-Q8 -j-Q8 = refl
associative-mul-Q8 e-Q8 -j-Q8 k-Q8 = refl
associative-mul-Q8 e-Q8 -j-Q8 -k-Q8 = refl
associative-mul-Q8 e-Q8 k-Q8 e-Q8 = refl
associative-mul-Q8 e-Q8 k-Q8 -e-Q8 = refl
associative-mul-Q8 e-Q8 k-Q8 i-Q8 = refl
associative-mul-Q8 e-Q8 k-Q8 -i-Q8 = refl
associative-mul-Q8 e-Q8 k-Q8 j-Q8 = refl
associative-mul-Q8 e-Q8 k-Q8 -j-Q8 = refl
associative-mul-Q8 e-Q8 k-Q8 k-Q8 = refl
associative-mul-Q8 e-Q8 k-Q8 -k-Q8 = refl
associative-mul-Q8 e-Q8 -k-Q8 e-Q8 = refl
associative-mul-Q8 e-Q8 -k-Q8 -e-Q8 = refl
associative-mul-Q8 e-Q8 -k-Q8 i-Q8 = refl
associative-mul-Q8 e-Q8 -k-Q8 -i-Q8 = refl
associative-mul-Q8 e-Q8 -k-Q8 j-Q8 = refl
associative-mul-Q8 e-Q8 -k-Q8 -j-Q8 = refl
associative-mul-Q8 e-Q8 -k-Q8 k-Q8 = refl
associative-mul-Q8 e-Q8 -k-Q8 -k-Q8 = refl
associative-mul-Q8 -e-Q8 e-Q8 e-Q8 = refl
associative-mul-Q8 -e-Q8 e-Q8 -e-Q8 = refl
associative-mul-Q8 -e-Q8 e-Q8 i-Q8 = refl
associative-mul-Q8 -e-Q8 e-Q8 -i-Q8 = refl
associative-mul-Q8 -e-Q8 e-Q8 j-Q8 = refl
associative-mul-Q8 -e-Q8 e-Q8 -j-Q8 = refl
associative-mul-Q8 -e-Q8 e-Q8 k-Q8 = refl
associative-mul-Q8 -e-Q8 e-Q8 -k-Q8 = refl
associative-mul-Q8 -e-Q8 -e-Q8 e-Q8 = refl
associative-mul-Q8 -e-Q8 -e-Q8 -e-Q8 = refl
associative-mul-Q8 -e-Q8 -e-Q8 i-Q8 = refl
associative-mul-Q8 -e-Q8 -e-Q8 -i-Q8 = refl
associative-mul-Q8 -e-Q8 -e-Q8 j-Q8 = refl
associative-mul-Q8 -e-Q8 -e-Q8 -j-Q8 = refl
associative-mul-Q8 -e-Q8 -e-Q8 k-Q8 = refl
associative-mul-Q8 -e-Q8 -e-Q8 -k-Q8 = refl
associative-mul-Q8 -e-Q8 i-Q8 e-Q8 = refl
associative-mul-Q8 -e-Q8 i-Q8 -e-Q8 = refl
associative-mul-Q8 -e-Q8 i-Q8 i-Q8 = refl
associative-mul-Q8 -e-Q8 i-Q8 -i-Q8 = refl
associative-mul-Q8 -e-Q8 i-Q8 j-Q8 = refl
associative-mul-Q8 -e-Q8 i-Q8 -j-Q8 = refl
associative-mul-Q8 -e-Q8 i-Q8 k-Q8 = refl
associative-mul-Q8 -e-Q8 i-Q8 -k-Q8 = refl
associative-mul-Q8 -e-Q8 -i-Q8 e-Q8 = refl
associative-mul-Q8 -e-Q8 -i-Q8 -e-Q8 = refl
associative-mul-Q8 -e-Q8 -i-Q8 i-Q8 = refl
associative-mul-Q8 -e-Q8 -i-Q8 -i-Q8 = refl
associative-mul-Q8 -e-Q8 -i-Q8 j-Q8 = refl
associative-mul-Q8 -e-Q8 -i-Q8 -j-Q8 = refl
associative-mul-Q8 -e-Q8 -i-Q8 k-Q8 = refl
associative-mul-Q8 -e-Q8 -i-Q8 -k-Q8 = refl
associative-mul-Q8 -e-Q8 j-Q8 e-Q8 = refl
associative-mul-Q8 -e-Q8 j-Q8 -e-Q8 = refl
associative-mul-Q8 -e-Q8 j-Q8 i-Q8 = refl
associative-mul-Q8 -e-Q8 j-Q8 -i-Q8 = refl
associative-mul-Q8 -e-Q8 j-Q8 j-Q8 = refl
associative-mul-Q8 -e-Q8 j-Q8 -j-Q8 = refl
associative-mul-Q8 -e-Q8 j-Q8 k-Q8 = refl
associative-mul-Q8 -e-Q8 j-Q8 -k-Q8 = refl
associative-mul-Q8 -e-Q8 -j-Q8 e-Q8 = refl
associative-mul-Q8 -e-Q8 -j-Q8 -e-Q8 = refl
associative-mul-Q8 -e-Q8 -j-Q8 i-Q8 = refl
associative-mul-Q8 -e-Q8 -j-Q8 -i-Q8 = refl
associative-mul-Q8 -e-Q8 -j-Q8 j-Q8 = refl
associative-mul-Q8 -e-Q8 -j-Q8 -j-Q8 = refl
associative-mul-Q8 -e-Q8 -j-Q8 k-Q8 = refl
associative-mul-Q8 -e-Q8 -j-Q8 -k-Q8 = refl
associative-mul-Q8 -e-Q8 k-Q8 e-Q8 = refl
associative-mul-Q8 -e-Q8 k-Q8 -e-Q8 = refl
associative-mul-Q8 -e-Q8 k-Q8 i-Q8 = refl
associative-mul-Q8 -e-Q8 k-Q8 -i-Q8 = refl
associative-mul-Q8 -e-Q8 k-Q8 j-Q8 = refl
associative-mul-Q8 -e-Q8 k-Q8 -j-Q8 = refl
associative-mul-Q8 -e-Q8 k-Q8 k-Q8 = refl
associative-mul-Q8 -e-Q8 k-Q8 -k-Q8 = refl
associative-mul-Q8 -e-Q8 -k-Q8 e-Q8 = refl
associative-mul-Q8 -e-Q8 -k-Q8 -e-Q8 = refl
associative-mul-Q8 -e-Q8 -k-Q8 i-Q8 = refl
associative-mul-Q8 -e-Q8 -k-Q8 -i-Q8 = refl
associative-mul-Q8 -e-Q8 -k-Q8 j-Q8 = refl
associative-mul-Q8 -e-Q8 -k-Q8 -j-Q8 = refl
associative-mul-Q8 -e-Q8 -k-Q8 k-Q8 = refl
associative-mul-Q8 -e-Q8 -k-Q8 -k-Q8 = refl
associative-mul-Q8 i-Q8 e-Q8 e-Q8 = refl
associative-mul-Q8 i-Q8 e-Q8 -e-Q8 = refl
associative-mul-Q8 i-Q8 e-Q8 i-Q8 = refl
associative-mul-Q8 i-Q8 e-Q8 -i-Q8 = refl
associative-mul-Q8 i-Q8 e-Q8 j-Q8 = refl
associative-mul-Q8 i-Q8 e-Q8 -j-Q8 = refl
associative-mul-Q8 i-Q8 e-Q8 k-Q8 = refl
associative-mul-Q8 i-Q8 e-Q8 -k-Q8 = refl
associative-mul-Q8 i-Q8 -e-Q8 e-Q8 = refl
associative-mul-Q8 i-Q8 -e-Q8 -e-Q8 = refl
associative-mul-Q8 i-Q8 -e-Q8 i-Q8 = refl
associative-mul-Q8 i-Q8 -e-Q8 -i-Q8 = refl
associative-mul-Q8 i-Q8 -e-Q8 j-Q8 = refl
associative-mul-Q8 i-Q8 -e-Q8 -j-Q8 = refl
associative-mul-Q8 i-Q8 -e-Q8 k-Q8 = refl
associative-mul-Q8 i-Q8 -e-Q8 -k-Q8 = refl
associative-mul-Q8 i-Q8 i-Q8 e-Q8 = refl
associative-mul-Q8 i-Q8 i-Q8 -e-Q8 = refl
associative-mul-Q8 i-Q8 i-Q8 i-Q8 = refl
associative-mul-Q8 i-Q8 i-Q8 -i-Q8 = refl
associative-mul-Q8 i-Q8 i-Q8 j-Q8 = refl
associative-mul-Q8 i-Q8 i-Q8 -j-Q8 = refl
associative-mul-Q8 i-Q8 i-Q8 k-Q8 = refl
associative-mul-Q8 i-Q8 i-Q8 -k-Q8 = refl
associative-mul-Q8 i-Q8 -i-Q8 e-Q8 = refl
associative-mul-Q8 i-Q8 -i-Q8 -e-Q8 = refl
associative-mul-Q8 i-Q8 -i-Q8 i-Q8 = refl
associative-mul-Q8 i-Q8 -i-Q8 -i-Q8 = refl
associative-mul-Q8 i-Q8 -i-Q8 j-Q8 = refl
associative-mul-Q8 i-Q8 -i-Q8 -j-Q8 = refl
associative-mul-Q8 i-Q8 -i-Q8 k-Q8 = refl
associative-mul-Q8 i-Q8 -i-Q8 -k-Q8 = refl
associative-mul-Q8 i-Q8 j-Q8 e-Q8 = refl
associative-mul-Q8 i-Q8 j-Q8 -e-Q8 = refl
associative-mul-Q8 i-Q8 j-Q8 i-Q8 = refl
associative-mul-Q8 i-Q8 j-Q8 -i-Q8 = refl
associative-mul-Q8 i-Q8 j-Q8 j-Q8 = refl
associative-mul-Q8 i-Q8 j-Q8 -j-Q8 = refl
associative-mul-Q8 i-Q8 j-Q8 k-Q8 = refl
associative-mul-Q8 i-Q8 j-Q8 -k-Q8 = refl
associative-mul-Q8 i-Q8 -j-Q8 e-Q8 = refl
associative-mul-Q8 i-Q8 -j-Q8 -e-Q8 = refl
associative-mul-Q8 i-Q8 -j-Q8 i-Q8 = refl
associative-mul-Q8 i-Q8 -j-Q8 -i-Q8 = refl
associative-mul-Q8 i-Q8 -j-Q8 j-Q8 = refl
associative-mul-Q8 i-Q8 -j-Q8 -j-Q8 = refl
associative-mul-Q8 i-Q8 -j-Q8 k-Q8 = refl
associative-mul-Q8 i-Q8 -j-Q8 -k-Q8 = refl
associative-mul-Q8 i-Q8 k-Q8 e-Q8 = refl
associative-mul-Q8 i-Q8 k-Q8 -e-Q8 = refl
associative-mul-Q8 i-Q8 k-Q8 i-Q8 = refl
associative-mul-Q8 i-Q8 k-Q8 -i-Q8 = refl
associative-mul-Q8 i-Q8 k-Q8 j-Q8 = refl
associative-mul-Q8 i-Q8 k-Q8 -j-Q8 = refl
associative-mul-Q8 i-Q8 k-Q8 k-Q8 = refl
associative-mul-Q8 i-Q8 k-Q8 -k-Q8 = refl
associative-mul-Q8 i-Q8 -k-Q8 e-Q8 = refl
associative-mul-Q8 i-Q8 -k-Q8 -e-Q8 = refl
associative-mul-Q8 i-Q8 -k-Q8 i-Q8 = refl
associative-mul-Q8 i-Q8 -k-Q8 -i-Q8 = refl
associative-mul-Q8 i-Q8 -k-Q8 j-Q8 = refl
associative-mul-Q8 i-Q8 -k-Q8 -j-Q8 = refl
associative-mul-Q8 i-Q8 -k-Q8 k-Q8 = refl
associative-mul-Q8 i-Q8 -k-Q8 -k-Q8 = refl
associative-mul-Q8 -i-Q8 e-Q8 e-Q8 = refl
associative-mul-Q8 -i-Q8 e-Q8 -e-Q8 = refl
associative-mul-Q8 -i-Q8 e-Q8 i-Q8 = refl
associative-mul-Q8 -i-Q8 e-Q8 -i-Q8 = refl
associative-mul-Q8 -i-Q8 e-Q8 j-Q8 = refl
associative-mul-Q8 -i-Q8 e-Q8 -j-Q8 = refl
associative-mul-Q8 -i-Q8 e-Q8 k-Q8 = refl
associative-mul-Q8 -i-Q8 e-Q8 -k-Q8 = refl
associative-mul-Q8 -i-Q8 -e-Q8 e-Q8 = refl
associative-mul-Q8 -i-Q8 -e-Q8 -e-Q8 = refl
associative-mul-Q8 -i-Q8 -e-Q8 i-Q8 = refl
associative-mul-Q8 -i-Q8 -e-Q8 -i-Q8 = refl
associative-mul-Q8 -i-Q8 -e-Q8 j-Q8 = refl
associative-mul-Q8 -i-Q8 -e-Q8 -j-Q8 = refl
associative-mul-Q8 -i-Q8 -e-Q8 k-Q8 = refl
associative-mul-Q8 -i-Q8 -e-Q8 -k-Q8 = refl
associative-mul-Q8 -i-Q8 i-Q8 e-Q8 = refl
associative-mul-Q8 -i-Q8 i-Q8 -e-Q8 = refl
associative-mul-Q8 -i-Q8 i-Q8 i-Q8 = refl
associative-mul-Q8 -i-Q8 i-Q8 -i-Q8 = refl
associative-mul-Q8 -i-Q8 i-Q8 j-Q8 = refl
associative-mul-Q8 -i-Q8 i-Q8 -j-Q8 = refl
associative-mul-Q8 -i-Q8 i-Q8 k-Q8 = refl
associative-mul-Q8 -i-Q8 i-Q8 -k-Q8 = refl
associative-mul-Q8 -i-Q8 -i-Q8 e-Q8 = refl
associative-mul-Q8 -i-Q8 -i-Q8 -e-Q8 = refl
associative-mul-Q8 -i-Q8 -i-Q8 i-Q8 = refl
associative-mul-Q8 -i-Q8 -i-Q8 -i-Q8 = refl
associative-mul-Q8 -i-Q8 -i-Q8 j-Q8 = refl
associative-mul-Q8 -i-Q8 -i-Q8 -j-Q8 = refl
associative-mul-Q8 -i-Q8 -i-Q8 k-Q8 = refl
associative-mul-Q8 -i-Q8 -i-Q8 -k-Q8 = refl
associative-mul-Q8 -i-Q8 j-Q8 e-Q8 = refl
associative-mul-Q8 -i-Q8 j-Q8 -e-Q8 = refl
associative-mul-Q8 -i-Q8 j-Q8 i-Q8 = refl
associative-mul-Q8 -i-Q8 j-Q8 -i-Q8 = refl
associative-mul-Q8 -i-Q8 j-Q8 j-Q8 = refl
associative-mul-Q8 -i-Q8 j-Q8 -j-Q8 = refl
associative-mul-Q8 -i-Q8 j-Q8 k-Q8 = refl
associative-mul-Q8 -i-Q8 j-Q8 -k-Q8 = refl
associative-mul-Q8 -i-Q8 -j-Q8 e-Q8 = refl
associative-mul-Q8 -i-Q8 -j-Q8 -e-Q8 = refl
associative-mul-Q8 -i-Q8 -j-Q8 i-Q8 = refl
associative-mul-Q8 -i-Q8 -j-Q8 -i-Q8 = refl
associative-mul-Q8 -i-Q8 -j-Q8 j-Q8 = refl
associative-mul-Q8 -i-Q8 -j-Q8 -j-Q8 = refl
associative-mul-Q8 -i-Q8 -j-Q8 k-Q8 = refl
associative-mul-Q8 -i-Q8 -j-Q8 -k-Q8 = refl
associative-mul-Q8 -i-Q8 k-Q8 e-Q8 = refl
associative-mul-Q8 -i-Q8 k-Q8 -e-Q8 = refl
associative-mul-Q8 -i-Q8 k-Q8 i-Q8 = refl
associative-mul-Q8 -i-Q8 k-Q8 -i-Q8 = refl
associative-mul-Q8 -i-Q8 k-Q8 j-Q8 = refl
associative-mul-Q8 -i-Q8 k-Q8 -j-Q8 = refl
associative-mul-Q8 -i-Q8 k-Q8 k-Q8 = refl
associative-mul-Q8 -i-Q8 k-Q8 -k-Q8 = refl
associative-mul-Q8 -i-Q8 -k-Q8 e-Q8 = refl
associative-mul-Q8 -i-Q8 -k-Q8 -e-Q8 = refl
associative-mul-Q8 -i-Q8 -k-Q8 i-Q8 = refl
associative-mul-Q8 -i-Q8 -k-Q8 -i-Q8 = refl
associative-mul-Q8 -i-Q8 -k-Q8 j-Q8 = refl
associative-mul-Q8 -i-Q8 -k-Q8 -j-Q8 = refl
associative-mul-Q8 -i-Q8 -k-Q8 k-Q8 = refl
associative-mul-Q8 -i-Q8 -k-Q8 -k-Q8 = refl
associative-mul-Q8 j-Q8 e-Q8 e-Q8 = refl
associative-mul-Q8 j-Q8 e-Q8 -e-Q8 = refl
associative-mul-Q8 j-Q8 e-Q8 i-Q8 = refl
associative-mul-Q8 j-Q8 e-Q8 -i-Q8 = refl
associative-mul-Q8 j-Q8 e-Q8 j-Q8 = refl
associative-mul-Q8 j-Q8 e-Q8 -j-Q8 = refl
associative-mul-Q8 j-Q8 e-Q8 k-Q8 = refl
associative-mul-Q8 j-Q8 e-Q8 -k-Q8 = refl
associative-mul-Q8 j-Q8 -e-Q8 e-Q8 = refl
associative-mul-Q8 j-Q8 -e-Q8 -e-Q8 = refl
associative-mul-Q8 j-Q8 -e-Q8 i-Q8 = refl
associative-mul-Q8 j-Q8 -e-Q8 -i-Q8 = refl
associative-mul-Q8 j-Q8 -e-Q8 j-Q8 = refl
associative-mul-Q8 j-Q8 -e-Q8 -j-Q8 = refl
associative-mul-Q8 j-Q8 -e-Q8 k-Q8 = refl
associative-mul-Q8 j-Q8 -e-Q8 -k-Q8 = refl
associative-mul-Q8 j-Q8 i-Q8 e-Q8 = refl
associative-mul-Q8 j-Q8 i-Q8 -e-Q8 = refl
associative-mul-Q8 j-Q8 i-Q8 i-Q8 = refl
associative-mul-Q8 j-Q8 i-Q8 -i-Q8 = refl
associative-mul-Q8 j-Q8 i-Q8 j-Q8 = refl
associative-mul-Q8 j-Q8 i-Q8 -j-Q8 = refl
associative-mul-Q8 j-Q8 i-Q8 k-Q8 = refl
associative-mul-Q8 j-Q8 i-Q8 -k-Q8 = refl
associative-mul-Q8 j-Q8 -i-Q8 e-Q8 = refl
associative-mul-Q8 j-Q8 -i-Q8 -e-Q8 = refl
associative-mul-Q8 j-Q8 -i-Q8 i-Q8 = refl
associative-mul-Q8 j-Q8 -i-Q8 -i-Q8 = refl
associative-mul-Q8 j-Q8 -i-Q8 j-Q8 = refl
associative-mul-Q8 j-Q8 -i-Q8 -j-Q8 = refl
associative-mul-Q8 j-Q8 -i-Q8 k-Q8 = refl
associative-mul-Q8 j-Q8 -i-Q8 -k-Q8 = refl
associative-mul-Q8 j-Q8 j-Q8 e-Q8 = refl
associative-mul-Q8 j-Q8 j-Q8 -e-Q8 = refl
associative-mul-Q8 j-Q8 j-Q8 i-Q8 = refl
associative-mul-Q8 j-Q8 j-Q8 -i-Q8 = refl
associative-mul-Q8 j-Q8 j-Q8 j-Q8 = refl
associative-mul-Q8 j-Q8 j-Q8 -j-Q8 = refl
associative-mul-Q8 j-Q8 j-Q8 k-Q8 = refl
associative-mul-Q8 j-Q8 j-Q8 -k-Q8 = refl
associative-mul-Q8 j-Q8 -j-Q8 e-Q8 = refl
associative-mul-Q8 j-Q8 -j-Q8 -e-Q8 = refl
associative-mul-Q8 j-Q8 -j-Q8 i-Q8 = refl
associative-mul-Q8 j-Q8 -j-Q8 -i-Q8 = refl
associative-mul-Q8 j-Q8 -j-Q8 j-Q8 = refl
associative-mul-Q8 j-Q8 -j-Q8 -j-Q8 = refl
associative-mul-Q8 j-Q8 -j-Q8 k-Q8 = refl
associative-mul-Q8 j-Q8 -j-Q8 -k-Q8 = refl
associative-mul-Q8 j-Q8 k-Q8 e-Q8 = refl
associative-mul-Q8 j-Q8 k-Q8 -e-Q8 = refl
associative-mul-Q8 j-Q8 k-Q8 i-Q8 = refl
associative-mul-Q8 j-Q8 k-Q8 -i-Q8 = refl
associative-mul-Q8 j-Q8 k-Q8 j-Q8 = refl
associative-mul-Q8 j-Q8 k-Q8 -j-Q8 = refl
associative-mul-Q8 j-Q8 k-Q8 k-Q8 = refl
associative-mul-Q8 j-Q8 k-Q8 -k-Q8 = refl
associative-mul-Q8 j-Q8 -k-Q8 e-Q8 = refl
associative-mul-Q8 j-Q8 -k-Q8 -e-Q8 = refl
associative-mul-Q8 j-Q8 -k-Q8 i-Q8 = refl
associative-mul-Q8 j-Q8 -k-Q8 -i-Q8 = refl
associative-mul-Q8 j-Q8 -k-Q8 j-Q8 = refl
associative-mul-Q8 j-Q8 -k-Q8 -j-Q8 = refl
associative-mul-Q8 j-Q8 -k-Q8 k-Q8 = refl
associative-mul-Q8 j-Q8 -k-Q8 -k-Q8 = refl
associative-mul-Q8 -j-Q8 e-Q8 e-Q8 = refl
associative-mul-Q8 -j-Q8 e-Q8 -e-Q8 = refl
associative-mul-Q8 -j-Q8 e-Q8 i-Q8 = refl
associative-mul-Q8 -j-Q8 e-Q8 -i-Q8 = refl
associative-mul-Q8 -j-Q8 e-Q8 j-Q8 = refl
associative-mul-Q8 -j-Q8 e-Q8 -j-Q8 = refl
associative-mul-Q8 -j-Q8 e-Q8 k-Q8 = refl
associative-mul-Q8 -j-Q8 e-Q8 -k-Q8 = refl
associative-mul-Q8 -j-Q8 -e-Q8 e-Q8 = refl
associative-mul-Q8 -j-Q8 -e-Q8 -e-Q8 = refl
associative-mul-Q8 -j-Q8 -e-Q8 i-Q8 = refl
associative-mul-Q8 -j-Q8 -e-Q8 -i-Q8 = refl
associative-mul-Q8 -j-Q8 -e-Q8 j-Q8 = refl
associative-mul-Q8 -j-Q8 -e-Q8 -j-Q8 = refl
associative-mul-Q8 -j-Q8 -e-Q8 k-Q8 = refl
associative-mul-Q8 -j-Q8 -e-Q8 -k-Q8 = refl
associative-mul-Q8 -j-Q8 i-Q8 e-Q8 = refl
associative-mul-Q8 -j-Q8 i-Q8 -e-Q8 = refl
associative-mul-Q8 -j-Q8 i-Q8 i-Q8 = refl
associative-mul-Q8 -j-Q8 i-Q8 -i-Q8 = refl
associative-mul-Q8 -j-Q8 i-Q8 j-Q8 = refl
associative-mul-Q8 -j-Q8 i-Q8 -j-Q8 = refl
associative-mul-Q8 -j-Q8 i-Q8 k-Q8 = refl
associative-mul-Q8 -j-Q8 i-Q8 -k-Q8 = refl
associative-mul-Q8 -j-Q8 -i-Q8 e-Q8 = refl
associative-mul-Q8 -j-Q8 -i-Q8 -e-Q8 = refl
associative-mul-Q8 -j-Q8 -i-Q8 i-Q8 = refl
associative-mul-Q8 -j-Q8 -i-Q8 -i-Q8 = refl
associative-mul-Q8 -j-Q8 -i-Q8 j-Q8 = refl
associative-mul-Q8 -j-Q8 -i-Q8 -j-Q8 = refl
associative-mul-Q8 -j-Q8 -i-Q8 k-Q8 = refl
associative-mul-Q8 -j-Q8 -i-Q8 -k-Q8 = refl
associative-mul-Q8 -j-Q8 j-Q8 e-Q8 = refl
associative-mul-Q8 -j-Q8 j-Q8 -e-Q8 = refl
associative-mul-Q8 -j-Q8 j-Q8 i-Q8 = refl
associative-mul-Q8 -j-Q8 j-Q8 -i-Q8 = refl
associative-mul-Q8 -j-Q8 j-Q8 j-Q8 = refl
associative-mul-Q8 -j-Q8 j-Q8 -j-Q8 = refl
associative-mul-Q8 -j-Q8 j-Q8 k-Q8 = refl
associative-mul-Q8 -j-Q8 j-Q8 -k-Q8 = refl
associative-mul-Q8 -j-Q8 -j-Q8 e-Q8 = refl
associative-mul-Q8 -j-Q8 -j-Q8 -e-Q8 = refl
associative-mul-Q8 -j-Q8 -j-Q8 i-Q8 = refl
associative-mul-Q8 -j-Q8 -j-Q8 -i-Q8 = refl
associative-mul-Q8 -j-Q8 -j-Q8 j-Q8 = refl
associative-mul-Q8 -j-Q8 -j-Q8 -j-Q8 = refl
associative-mul-Q8 -j-Q8 -j-Q8 k-Q8 = refl
associative-mul-Q8 -j-Q8 -j-Q8 -k-Q8 = refl
associative-mul-Q8 -j-Q8 k-Q8 e-Q8 = refl
associative-mul-Q8 -j-Q8 k-Q8 -e-Q8 = refl
associative-mul-Q8 -j-Q8 k-Q8 i-Q8 = refl
associative-mul-Q8 -j-Q8 k-Q8 -i-Q8 = refl
associative-mul-Q8 -j-Q8 k-Q8 j-Q8 = refl
associative-mul-Q8 -j-Q8 k-Q8 -j-Q8 = refl
associative-mul-Q8 -j-Q8 k-Q8 k-Q8 = refl
associative-mul-Q8 -j-Q8 k-Q8 -k-Q8 = refl
associative-mul-Q8 -j-Q8 -k-Q8 e-Q8 = refl
associative-mul-Q8 -j-Q8 -k-Q8 -e-Q8 = refl
associative-mul-Q8 -j-Q8 -k-Q8 i-Q8 = refl
associative-mul-Q8 -j-Q8 -k-Q8 -i-Q8 = refl
associative-mul-Q8 -j-Q8 -k-Q8 j-Q8 = refl
associative-mul-Q8 -j-Q8 -k-Q8 -j-Q8 = refl
associative-mul-Q8 -j-Q8 -k-Q8 k-Q8 = refl
associative-mul-Q8 -j-Q8 -k-Q8 -k-Q8 = refl
associative-mul-Q8 k-Q8 e-Q8 e-Q8 = refl
associative-mul-Q8 k-Q8 e-Q8 -e-Q8 = refl
associative-mul-Q8 k-Q8 e-Q8 i-Q8 = refl
associative-mul-Q8 k-Q8 e-Q8 -i-Q8 = refl
associative-mul-Q8 k-Q8 e-Q8 j-Q8 = refl
associative-mul-Q8 k-Q8 e-Q8 -j-Q8 = refl
associative-mul-Q8 k-Q8 e-Q8 k-Q8 = refl
associative-mul-Q8 k-Q8 e-Q8 -k-Q8 = refl
associative-mul-Q8 k-Q8 -e-Q8 e-Q8 = refl
associative-mul-Q8 k-Q8 -e-Q8 -e-Q8 = refl
associative-mul-Q8 k-Q8 -e-Q8 i-Q8 = refl
associative-mul-Q8 k-Q8 -e-Q8 -i-Q8 = refl
associative-mul-Q8 k-Q8 -e-Q8 j-Q8 = refl
associative-mul-Q8 k-Q8 -e-Q8 -j-Q8 = refl
associative-mul-Q8 k-Q8 -e-Q8 k-Q8 = refl
associative-mul-Q8 k-Q8 -e-Q8 -k-Q8 = refl
associative-mul-Q8 k-Q8 i-Q8 e-Q8 = refl
associative-mul-Q8 k-Q8 i-Q8 -e-Q8 = refl
associative-mul-Q8 k-Q8 i-Q8 i-Q8 = refl
associative-mul-Q8 k-Q8 i-Q8 -i-Q8 = refl
associative-mul-Q8 k-Q8 i-Q8 j-Q8 = refl
associative-mul-Q8 k-Q8 i-Q8 -j-Q8 = refl
associative-mul-Q8 k-Q8 i-Q8 k-Q8 = refl
associative-mul-Q8 k-Q8 i-Q8 -k-Q8 = refl
associative-mul-Q8 k-Q8 -i-Q8 e-Q8 = refl
associative-mul-Q8 k-Q8 -i-Q8 -e-Q8 = refl
associative-mul-Q8 k-Q8 -i-Q8 i-Q8 = refl
associative-mul-Q8 k-Q8 -i-Q8 -i-Q8 = refl
associative-mul-Q8 k-Q8 -i-Q8 j-Q8 = refl
associative-mul-Q8 k-Q8 -i-Q8 -j-Q8 = refl
associative-mul-Q8 k-Q8 -i-Q8 k-Q8 = refl
associative-mul-Q8 k-Q8 -i-Q8 -k-Q8 = refl
associative-mul-Q8 k-Q8 j-Q8 e-Q8 = refl
associative-mul-Q8 k-Q8 j-Q8 -e-Q8 = refl
associative-mul-Q8 k-Q8 j-Q8 i-Q8 = refl
associative-mul-Q8 k-Q8 j-Q8 -i-Q8 = refl
associative-mul-Q8 k-Q8 j-Q8 j-Q8 = refl
associative-mul-Q8 k-Q8 j-Q8 -j-Q8 = refl
associative-mul-Q8 k-Q8 j-Q8 k-Q8 = refl
associative-mul-Q8 k-Q8 j-Q8 -k-Q8 = refl
associative-mul-Q8 k-Q8 -j-Q8 e-Q8 = refl
associative-mul-Q8 k-Q8 -j-Q8 -e-Q8 = refl
associative-mul-Q8 k-Q8 -j-Q8 i-Q8 = refl
associative-mul-Q8 k-Q8 -j-Q8 -i-Q8 = refl
associative-mul-Q8 k-Q8 -j-Q8 j-Q8 = refl
associative-mul-Q8 k-Q8 -j-Q8 -j-Q8 = refl
associative-mul-Q8 k-Q8 -j-Q8 k-Q8 = refl
associative-mul-Q8 k-Q8 -j-Q8 -k-Q8 = refl
associative-mul-Q8 k-Q8 k-Q8 e-Q8 = refl
associative-mul-Q8 k-Q8 k-Q8 -e-Q8 = refl
associative-mul-Q8 k-Q8 k-Q8 i-Q8 = refl
associative-mul-Q8 k-Q8 k-Q8 -i-Q8 = refl
associative-mul-Q8 k-Q8 k-Q8 j-Q8 = refl
associative-mul-Q8 k-Q8 k-Q8 -j-Q8 = refl
associative-mul-Q8 k-Q8 k-Q8 k-Q8 = refl
associative-mul-Q8 k-Q8 k-Q8 -k-Q8 = refl
associative-mul-Q8 k-Q8 -k-Q8 e-Q8 = refl
associative-mul-Q8 k-Q8 -k-Q8 -e-Q8 = refl
associative-mul-Q8 k-Q8 -k-Q8 i-Q8 = refl
associative-mul-Q8 k-Q8 -k-Q8 -i-Q8 = refl
associative-mul-Q8 k-Q8 -k-Q8 j-Q8 = refl
associative-mul-Q8 k-Q8 -k-Q8 -j-Q8 = refl
associative-mul-Q8 k-Q8 -k-Q8 k-Q8 = refl
associative-mul-Q8 k-Q8 -k-Q8 -k-Q8 = refl
associative-mul-Q8 -k-Q8 e-Q8 e-Q8 = refl
associative-mul-Q8 -k-Q8 e-Q8 -e-Q8 = refl
associative-mul-Q8 -k-Q8 e-Q8 i-Q8 = refl
associative-mul-Q8 -k-Q8 e-Q8 -i-Q8 = refl
associative-mul-Q8 -k-Q8 e-Q8 j-Q8 = refl
associative-mul-Q8 -k-Q8 e-Q8 -j-Q8 = refl
associative-mul-Q8 -k-Q8 e-Q8 k-Q8 = refl
associative-mul-Q8 -k-Q8 e-Q8 -k-Q8 = refl
associative-mul-Q8 -k-Q8 -e-Q8 e-Q8 = refl
associative-mul-Q8 -k-Q8 -e-Q8 -e-Q8 = refl
associative-mul-Q8 -k-Q8 -e-Q8 i-Q8 = refl
associative-mul-Q8 -k-Q8 -e-Q8 -i-Q8 = refl
associative-mul-Q8 -k-Q8 -e-Q8 j-Q8 = refl
associative-mul-Q8 -k-Q8 -e-Q8 -j-Q8 = refl
associative-mul-Q8 -k-Q8 -e-Q8 k-Q8 = refl
associative-mul-Q8 -k-Q8 -e-Q8 -k-Q8 = refl
associative-mul-Q8 -k-Q8 i-Q8 e-Q8 = refl
associative-mul-Q8 -k-Q8 i-Q8 -e-Q8 = refl
associative-mul-Q8 -k-Q8 i-Q8 i-Q8 = refl
associative-mul-Q8 -k-Q8 i-Q8 -i-Q8 = refl
associative-mul-Q8 -k-Q8 i-Q8 j-Q8 = refl
associative-mul-Q8 -k-Q8 i-Q8 -j-Q8 = refl
associative-mul-Q8 -k-Q8 i-Q8 k-Q8 = refl
associative-mul-Q8 -k-Q8 i-Q8 -k-Q8 = refl
associative-mul-Q8 -k-Q8 -i-Q8 e-Q8 = refl
associative-mul-Q8 -k-Q8 -i-Q8 -e-Q8 = refl
associative-mul-Q8 -k-Q8 -i-Q8 i-Q8 = refl
associative-mul-Q8 -k-Q8 -i-Q8 -i-Q8 = refl
associative-mul-Q8 -k-Q8 -i-Q8 j-Q8 = refl
associative-mul-Q8 -k-Q8 -i-Q8 -j-Q8 = refl
associative-mul-Q8 -k-Q8 -i-Q8 k-Q8 = refl
associative-mul-Q8 -k-Q8 -i-Q8 -k-Q8 = refl
associative-mul-Q8 -k-Q8 j-Q8 e-Q8 = refl
associative-mul-Q8 -k-Q8 j-Q8 -e-Q8 = refl
associative-mul-Q8 -k-Q8 j-Q8 i-Q8 = refl
associative-mul-Q8 -k-Q8 j-Q8 -i-Q8 = refl
associative-mul-Q8 -k-Q8 j-Q8 j-Q8 = refl
associative-mul-Q8 -k-Q8 j-Q8 -j-Q8 = refl
associative-mul-Q8 -k-Q8 j-Q8 k-Q8 = refl
associative-mul-Q8 -k-Q8 j-Q8 -k-Q8 = refl
associative-mul-Q8 -k-Q8 -j-Q8 e-Q8 = refl
associative-mul-Q8 -k-Q8 -j-Q8 -e-Q8 = refl
associative-mul-Q8 -k-Q8 -j-Q8 i-Q8 = refl
associative-mul-Q8 -k-Q8 -j-Q8 -i-Q8 = refl
associative-mul-Q8 -k-Q8 -j-Q8 j-Q8 = refl
associative-mul-Q8 -k-Q8 -j-Q8 -j-Q8 = refl
associative-mul-Q8 -k-Q8 -j-Q8 k-Q8 = refl
associative-mul-Q8 -k-Q8 -j-Q8 -k-Q8 = refl
associative-mul-Q8 -k-Q8 k-Q8 e-Q8 = refl
associative-mul-Q8 -k-Q8 k-Q8 -e-Q8 = refl
associative-mul-Q8 -k-Q8 k-Q8 i-Q8 = refl
associative-mul-Q8 -k-Q8 k-Q8 -i-Q8 = refl
associative-mul-Q8 -k-Q8 k-Q8 j-Q8 = refl
associative-mul-Q8 -k-Q8 k-Q8 -j-Q8 = refl
associative-mul-Q8 -k-Q8 k-Q8 k-Q8 = refl
associative-mul-Q8 -k-Q8 k-Q8 -k-Q8 = refl
associative-mul-Q8 -k-Q8 -k-Q8 e-Q8 = refl
associative-mul-Q8 -k-Q8 -k-Q8 -e-Q8 = refl
associative-mul-Q8 -k-Q8 -k-Q8 i-Q8 = refl
associative-mul-Q8 -k-Q8 -k-Q8 -i-Q8 = refl
associative-mul-Q8 -k-Q8 -k-Q8 j-Q8 = refl
associative-mul-Q8 -k-Q8 -k-Q8 -j-Q8 = refl
associative-mul-Q8 -k-Q8 -k-Q8 k-Q8 = refl
associative-mul-Q8 -k-Q8 -k-Q8 -k-Q8 = refl

left-inverse-law-mul-Q8 : (x : Q8) → Id (mul-Q8 (inv-Q8 x) x) e-Q8
left-inverse-law-mul-Q8 e-Q8 = refl
left-inverse-law-mul-Q8 -e-Q8 = refl
left-inverse-law-mul-Q8 i-Q8 = refl
left-inverse-law-mul-Q8 -i-Q8 = refl
left-inverse-law-mul-Q8 j-Q8 = refl
left-inverse-law-mul-Q8 -j-Q8 = refl
left-inverse-law-mul-Q8 k-Q8 = refl
left-inverse-law-mul-Q8 -k-Q8 = refl

right-inverse-law-mul-Q8 : (x : Q8) → Id (mul-Q8 x (inv-Q8 x)) e-Q8
right-inverse-law-mul-Q8 e-Q8 = refl
right-inverse-law-mul-Q8 -e-Q8 = refl
right-inverse-law-mul-Q8 i-Q8 = refl
right-inverse-law-mul-Q8 -i-Q8 = refl
right-inverse-law-mul-Q8 j-Q8 = refl
right-inverse-law-mul-Q8 -j-Q8 = refl
right-inverse-law-mul-Q8 k-Q8 = refl
right-inverse-law-mul-Q8 -k-Q8 = refl

Eq-Q8 : Q8 → Q8 → UU lzero
Eq-Q8 e-Q8 e-Q8 = unit
Eq-Q8 e-Q8 -e-Q8 = empty
Eq-Q8 e-Q8 i-Q8 = empty
Eq-Q8 e-Q8 -i-Q8 = empty
Eq-Q8 e-Q8 j-Q8 = empty
Eq-Q8 e-Q8 -j-Q8 = empty
Eq-Q8 e-Q8 k-Q8 = empty
Eq-Q8 e-Q8 -k-Q8 = empty
Eq-Q8 -e-Q8 e-Q8 = empty
Eq-Q8 -e-Q8 -e-Q8 = unit
Eq-Q8 -e-Q8 i-Q8 = empty
Eq-Q8 -e-Q8 -i-Q8 = empty
Eq-Q8 -e-Q8 j-Q8 = empty
Eq-Q8 -e-Q8 -j-Q8 = empty
Eq-Q8 -e-Q8 k-Q8 = empty
Eq-Q8 -e-Q8 -k-Q8 = empty
Eq-Q8 i-Q8 e-Q8 = empty
Eq-Q8 i-Q8 -e-Q8 = empty
Eq-Q8 i-Q8 i-Q8 = unit
Eq-Q8 i-Q8 -i-Q8 = empty
Eq-Q8 i-Q8 j-Q8 = empty
Eq-Q8 i-Q8 -j-Q8 = empty
Eq-Q8 i-Q8 k-Q8 = empty
Eq-Q8 i-Q8 -k-Q8 = empty
Eq-Q8 -i-Q8 e-Q8 = empty
Eq-Q8 -i-Q8 -e-Q8 = empty
Eq-Q8 -i-Q8 i-Q8 = empty
Eq-Q8 -i-Q8 -i-Q8 = unit
Eq-Q8 -i-Q8 j-Q8 = empty
Eq-Q8 -i-Q8 -j-Q8 = empty
Eq-Q8 -i-Q8 k-Q8 = empty
Eq-Q8 -i-Q8 -k-Q8 = empty
Eq-Q8 j-Q8 e-Q8 = empty
Eq-Q8 j-Q8 -e-Q8 = empty
Eq-Q8 j-Q8 i-Q8 = empty
Eq-Q8 j-Q8 -i-Q8 = empty
Eq-Q8 j-Q8 j-Q8 = unit
Eq-Q8 j-Q8 -j-Q8 = empty
Eq-Q8 j-Q8 k-Q8 = empty
Eq-Q8 j-Q8 -k-Q8 = empty
Eq-Q8 -j-Q8 e-Q8 = empty
Eq-Q8 -j-Q8 -e-Q8 = empty
Eq-Q8 -j-Q8 i-Q8 = empty
Eq-Q8 -j-Q8 -i-Q8 = empty
Eq-Q8 -j-Q8 j-Q8 = empty
Eq-Q8 -j-Q8 -j-Q8 = unit
Eq-Q8 -j-Q8 k-Q8 = empty
Eq-Q8 -j-Q8 -k-Q8 = empty
Eq-Q8 k-Q8 e-Q8 = empty
Eq-Q8 k-Q8 -e-Q8 = empty
Eq-Q8 k-Q8 i-Q8 = empty
Eq-Q8 k-Q8 -i-Q8 = empty
Eq-Q8 k-Q8 j-Q8 = empty
Eq-Q8 k-Q8 -j-Q8 = empty
Eq-Q8 k-Q8 k-Q8 = unit
Eq-Q8 k-Q8 -k-Q8 = empty
Eq-Q8 -k-Q8 e-Q8 = empty
Eq-Q8 -k-Q8 -e-Q8 = empty
Eq-Q8 -k-Q8 i-Q8 = empty
Eq-Q8 -k-Q8 -i-Q8 = empty
Eq-Q8 -k-Q8 j-Q8 = empty
Eq-Q8 -k-Q8 -j-Q8 = empty
Eq-Q8 -k-Q8 k-Q8 = empty
Eq-Q8 -k-Q8 -k-Q8 = unit

refl-Eq-Q8 : (x : Q8) → Eq-Q8 x x
refl-Eq-Q8 e-Q8 = star
refl-Eq-Q8 -e-Q8 = star
refl-Eq-Q8 i-Q8 = star
refl-Eq-Q8 -i-Q8 = star
refl-Eq-Q8 j-Q8 = star
refl-Eq-Q8 -j-Q8 = star
refl-Eq-Q8 k-Q8 = star
refl-Eq-Q8 -k-Q8 = star

Eq-eq-Q8 : {x y : Q8} → Id x y → Eq-Q8 x y
Eq-eq-Q8 {x} refl = refl-Eq-Q8 x

eq-Eq-Q8 : (x y : Q8) → Eq-Q8 x y → Id x y
eq-Eq-Q8 e-Q8 e-Q8 e = refl
eq-Eq-Q8 -e-Q8 -e-Q8 e = refl
eq-Eq-Q8 i-Q8 i-Q8 e = refl
eq-Eq-Q8 -i-Q8 -i-Q8 e = refl
eq-Eq-Q8 j-Q8 j-Q8 e = refl
eq-Eq-Q8 -j-Q8 -j-Q8 e = refl
eq-Eq-Q8 k-Q8 k-Q8 e = refl
eq-Eq-Q8 -k-Q8 -k-Q8 e = refl

is-decidable-Eq-Q8 : (x y : Q8) → is-decidable (Eq-Q8 x y)
is-decidable-Eq-Q8 e-Q8 e-Q8 = is-decidable-unit
is-decidable-Eq-Q8 e-Q8 -e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 e-Q8 i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 e-Q8 -i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 e-Q8 j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 e-Q8 -j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 e-Q8 k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 e-Q8 -k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -e-Q8 e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -e-Q8 -e-Q8 = is-decidable-unit
is-decidable-Eq-Q8 -e-Q8 i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -e-Q8 -i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -e-Q8 j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -e-Q8 -j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -e-Q8 k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -e-Q8 -k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 i-Q8 e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 i-Q8 -e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 i-Q8 i-Q8 = is-decidable-unit
is-decidable-Eq-Q8 i-Q8 -i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 i-Q8 j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 i-Q8 -j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 i-Q8 k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 i-Q8 -k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -i-Q8 e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -i-Q8 -e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -i-Q8 i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -i-Q8 -i-Q8 = is-decidable-unit
is-decidable-Eq-Q8 -i-Q8 j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -i-Q8 -j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -i-Q8 k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -i-Q8 -k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 j-Q8 e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 j-Q8 -e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 j-Q8 i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 j-Q8 -i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 j-Q8 j-Q8 = is-decidable-unit
is-decidable-Eq-Q8 j-Q8 -j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 j-Q8 k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 j-Q8 -k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -j-Q8 e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -j-Q8 -e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -j-Q8 i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -j-Q8 -i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -j-Q8 j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -j-Q8 -j-Q8 = is-decidable-unit
is-decidable-Eq-Q8 -j-Q8 k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -j-Q8 -k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 k-Q8 e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 k-Q8 -e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 k-Q8 i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 k-Q8 -i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 k-Q8 j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 k-Q8 -j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 k-Q8 k-Q8 = is-decidable-unit
is-decidable-Eq-Q8 k-Q8 -k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -k-Q8 e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -k-Q8 -e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -k-Q8 i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -k-Q8 -i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -k-Q8 j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -k-Q8 -j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -k-Q8 k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -k-Q8 -k-Q8 = is-decidable-unit

has-decidable-equality-Q8 : has-decidable-equality Q8
has-decidable-equality-Q8 x y =
  is-decidable-iff
    ( eq-Eq-Q8 x y)
    ( Eq-eq-Q8)
    ( is-decidable-Eq-Q8 x y)

is-set-Q8 : is-set Q8
is-set-Q8 = is-set-has-decidable-equality has-decidable-equality-Q8

Q8-Set : UU-Set lzero
Q8-Set = pair Q8 is-set-Q8

Q8-Semi-Group : Semi-Group lzero
Q8-Semi-Group = pair Q8-Set (pair mul-Q8 associative-mul-Q8)

Q8-Group : Group lzero
Q8-Group =
  pair
    Q8-Semi-Group
    ( pair
      ( pair e-Q8
        ( pair left-unit-law-mul-Q8 right-unit-law-mul-Q8))
      ( pair inv-Q8 (pair left-inverse-law-mul-Q8 right-inverse-law-mul-Q8)))

--------------------------------------------------------------------------------

cube : ℕ → UU (lsuc lzero)
cube d = Σ (UU-Fin d) (λ X → type-UU-Fin X → UU-Fin two-ℕ)

dim-cube-UU-Fin : {d : ℕ} (c : cube d) → UU-Fin d
dim-cube-UU-Fin c = pr1 c

dim-cube : {k : ℕ} → cube k → UU lzero
dim-cube c = type-UU-Fin (dim-cube-UU-Fin c)

has-finite-cardinality-dim-cube :
  {k : ℕ} (c : cube k) → has-finite-cardinality (dim-cube c)
has-finite-cardinality-dim-cube {k} c =
  pair k (pr2 (dim-cube-UU-Fin c))

is-finite-dim-cube :
  {k : ℕ} (c : cube k) → is-finite (dim-cube c)
is-finite-dim-cube c =
  is-finite-has-finite-cardinality (has-finite-cardinality-dim-cube c)

axis-cube-UU-2 :
  {d : ℕ} (c : cube d) → dim-cube c → UU-Fin two-ℕ
axis-cube-UU-2 c = pr2 c

axis-cube : {d : ℕ} (c : cube d) → dim-cube c → UU lzero
axis-cube c i = type-UU-Fin (axis-cube-UU-2 c i)

vertex-cube : {d : ℕ} (c : cube d) → UU lzero
vertex-cube c = (d : dim-cube c) → axis-cube c d

standard-cube : (k : ℕ) → cube k
standard-cube k =
  pair
    ( pair (Fin k) (unit-trunc-Prop equiv-id))
    ( λ x → pair (Fin two-ℕ) (unit-trunc-Prop equiv-id))

labelling-cube : {k : ℕ} (c : cube k) → UU (lsuc lzero)
labelling-cube {k} c = Id (standard-cube k) c

orientation-cube : {k : ℕ} → cube k → UU (lzero)
orientation-cube {k} c =
  Σ ( vertex-cube c → Fin two-ℕ)
    ( λ h →
      ( x y : vertex-cube c) →
        Id ( iterate
             ( number-of-elements-is-finite
               ( is-finite-Σ
                 ( is-finite-dim-cube c)
                 ( λ d →
                   is-finite-function-type
                     ( is-finite-eq
                       ( has-decidable-equality-is-finite
                         ( is-finite-has-finite-cardinality
                           ( pair two-ℕ (pr2 (axis-cube-UU-2 c d)))))
                     { x d}
                     { y d})
                     ( is-finite-empty))))
             ( succ-Fin)
             ( h x))
           ( h y))

face-cube :
  {k : ℕ} (c : cube (succ-ℕ k)) (d : dim-cube c) (a : axis-cube c d) → cube k
face-cube c d a =
  pair ( complement-point-UU-Fin' (pair (dim-cube-UU-Fin c) d))
       ( λ d' →
         axis-cube-UU-2 c
           ( inclusion-complement-point-UU-Fin'
             ( pair (dim-cube-UU-Fin c) d) d'))
