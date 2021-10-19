{-# OPTIONS --without-K --exact-split #-}

module extra.Gaussian-integers where

open import book public

ℤ[i] : UU lzero
ℤ[i] = ℤ × ℤ

Eq-ℤ[i] : ℤ[i] → ℤ[i] → UU lzero
Eq-ℤ[i] x y = (Id (pr1 x) (pr1 y)) × (Id (pr2 x) (pr2 y))

refl-Eq-ℤ[i] : (x : ℤ[i]) → Eq-ℤ[i] x x
refl-Eq-ℤ[i] x = pair refl refl

Eq-eq-ℤ[i] : {x y : ℤ[i]} → Id x y → Eq-ℤ[i] x y
Eq-eq-ℤ[i] {x} refl = refl-Eq-ℤ[i] x

eq-Eq-ℤ[i]' : {x y : ℤ[i]} → Eq-ℤ[i] x y → Id x y
eq-Eq-ℤ[i]' {pair a b} {pair .a .b} (pair refl refl) = refl

eq-Eq-ℤ[i] : {x y : ℤ[i]} → Id (pr1 x) (pr1 y) → Id (pr2 x) (pr2 y) → Id x y
eq-Eq-ℤ[i] {pair a b} {pair .a .b} refl refl = refl

zero-ℤ[i] : ℤ[i]
zero-ℤ[i] = pair zero-ℤ zero-ℤ

add-ℤ[i] : ℤ[i] → ℤ[i] → ℤ[i]
add-ℤ[i] (pair a b) (pair a' b') = pair (add-ℤ a a') (add-ℤ b b')

neg-ℤ[i] : ℤ[i] → ℤ[i]
neg-ℤ[i] (pair a b) = pair (neg-ℤ a) (neg-ℤ b)

mul-ℤ[i] : ℤ[i] → ℤ[i] → ℤ[i]
mul-ℤ[i] (pair a b) (pair a' b') =
  pair
    ( add-ℤ (mul-ℤ a a') (mul-ℤ neg-one-ℤ (mul-ℤ b b')))
    ( add-ℤ (mul-ℤ a b') (mul-ℤ a' b))

left-unit-law-add-ℤ[i] : (x : ℤ[i]) → Id (add-ℤ[i] zero-ℤ[i] x) x
left-unit-law-add-ℤ[i] (pair a b) = eq-Eq-ℤ[i] refl refl

right-unit-law-add-ℤ[i] : (x : ℤ[i]) → Id (add-ℤ[i] x zero-ℤ[i]) x
right-unit-law-add-ℤ[i] (pair a b) =
  eq-Eq-ℤ[i] (right-unit-law-add-ℤ a) (right-unit-law-add-ℤ b)

associative-add-ℤ[i] :
  (x y z : ℤ[i]) → Id (add-ℤ[i] (add-ℤ[i] x y) z) (add-ℤ[i] x (add-ℤ[i] y z))
associative-add-ℤ[i] (pair a1 b1) (pair a2 b2) (pair a3 b3) =
  eq-Eq-ℤ[i] (associative-add-ℤ a1 a2 a3) (associative-add-ℤ b1 b2 b3)
  
left-inverse-law-add-ℤ[i] :
  (x : ℤ[i]) → Id (add-ℤ[i] (neg-ℤ[i] x) x) zero-ℤ[i]
left-inverse-law-add-ℤ[i] (pair a b) =
  eq-Eq-ℤ[i] (left-inverse-law-add-ℤ a) (left-inverse-law-add-ℤ b)

right-inverse-law-add-ℤ[i] :
  (x : ℤ[i]) → Id (add-ℤ[i] x (neg-ℤ[i] x)) zero-ℤ[i]
right-inverse-law-add-ℤ[i] (pair a b) =
  eq-Eq-ℤ[i] (right-inverse-law-add-ℤ a) (right-inverse-law-add-ℤ b)

commutative-add-ℤ[i] :
  (x y : ℤ[i]) → Id (add-ℤ[i] x y) (add-ℤ[i] y x)
commutative-add-ℤ[i] (pair a b) (pair a' b') =
  eq-Eq-ℤ[i] (commutative-add-ℤ a a') (commutative-add-ℤ b b')

interchange-2-3-add-ℤ :
  (a b c d : ℤ) →
  Id (add-ℤ (add-ℤ a b) (add-ℤ c d)) (add-ℤ (add-ℤ a c) (add-ℤ b d))
interchange-2-3-add-ℤ a b c d =
  ( associative-add-ℤ a b (add-ℤ c d)) ∙
  ( ( ap
      ( add-ℤ a)
      ( ( inv (associative-add-ℤ b c d)) ∙
        ( ( ap (add-ℤ' d) (commutative-add-ℤ b c)) ∙
          ( associative-add-ℤ c b d)))) ∙
    ( inv (associative-add-ℤ a c (add-ℤ b d))))

associative-mul-ℤ[i] :
  (x y z : ℤ[i]) → Id (mul-ℤ[i] (mul-ℤ[i] x y) z) (mul-ℤ[i] x (mul-ℤ[i] y z))
associative-mul-ℤ[i] (pair a1 b1) (pair a2 b2) (pair a3 b3) =
  eq-Eq-ℤ[i]
    ( ( ap-add-ℤ
        ( ( right-distributive-mul-add-ℤ
            ( mul-ℤ a1 a2)
            ( mul-ℤ neg-one-ℤ (mul-ℤ b1 b2))
            ( a3)) ∙
          ( ap-add-ℤ
            ( associative-mul-ℤ a1 a2 a3)
            ( ( associative-mul-ℤ neg-one-ℤ (mul-ℤ b1 b2) a3) ∙
              ( ap
                ( mul-ℤ neg-one-ℤ)
                ( ( associative-mul-ℤ b1 b2 a3) ∙
                  ( ap (mul-ℤ b1) (commutative-mul-ℤ b2 a3)))))))
        ( ( ap
            ( neg-ℤ)
            ( ( right-distributive-mul-add-ℤ (mul-ℤ a1 b2) (mul-ℤ a2 b1) b3) ∙
              ( ap-add-ℤ
                ( associative-mul-ℤ a1 b2 b3)
                ( associative-mul-ℤ a2 b1 b3)))) ∙
          ( ( left-distributive-mul-add-ℤ
              ( neg-one-ℤ)
              ( mul-ℤ a1 (mul-ℤ b2 b3))
              ( mul-ℤ a2 (mul-ℤ b1 b3)))))) ∙
      ( ( interchange-2-3-add-ℤ
          ( mul-ℤ a1 (mul-ℤ a2 a3))
          ( neg-ℤ (mul-ℤ b1 (mul-ℤ a3 b2)))
          ( neg-ℤ (mul-ℤ a1 (mul-ℤ b2 b3)))
          ( neg-ℤ (mul-ℤ a2 (mul-ℤ b1 b3)))) ∙
        ( ap-add-ℤ
          ( ( ap-add-ℤ
              ( refl {x = mul-ℤ a1 (mul-ℤ a2 a3)})
              ( inv
                ( right-negative-law-mul-ℤ a1 (mul-ℤ b2 b3)))) ∙
            ( inv
              ( left-distributive-mul-add-ℤ a1
                ( mul-ℤ a2 a3)
                ( neg-ℤ (mul-ℤ b2 b3)))))
          ( ( inv
              ( left-distributive-mul-add-ℤ
                ( neg-one-ℤ)
                ( mul-ℤ b1 (mul-ℤ a3 b2))
                ( mul-ℤ a2 (mul-ℤ b1 b3)))) ∙
            ( ap neg-ℤ
              ( ( ap-add-ℤ
                  ( refl {x = mul-ℤ b1 (mul-ℤ a3 b2)})
                  ( ( ap (mul-ℤ a2) (commutative-mul-ℤ b1 b3)) ∙
                    ( ( inv (associative-mul-ℤ a2 b3 b1)) ∙
                      ( commutative-mul-ℤ (mul-ℤ a2 b3) b1)))) ∙
                ( ( inv
                    ( left-distributive-mul-add-ℤ b1
                      ( mul-ℤ a3 b2)
                      ( mul-ℤ a2 b3))) ∙
                  ( ap
                    ( mul-ℤ b1)
                    ( commutative-add-ℤ (mul-ℤ a3 b2) (mul-ℤ a2 b3))))))))))
    ( ( ap-add-ℤ
        ( ( right-distributive-mul-add-ℤ
            ( mul-ℤ a1 a2)
            ( neg-ℤ (mul-ℤ b1 b2))
            ( b3)) ∙
          ( ap
            ( add-ℤ (mul-ℤ (mul-ℤ a1 a2) b3))
            ( left-negative-law-mul-ℤ (mul-ℤ b1 b2) b3)))
        ( ( left-distributive-mul-add-ℤ a3 (mul-ℤ a1 b2) (mul-ℤ a2 b1)) ∙
          ( ap-add-ℤ
            ( ( commutative-mul-ℤ a3 (mul-ℤ a1 b2)) ∙
              ( ( associative-mul-ℤ a1 b2 a3) ∙
                ( ap (mul-ℤ a1) (commutative-mul-ℤ b2 a3))))
            ( ( inv (associative-mul-ℤ a3 a2 b1)) ∙
              ( ap (mul-ℤ' b1) (commutative-mul-ℤ a3 a2)))))) ∙
      ( ( interchange-2-3-add-ℤ
          ( mul-ℤ (mul-ℤ a1 a2) b3)
          ( neg-ℤ (mul-ℤ (mul-ℤ b1 b2) b3))
          ( mul-ℤ a1 (mul-ℤ a3 b2))
          ( mul-ℤ (mul-ℤ a2 a3) b1)) ∙
        ( ap-add-ℤ
          ( ( ap-add-ℤ
              ( associative-mul-ℤ a1 a2 b3)
              ( refl)) ∙
            ( inv (left-distributive-mul-add-ℤ a1 (mul-ℤ a2 b3) (mul-ℤ a3 b2))))
          ( ( ap-add-ℤ
              ( ( ap
                  ( neg-ℤ)
                  ( ( associative-mul-ℤ b1 b2 b3) ∙
                    ( commutative-mul-ℤ b1 (mul-ℤ b2 b3)))) ∙
                ( inv (left-negative-law-mul-ℤ (mul-ℤ b2 b3) b1)))
              ( refl)) ∙
            ( ( inv
                ( ( right-distributive-mul-add-ℤ
                    ( neg-ℤ (mul-ℤ b2 b3))
                    ( mul-ℤ a2 a3) b1))) ∙
              ( ap
                ( mul-ℤ' b1)
                ( commutative-add-ℤ (neg-ℤ (mul-ℤ b2 b3)) (mul-ℤ a2 a3))))))))
