{-# OPTIONS --without-K --exact-split #-}

module extra.Eisenstein-integers where

open import extra.integers public

{-------------------------------------------------------------------------------

  The Eisenstein Integers

  The Eisenstein integers are the complex numbers of the form

    a + bω

  where ω = -½ + ½√3i, and where a and b are integers. Note that ω is a 
  solution to the equation ω² + ω + 1 = 0.

-------------------------------------------------------------------------------}

ℤ[ω] : UU lzero
ℤ[ω] = ℤ × ℤ

Eq-ℤ[ω] : ℤ[ω] → ℤ[ω] → UU lzero
Eq-ℤ[ω] x y = (Id (pr1 x) (pr1 y)) × (Id (pr2 x) (pr2 y))

refl-Eq-ℤ[ω] : (x : ℤ[ω]) → Eq-ℤ[ω] x x
refl-Eq-ℤ[ω] x = pair refl refl

Eq-eq-ℤ[ω] : {x y : ℤ[ω]} → Id x y → Eq-ℤ[ω] x y
Eq-eq-ℤ[ω] {x} refl = refl-Eq-ℤ[ω] x

eq-Eq-ℤ[ω]' : {x y : ℤ[ω]} → Eq-ℤ[ω] x y → Id x y
eq-Eq-ℤ[ω]' {pair a b} {pair .a .b} (pair refl refl) = refl

eq-Eq-ℤ[ω] : {x y : ℤ[ω]} → Id (pr1 x) (pr1 y) → Id (pr2 x) (pr2 y) → Id x y
eq-Eq-ℤ[ω] {pair a b} {pair .a .b} refl refl = refl

zero-ℤ[ω] : ℤ[ω]
zero-ℤ[ω] = pair zero-ℤ zero-ℤ

one-ℤ[ω] : ℤ[ω]
one-ℤ[ω] = pair one-ℤ zero-ℤ

eisenstein-int-ℤ : ℤ → ℤ[ω]
eisenstein-int-ℤ x = pair x zero-ℤ

ω-ℤ[ω] : ℤ[ω]
ω-ℤ[ω] = pair zero-ℤ one-ℤ

neg-ω-ℤ[ω] : ℤ[ω]
neg-ω-ℤ[ω] = pair zero-ℤ neg-one-ℤ

add-ℤ[ω] : ℤ[ω] → ℤ[ω] → ℤ[ω]
add-ℤ[ω] (pair a b) (pair a' b') = pair (add-ℤ a a') (add-ℤ b b')

ap-add-ℤ[ω] :
  {x x' y y' : ℤ[ω]} → Id x x' → Id y y' → Id (add-ℤ[ω] x y) (add-ℤ[ω] x' y')
ap-add-ℤ[ω] p q = ap-binary add-ℤ[ω] p q

neg-ℤ[ω] : ℤ[ω] → ℤ[ω]
neg-ℤ[ω] (pair a b) = pair (neg-ℤ a) (neg-ℤ b)

-- (a + bω)(c + dω) = (ac - bd) + (ad + cb - bd)ω

mul-ℤ[ω] : ℤ[ω] → ℤ[ω] → ℤ[ω]
mul-ℤ[ω] (pair a1 b1) (pair a2 b2) =
  pair
    ( add-ℤ (mul-ℤ a1 a2) (neg-ℤ (mul-ℤ b1 b2)))
    ( add-ℤ (add-ℤ (mul-ℤ a1 b2) (mul-ℤ a2 b1)) (neg-ℤ (mul-ℤ b1 b2)))

ap-mul-ℤ[ω] :
  {x x' y y' : ℤ[ω]} → Id x x' → Id y y' → Id (mul-ℤ[ω] x y) (mul-ℤ[ω] x' y')
ap-mul-ℤ[ω] p q = ap-binary mul-ℤ[ω] p q

-- The conjugate of (a + bω) is (a + bω²), which is ((a - b) - bω).

conjugate-ℤ[ω] : ℤ[ω] → ℤ[ω]
conjugate-ℤ[ω] (pair a b) = pair (add-ℤ a (neg-ℤ b)) (neg-ℤ b)

conjugate-conjugate-ℤ[ω] :
  (x : ℤ[ω]) → Id (conjugate-ℤ[ω] (conjugate-ℤ[ω] x)) x
conjugate-conjugate-ℤ[ω] (pair a b) =
  eq-Eq-ℤ[ω] (isretr-add-neg-ℤ' (neg-ℤ b) a) (neg-neg-ℤ b)

-- We show that the Eisenstein integers form a ring with conjugation

left-unit-law-add-ℤ[ω] : (x : ℤ[ω]) → Id (add-ℤ[ω] zero-ℤ[ω] x) x
left-unit-law-add-ℤ[ω] (pair a b) = eq-Eq-ℤ[ω] refl refl

right-unit-law-add-ℤ[ω] : (x : ℤ[ω]) → Id (add-ℤ[ω] x zero-ℤ[ω]) x
right-unit-law-add-ℤ[ω] (pair a b) =
  eq-Eq-ℤ[ω] (right-unit-law-add-ℤ a) (right-unit-law-add-ℤ b)

associative-add-ℤ[ω] :
  (x y z : ℤ[ω]) → Id (add-ℤ[ω] (add-ℤ[ω] x y) z) (add-ℤ[ω] x (add-ℤ[ω] y z))
associative-add-ℤ[ω] (pair a b) (pair c d) (pair e f) =
  eq-Eq-ℤ[ω] (associative-add-ℤ a c e) (associative-add-ℤ b d f)
  
left-inverse-law-add-ℤ[ω] :
  (x : ℤ[ω]) → Id (add-ℤ[ω] (neg-ℤ[ω] x) x) zero-ℤ[ω]
left-inverse-law-add-ℤ[ω] (pair a b) =
  eq-Eq-ℤ[ω] (left-inverse-law-add-ℤ a) (left-inverse-law-add-ℤ b)

right-inverse-law-add-ℤ[ω] :
  (x : ℤ[ω]) → Id (add-ℤ[ω] x (neg-ℤ[ω] x)) zero-ℤ[ω]
right-inverse-law-add-ℤ[ω] (pair a b) =
  eq-Eq-ℤ[ω] (right-inverse-law-add-ℤ a) (right-inverse-law-add-ℤ b)

commutative-add-ℤ[ω] :
  (x y : ℤ[ω]) → Id (add-ℤ[ω] x y) (add-ℤ[ω] y x)
commutative-add-ℤ[ω] (pair a b) (pair a' b') =
  eq-Eq-ℤ[ω] (commutative-add-ℤ a a') (commutative-add-ℤ b b')

left-unit-law-mul-ℤ[ω] :
  (x : ℤ[ω]) → Id (mul-ℤ[ω] one-ℤ[ω] x) x
left-unit-law-mul-ℤ[ω] (pair a b) =
  eq-Eq-ℤ[ω]
    ( right-unit-law-add-ℤ a)
    ( ( right-unit-law-add-ℤ (add-ℤ b (mul-ℤ a zero-ℤ))) ∙
      ( ( ap (add-ℤ b) (right-zero-law-mul-ℤ a)) ∙
        ( right-unit-law-add-ℤ b)))

right-unit-law-mul-ℤ[ω] :
  (x : ℤ[ω]) → Id (mul-ℤ[ω] x one-ℤ[ω]) x
right-unit-law-mul-ℤ[ω] (pair a b) =
  eq-Eq-ℤ[ω]
    ( ( ap-add-ℤ (right-unit-law-mul-ℤ a) (ap neg-ℤ (right-zero-law-mul-ℤ b))) ∙
      ( right-unit-law-add-ℤ a))
    ( ( ap-add-ℤ
        ( ap (add-ℤ' b) (right-zero-law-mul-ℤ a))
        ( ap neg-ℤ (right-zero-law-mul-ℤ b))) ∙
      ( right-unit-law-add-ℤ b))

commutative-mul-ℤ[ω] :
  (x y : ℤ[ω]) → Id (mul-ℤ[ω] x y) (mul-ℤ[ω] y x)
commutative-mul-ℤ[ω] (pair a b) (pair c d) =
  eq-Eq-ℤ[ω]
    ( ap-add-ℤ (commutative-mul-ℤ a c) (ap neg-ℤ (commutative-mul-ℤ b d)))
    ( ap-add-ℤ
      ( commutative-add-ℤ (mul-ℤ a d) (mul-ℤ c b))
      ( ap neg-ℤ (commutative-mul-ℤ b d)))

associative-mul-ℤ[ω] :
  (x y z : ℤ[ω]) → Id (mul-ℤ[ω] (mul-ℤ[ω] x y) z) (mul-ℤ[ω] x (mul-ℤ[ω] y z))
associative-mul-ℤ[ω] (pair a b) (pair c d) (pair e f) =
  eq-Eq-ℤ[ω]
    ( ( ap-add-ℤ
        ( ( right-distributive-mul-add-ℤ
            ( mul-ℤ a c)
            ( neg-ℤ (mul-ℤ b d))
            ( e)) ∙
          ( ap-add-ℤ
            ( associative-mul-ℤ a c e)
            ( ( left-negative-law-mul-ℤ (mul-ℤ b d) e) ∙
              ( ap neg-ℤ (associative-mul-ℤ b d e)))))
        ( ( ap
            ( neg-ℤ)
            ( ( right-distributive-mul-add-ℤ
                ( add-ℤ (mul-ℤ a d) (mul-ℤ c b))
                ( neg-ℤ (mul-ℤ b d))
                ( f)) ∙
              ( ap-add-ℤ
                ( ( right-distributive-mul-add-ℤ (mul-ℤ a d) (mul-ℤ c b) f) ∙
                  ( ap-add-ℤ
                    ( associative-mul-ℤ a d f)
                    ( ( ap (mul-ℤ' f) (commutative-mul-ℤ c b)) ∙
                      ( associative-mul-ℤ b c f))))
                ( ( left-negative-law-mul-ℤ (mul-ℤ b d) f) ∙
                  ( ap neg-ℤ (associative-mul-ℤ b d f)))))) ∙
          ( ( distributive-neg-add-ℤ
              ( add-ℤ (mul-ℤ a (mul-ℤ d f)) (mul-ℤ b (mul-ℤ c f)))
              ( neg-ℤ (mul-ℤ b (mul-ℤ d f)))) ∙
            ( ( ap-add-ℤ
                ( distributive-neg-add-ℤ
                  ( mul-ℤ a (mul-ℤ d f))
                  ( mul-ℤ b (mul-ℤ c f)))
                ( refl
                  { x = neg-ℤ (neg-ℤ (mul-ℤ b (mul-ℤ d f)))})) ∙
              ( associative-add-ℤ
                ( neg-ℤ (mul-ℤ a (mul-ℤ d f)))
                ( neg-ℤ (mul-ℤ b (mul-ℤ c f)))
                ( neg-ℤ (neg-ℤ (mul-ℤ b (mul-ℤ d f))))))))) ∙
      ( ( interchange-2-3-add-ℤ
          ( mul-ℤ a (mul-ℤ c e))
          ( neg-ℤ (mul-ℤ b (mul-ℤ d e)))
          ( neg-ℤ (mul-ℤ a (mul-ℤ d f)))
          ( add-ℤ
            ( neg-ℤ (mul-ℤ b (mul-ℤ c f)))
            ( neg-ℤ (neg-ℤ (mul-ℤ b (mul-ℤ d f)))))) ∙
        ( ap-add-ℤ
          ( ( ap
              ( add-ℤ (mul-ℤ a (mul-ℤ c e)))
              ( inv ( right-negative-law-mul-ℤ a (mul-ℤ d f)))) ∙
            ( inv
              ( left-distributive-mul-add-ℤ a (mul-ℤ c e) (neg-ℤ (mul-ℤ d f)))))
          ( ( ap
              ( add-ℤ (neg-ℤ (mul-ℤ b (mul-ℤ d e))))
              ( inv
                ( distributive-neg-add-ℤ
                  ( mul-ℤ b (mul-ℤ c f))
                  ( neg-ℤ (mul-ℤ b (mul-ℤ d f)))))) ∙
            ( ( inv
                ( distributive-neg-add-ℤ
                  ( mul-ℤ b (mul-ℤ d e))
                  ( add-ℤ
                    ( mul-ℤ b (mul-ℤ c f))
                    ( neg-ℤ (mul-ℤ b (mul-ℤ d f)))))) ∙
              ( ap
                ( neg-ℤ)
                ( ( ap
                    ( add-ℤ (mul-ℤ b (mul-ℤ d e)))
                    ( ( ap
                        ( add-ℤ (mul-ℤ b (mul-ℤ c f)))
                        ( inv (right-negative-law-mul-ℤ b (mul-ℤ d f)))) ∙
                      ( inv
                        ( left-distributive-mul-add-ℤ b
                          ( mul-ℤ c f)
                          ( neg-ℤ (mul-ℤ d f)))))) ∙
                  ( ( inv
                      ( left-distributive-mul-add-ℤ b
                        ( mul-ℤ d e)
                        ( add-ℤ (mul-ℤ c f) (neg-ℤ (mul-ℤ d f))))) ∙
                    ( ap
                      ( mul-ℤ b)
                      ( ( inv
                          ( associative-add-ℤ
                            ( mul-ℤ d e)
                            ( mul-ℤ c f)
                            ( neg-ℤ (mul-ℤ d f)))) ∙
                        ( ap
                          ( add-ℤ' (neg-ℤ (mul-ℤ d f)))
                          ( ( commutative-add-ℤ (mul-ℤ d e) (mul-ℤ c f)) ∙
                            ( ap
                              ( add-ℤ (mul-ℤ c f))
                              ( commutative-mul-ℤ d e))))))))))))))
    ( ( ap-add-ℤ
        ( ( ap-add-ℤ
            ( ( right-distributive-mul-add-ℤ ac (neg-ℤ bd) f) ∙
              ( ap-add-ℤ
                ( associative-mul-ℤ a c f)
                ( ( left-negative-law-mul-ℤ bd f) ∙
                  ( ( ap neg-ℤ (associative-mul-ℤ b d f)) ∙
                    ( ( inv (right-negative-law-mul-ℤ b df)) ∙
                      ( commutative-mul-ℤ b (neg-ℤ df)))))))
            ( ( left-distributive-mul-add-ℤ e (add-ℤ ad cb) (neg-ℤ bd)) ∙
              ( ( ap-add-ℤ
                  ( ( left-distributive-mul-add-ℤ e ad cb) ∙
                    ( ap-add-ℤ
                      ( ( commutative-mul-ℤ e ad) ∙
                        ( ( associative-mul-ℤ a d e) ∙
                          ( ap (mul-ℤ a) (commutative-mul-ℤ d e))))
                      ( ( ap (mul-ℤ e) (commutative-mul-ℤ c b)) ∙
                        ( ( commutative-mul-ℤ e (mul-ℤ b c)) ∙
                          ( ( associative-mul-ℤ b c e) ∙
                            ( commutative-mul-ℤ b ce))))))
                  ( ( right-negative-law-mul-ℤ e bd) ∙
                    ( ( ap
                        ( neg-ℤ)
                        ( ( commutative-mul-ℤ e bd) ∙
                          ( associative-mul-ℤ b d e))) ∙
                      ( ap
                        ( neg-ℤ)
                        (  ap (mul-ℤ b) (commutative-mul-ℤ d e)))))) ∙
                ( associative-add-ℤ
                  ( mul-ℤ a ed)
                  ( mul-ℤ ce b)
                  ( neg-ℤ (mul-ℤ b ed)))))) ∙
          ( ( interchange-2-3-add-ℤ
              ( mul-ℤ a cf)
              ( mul-ℤ (neg-ℤ df) b)
              ( mul-ℤ a ed)
              ( add-ℤ (mul-ℤ ce b) (neg-ℤ (mul-ℤ b ed)))) ∙
            ( ( ap-add-ℤ
                ( inv (left-distributive-mul-add-ℤ a cf ed))
                ( ( inv
                    ( associative-add-ℤ
                      ( mul-ℤ (neg-ℤ df) b)
                      ( mul-ℤ ce b)
                      ( neg-ℤ (mul-ℤ b ed)))) ∙
                  ( ap
                    ( add-ℤ' (neg-ℤ (mul-ℤ b ed)))
                    ( ( commutative-add-ℤ (mul-ℤ (neg-ℤ df) b) (mul-ℤ ce b)) ∙
                      ( inv
                        ( right-distributive-mul-add-ℤ ce (neg-ℤ df) b)))))) ∙
              ( ( inv
                  ( associative-add-ℤ
                    ( mul-ℤ a (add-ℤ cf ed))
                    ( mul-ℤ (add-ℤ ce (neg-ℤ df)) b)
                    ( neg-ℤ (mul-ℤ b ed)))) ∙
                ( ( ap
                    ( add-ℤ' (neg-ℤ (mul-ℤ b ed)))
                    ( commutative-add-ℤ
                      ( mul-ℤ a (add-ℤ cf ed))
                      ( mul-ℤ (add-ℤ ce (neg-ℤ df)) b))) ∙
                  ( associative-add-ℤ
                    ( mul-ℤ (add-ℤ ce (neg-ℤ df)) b)
                    ( mul-ℤ a (add-ℤ cf ed))
                    ( neg-ℤ (mul-ℤ b ed))))))))
        ( ( inv (left-negative-law-mul-ℤ (add-ℤ (add-ℤ ad cb) (neg-ℤ bd)) f)) ∙
          ( ( ap
              ( mul-ℤ' f)
              ( ( distributive-neg-add-ℤ (add-ℤ ad cb) (neg-ℤ bd)) ∙
                ( ap-add-ℤ (distributive-neg-add-ℤ ad cb) (neg-neg-ℤ bd)))) ∙
            ( ( right-distributive-mul-add-ℤ
                ( add-ℤ (neg-ℤ ad) (neg-ℤ cb))
                ( bd)
                ( f)) ∙
              ( ( ap-add-ℤ
                  ( ( right-distributive-mul-add-ℤ (neg-ℤ ad) (neg-ℤ cb) f) ∙
                    ( ap-add-ℤ
                      ( ( left-negative-law-mul-ℤ ad f) ∙
                        ( ( ap
                            ( neg-ℤ)
                            ( associative-mul-ℤ a d f)) ∙
                          ( inv (right-negative-law-mul-ℤ a df))))
                      ( ( left-negative-law-mul-ℤ cb f) ∙
                        ( ap
                          ( neg-ℤ)
                          ( ( ap
                              ( mul-ℤ' f)
                              ( commutative-mul-ℤ c b)) ∙
                            ( associative-mul-ℤ b c f))))))
                  ( ( associative-mul-ℤ b d f) ∙
                    ( ( inv (neg-neg-ℤ (mul-ℤ b df))) ∙
                      ( ap neg-ℤ (inv (right-negative-law-mul-ℤ b df)))))) ∙
                ( ( associative-add-ℤ
                    ( mul-ℤ a ( neg-ℤ df))
                    ( neg-ℤ (mul-ℤ b cf))
                    ( neg-ℤ (mul-ℤ b (neg-ℤ df)))) ∙
                  ( ap
                    ( add-ℤ (mul-ℤ a (neg-ℤ df)))
                    ( ( inv
                        ( distributive-neg-add-ℤ
                          ( mul-ℤ b cf)
                          ( mul-ℤ b (neg-ℤ df)))) ∙
                      ( ap
                        ( neg-ℤ)
                        ( inv
                          ( left-distributive-mul-add-ℤ
                            ( b)
                            ( cf)
                            ( neg-ℤ df)))))))))))) ∙
      ( ( associative-add-ℤ
          ( mul-ℤ (add-ℤ ce (neg-ℤ df)) b)
          ( add-ℤ (mul-ℤ a (add-ℤ cf ed)) (neg-ℤ (mul-ℤ b ed)))
          ( add-ℤ
            ( mul-ℤ a (neg-ℤ df))
            ( neg-ℤ (mul-ℤ b (add-ℤ cf (neg-ℤ df)))))) ∙
        ( ( ( ap
              ( add-ℤ (mul-ℤ (add-ℤ ce (neg-ℤ df)) b))
              ( ( interchange-2-3-add-ℤ
                  ( mul-ℤ a (add-ℤ cf ed))
                  ( neg-ℤ (mul-ℤ b ed))
                  ( mul-ℤ a (neg-ℤ df))
                  ( neg-ℤ (mul-ℤ b (add-ℤ cf (neg-ℤ df))))) ∙
                ( ap-add-ℤ
                  ( inv
                    ( left-distributive-mul-add-ℤ a (add-ℤ cf ed) (neg-ℤ df)))
                  ( ( inv
                      ( distributive-neg-add-ℤ
                        ( mul-ℤ b ed)
                        ( mul-ℤ b (add-ℤ cf (neg-ℤ df))))) ∙
                    ( ap
                      ( neg-ℤ)
                      ( ( inv
                          ( left-distributive-mul-add-ℤ b ed
                            ( add-ℤ cf (neg-ℤ df)))) ∙
                        ( ap
                          ( mul-ℤ b)
                          ( ( inv
                              ( associative-add-ℤ ed cf (neg-ℤ df))) ∙
                            ( ap
                              ( add-ℤ' (neg-ℤ df))
                              ( commutative-add-ℤ ed cf)))))))))) ∙
            ( inv
              ( associative-add-ℤ
                ( mul-ℤ (add-ℤ ce (neg-ℤ df)) b)
                ( mul-ℤ a (add-ℤ (add-ℤ cf ed) (neg-ℤ df)))
                ( neg-ℤ (mul-ℤ b (add-ℤ (add-ℤ cf ed) (neg-ℤ df))))))) ∙
          ( ap
            ( add-ℤ' (neg-ℤ (mul-ℤ b (add-ℤ (add-ℤ cf ed) (neg-ℤ df)))))
            ( commutative-add-ℤ
              ( mul-ℤ (add-ℤ ce (neg-ℤ df)) b)
              ( mul-ℤ a (add-ℤ (add-ℤ cf ed) (neg-ℤ df))))))))
    where
    ac = mul-ℤ a c
    bd = mul-ℤ b d
    ad = mul-ℤ a d
    cb = mul-ℤ c b
    ce = mul-ℤ c e
    cf = mul-ℤ c f
    ed = mul-ℤ e d
    df = mul-ℤ d f

left-distributive-mul-add-ℤ[ω] :
  (x y z : ℤ[ω]) →
  Id (mul-ℤ[ω] x (add-ℤ[ω] y z)) (add-ℤ[ω] (mul-ℤ[ω] x y) (mul-ℤ[ω] x z))
left-distributive-mul-add-ℤ[ω] (pair a b) (pair c d) (pair e f) =
  eq-Eq-ℤ[ω]
    ( ( ap-add-ℤ
        ( left-distributive-mul-add-ℤ a c e)
        ( ( ap
            ( neg-ℤ)
            ( left-distributive-mul-add-ℤ b d f)) ∙
          ( distributive-neg-add-ℤ (mul-ℤ b d) (mul-ℤ b f)))) ∙
      ( interchange-2-3-add-ℤ
        ( mul-ℤ a c)
        ( mul-ℤ a e)
        ( neg-ℤ (mul-ℤ b d))
        ( neg-ℤ (mul-ℤ b f))))
    ( ( ap-add-ℤ
        ( ( ap-add-ℤ
            ( left-distributive-mul-add-ℤ a d f)
            ( right-distributive-mul-add-ℤ c e b)) ∙
          ( interchange-2-3-add-ℤ
            ( mul-ℤ a d)
            ( mul-ℤ a f)
            ( mul-ℤ c b)
            ( mul-ℤ e b)))
        ( ( ap neg-ℤ (left-distributive-mul-add-ℤ b d f)) ∙
          ( distributive-neg-add-ℤ (mul-ℤ b d) (mul-ℤ b f)))) ∙
      ( interchange-2-3-add-ℤ
        ( add-ℤ (mul-ℤ a d) (mul-ℤ c b))
        ( add-ℤ (mul-ℤ a f) (mul-ℤ e b))
        ( neg-ℤ (mul-ℤ b d))
        ( neg-ℤ (mul-ℤ b f))))

right-distributive-mul-add-ℤ[ω] :
  (x y z : ℤ[ω]) →
  Id (mul-ℤ[ω] (add-ℤ[ω] x y) z) (add-ℤ[ω] (mul-ℤ[ω] x z) (mul-ℤ[ω] y z))
right-distributive-mul-add-ℤ[ω] x y z =
  ( commutative-mul-ℤ[ω] (add-ℤ[ω] x y) z) ∙
  ( ( left-distributive-mul-add-ℤ[ω] z x y) ∙
    ( ap-add-ℤ[ω] (commutative-mul-ℤ[ω] z x) (commutative-mul-ℤ[ω] z y)))

-- We complete the construction of the ring of Gaussian integers

ℤ[ω]-Semi-Group : Semi-Group lzero
ℤ[ω]-Semi-Group =
  pair
    ( prod-Set ℤ-Set ℤ-Set)
    ( pair add-ℤ[ω] associative-add-ℤ[ω])

ℤ[ω]-Group : Group lzero
ℤ[ω]-Group =
  pair
    ( ℤ[ω]-Semi-Group)
    ( pair
      ( pair zero-ℤ[ω] (pair left-unit-law-add-ℤ[ω] right-unit-law-add-ℤ[ω]))
      ( pair neg-ℤ[ω]
        ( pair left-inverse-law-add-ℤ[ω] right-inverse-law-add-ℤ[ω])))

ℤ[ω]-Ab : Ab lzero
ℤ[ω]-Ab =
  pair
    ( ℤ[ω]-Group)
    ( commutative-add-ℤ[ω])


ℤ[ω]-Ring : Ring lzero
ℤ[ω]-Ring =
  pair
    ( ℤ[ω]-Ab)
    ( pair
      ( pair mul-ℤ[ω] associative-mul-ℤ[ω])
      ( pair
        ( pair one-ℤ[ω] (pair left-unit-law-mul-ℤ[ω] right-unit-law-mul-ℤ[ω]))
        ( pair left-distributive-mul-add-ℤ[ω] right-distributive-mul-add-ℤ[ω])))
