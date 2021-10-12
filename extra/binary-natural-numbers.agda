{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.binary-natural-numbers where

open import book public

--------------------------------------------------------------------------------

{- The binary natural numbers -}

data ℕ₂ : UU lzero where
  zero-ℕ₂ : ℕ₂
  one-ℕ₂ : ℕ₂
  double-plus-two-ℕ₂ : ℕ₂ → ℕ₂
  double-plus-three-ℕ₂ : ℕ₂ → ℕ₂

-- The successor function on ℕ₂
succ-ℕ₂ : ℕ₂ → ℕ₂
succ-ℕ₂ zero-ℕ₂ = one-ℕ₂
succ-ℕ₂ one-ℕ₂ = double-plus-two-ℕ₂ zero-ℕ₂
succ-ℕ₂ (double-plus-two-ℕ₂ n) = double-plus-three-ℕ₂ n
succ-ℕ₂ (double-plus-three-ℕ₂ n) = double-plus-two-ℕ₂ (succ-ℕ₂ n)

two-ℕ₂ : ℕ₂
two-ℕ₂ = succ-ℕ₂ one-ℕ₂

three-ℕ₂ : ℕ₂
three-ℕ₂ = succ-ℕ₂ two-ℕ₂

four-ℕ₂ : ℕ₂
four-ℕ₂ = succ-ℕ₂ three-ℕ₂

five-ℕ₂ : ℕ₂
five-ℕ₂ = succ-ℕ₂ four-ℕ₂

six-ℕ₂ : ℕ₂
six-ℕ₂ = succ-ℕ₂ five-ℕ₂

seven-ℕ₂ : ℕ₂
seven-ℕ₂ = succ-ℕ₂ six-ℕ₂

eight-ℕ₂ : ℕ₂
eight-ℕ₂ = succ-ℕ₂ seven-ℕ₂

nine-ℕ₂ : ℕ₂
nine-ℕ₂ = succ-ℕ₂ eight-ℕ₂

ten-ℕ₂ : ℕ₂
ten-ℕ₂ = succ-ℕ₂ nine-ℕ₂

eleven-ℕ₂ : ℕ₂
eleven-ℕ₂ = succ-ℕ₂ ten-ℕ₂

twelve-ℕ₂ : ℕ₂
twelve-ℕ₂ = succ-ℕ₂ eleven-ℕ₂

thirteen-ℕ₂ : ℕ₂
thirteen-ℕ₂ = succ-ℕ₂ twelve-ℕ₂

fourteen-ℕ₂ : ℕ₂
fourteen-ℕ₂ = succ-ℕ₂ thirteen-ℕ₂

fifteen-ℕ₂ : ℕ₂
fifteen-ℕ₂ = succ-ℕ₂ fourteen-ℕ₂

sixteen-ℕ₂ : ℕ₂
sixteen-ℕ₂ = succ-ℕ₂ fifteen-ℕ₂

seventeen-ℕ₂ : ℕ₂
seventeen-ℕ₂ = succ-ℕ₂ sixteen-ℕ₂

eighteen-ℕ₂ : ℕ₂
eighteen-ℕ₂ = succ-ℕ₂ seventeen-ℕ₂

nineteen-ℕ₂ : ℕ₂
nineteen-ℕ₂ = succ-ℕ₂ eighteen-ℕ₂

twenty-ℕ₂ : ℕ₂
twenty-ℕ₂ = succ-ℕ₂ nineteen-ℕ₂

-- The function that turns a natural number into a binary natural number
binary-ℕ : ℕ → ℕ₂
binary-ℕ zero-ℕ = zero-ℕ₂
binary-ℕ (succ-ℕ n) = succ-ℕ₂ (binary-ℕ n)

-- The function that turns a binary natural number into a natural number
double-plus-two-ℕ : ℕ → ℕ
double-plus-two-ℕ n = succ-ℕ (succ-ℕ (mul-ℕ two-ℕ n))

double-plus-three-ℕ : ℕ → ℕ
double-plus-three-ℕ = succ-ℕ ∘ double-plus-two-ℕ

unary-ℕ₂ : ℕ₂ → ℕ
unary-ℕ₂ zero-ℕ₂ = zero-ℕ
unary-ℕ₂ one-ℕ₂ = one-ℕ
unary-ℕ₂ (double-plus-two-ℕ₂ n) = double-plus-two-ℕ (unary-ℕ₂ n)
unary-ℕ₂ (double-plus-three-ℕ₂ n) = double-plus-three-ℕ (unary-ℕ₂ n)

-- We show that unary-ℕ ∘ binary-ℕ is homotopic to the identity function
mul-two-succ-ℕ :
  (x : ℕ) → Id (mul-ℕ two-ℕ (succ-ℕ x)) (succ-ℕ (succ-ℕ (mul-ℕ two-ℕ x)))
mul-two-succ-ℕ x =
  ( right-successor-law-mul-ℕ two-ℕ x) ∙
  ( commutative-add-ℕ two-ℕ (mul-ℕ two-ℕ x))

unary-succ-ℕ₂ : (n : ℕ₂) → Id (unary-ℕ₂ (succ-ℕ₂ n)) (succ-ℕ (unary-ℕ₂ n))
unary-succ-ℕ₂ zero-ℕ₂ = refl
unary-succ-ℕ₂ one-ℕ₂ = refl
unary-succ-ℕ₂ (double-plus-two-ℕ₂ n) = refl
unary-succ-ℕ₂ (double-plus-three-ℕ₂ n) =
  ap ( succ-ℕ ∘ succ-ℕ)
     ( ( ap (mul-ℕ two-ℕ) (unary-succ-ℕ₂ n)) ∙
       ( mul-two-succ-ℕ (unary-ℕ₂ n)))

unary-binary-ℕ₂ : (n : ℕ) → Id (unary-ℕ₂ (binary-ℕ n)) n
unary-binary-ℕ₂ zero-ℕ = refl
unary-binary-ℕ₂ (succ-ℕ n) =
  ( unary-succ-ℕ₂ (binary-ℕ n)) ∙
  ( ap succ-ℕ (unary-binary-ℕ₂ n))

-- We show that binary-ℕ ∘ unary-ℕ₂ is homotopic to the identity function
double-plus-two-succ-ℕ :
  (n : ℕ) →
  Id (double-plus-two-ℕ (succ-ℕ n)) (succ-ℕ (succ-ℕ (double-plus-two-ℕ n)))
double-plus-two-succ-ℕ n =
  ap ( succ-ℕ ∘ succ-ℕ)
     ( ( right-successor-law-mul-ℕ two-ℕ n) ∙
       ( commutative-add-ℕ two-ℕ (mul-ℕ two-ℕ n)))
  
binary-double-plus-two-ℕ :
  (n : ℕ) →
  Id (binary-ℕ (double-plus-two-ℕ n)) (double-plus-two-ℕ₂ (binary-ℕ n))
binary-double-plus-two-ℕ zero-ℕ = refl
binary-double-plus-two-ℕ (succ-ℕ n) =
  ( ap binary-ℕ (double-plus-two-succ-ℕ n)) ∙
  ( ap (succ-ℕ₂ ∘ succ-ℕ₂) (binary-double-plus-two-ℕ n))

double-plus-three-succ-ℕ :
  (n : ℕ) →
  Id (double-plus-three-ℕ (succ-ℕ n)) (succ-ℕ (succ-ℕ (double-plus-three-ℕ n)))
double-plus-three-succ-ℕ n =
  ap succ-ℕ (double-plus-two-succ-ℕ n)

binary-double-plus-three-ℕ :
  (n : ℕ) →
  Id (binary-ℕ (double-plus-three-ℕ n)) (double-plus-three-ℕ₂ (binary-ℕ n))
binary-double-plus-three-ℕ zero-ℕ = refl
binary-double-plus-three-ℕ (succ-ℕ n) =
  ( ap binary-ℕ (double-plus-three-succ-ℕ n)) ∙
  ( ap (succ-ℕ₂ ∘ succ-ℕ₂) (binary-double-plus-three-ℕ n))

binary-unary-ℕ₂ : (n : ℕ₂) → Id (binary-ℕ (unary-ℕ₂ n)) n
binary-unary-ℕ₂ zero-ℕ₂ = refl
binary-unary-ℕ₂ one-ℕ₂ = refl
binary-unary-ℕ₂ (double-plus-two-ℕ₂ n) =
  ( binary-double-plus-two-ℕ (unary-ℕ₂ n)) ∙
  ( ap double-plus-two-ℕ₂ (binary-unary-ℕ₂ n))
binary-unary-ℕ₂ (double-plus-three-ℕ₂ n) =
  ( binary-double-plus-three-ℕ (unary-ℕ₂ n)) ∙
  ( ap double-plus-three-ℕ₂ (binary-unary-ℕ₂ n))

-- Addition on the binary natural numbers
add-ℕ₂ : ℕ₂ → ℕ₂ → ℕ₂
add-ℕ₂ m zero-ℕ₂ = m
add-ℕ₂ m one-ℕ₂ = succ-ℕ₂ m
add-ℕ₂ zero-ℕ₂ (double-plus-two-ℕ₂ n) =
  double-plus-two-ℕ₂ n
add-ℕ₂ one-ℕ₂ (double-plus-two-ℕ₂ n) =
  double-plus-three-ℕ₂ n
add-ℕ₂ (double-plus-two-ℕ₂ m) (double-plus-two-ℕ₂ n) =
  double-plus-two-ℕ₂ (succ-ℕ₂ (add-ℕ₂ m n))
add-ℕ₂ (double-plus-three-ℕ₂ m) (double-plus-two-ℕ₂ n) =
  double-plus-three-ℕ₂ (succ-ℕ₂ (add-ℕ₂ m n))
add-ℕ₂ zero-ℕ₂ (double-plus-three-ℕ₂ n) =
  double-plus-three-ℕ₂ n
add-ℕ₂ one-ℕ₂ (double-plus-three-ℕ₂ n) =
  succ-ℕ₂ (double-plus-three-ℕ₂ n)
add-ℕ₂ (double-plus-two-ℕ₂ m) (double-plus-three-ℕ₂ n) =
  double-plus-three-ℕ₂ (succ-ℕ₂ (add-ℕ₂ m n))
add-ℕ₂ (double-plus-three-ℕ₂ m) (double-plus-three-ℕ₂ n) =
  double-plus-two-ℕ₂ (succ-ℕ₂ (succ-ℕ₂ (add-ℕ₂ m n)))

right-unit-law-add-ℕ₂ : (n : ℕ₂) → Id (add-ℕ₂ n zero-ℕ₂) n
right-unit-law-add-ℕ₂ n = refl

left-unit-law-add-ℕ₂ : (n : ℕ₂) → Id (add-ℕ₂ zero-ℕ₂ n) n
left-unit-law-add-ℕ₂ zero-ℕ₂ = refl
left-unit-law-add-ℕ₂ one-ℕ₂ = refl
left-unit-law-add-ℕ₂ (double-plus-two-ℕ₂ n) = refl
left-unit-law-add-ℕ₂ (double-plus-three-ℕ₂ n) = refl

-- We define observational equality on ℕ₂

Eq-ℕ₂ : ℕ₂ → ℕ₂ → UU lzero
Eq-ℕ₂ zero-ℕ₂ zero-ℕ₂ = unit
Eq-ℕ₂ zero-ℕ₂ one-ℕ₂ = empty
Eq-ℕ₂ zero-ℕ₂ (double-plus-two-ℕ₂ y) = empty
Eq-ℕ₂ zero-ℕ₂ (double-plus-three-ℕ₂ y) = empty
Eq-ℕ₂ one-ℕ₂ zero-ℕ₂ = empty
Eq-ℕ₂ one-ℕ₂ one-ℕ₂ = unit
Eq-ℕ₂ one-ℕ₂ (double-plus-two-ℕ₂ y) = empty
Eq-ℕ₂ one-ℕ₂ (double-plus-three-ℕ₂ y) = empty
Eq-ℕ₂ (double-plus-two-ℕ₂ x) zero-ℕ₂ = empty
Eq-ℕ₂ (double-plus-two-ℕ₂ x) one-ℕ₂ = empty
Eq-ℕ₂ (double-plus-two-ℕ₂ x) (double-plus-two-ℕ₂ y) = Eq-ℕ₂ x y
Eq-ℕ₂ (double-plus-two-ℕ₂ x) (double-plus-three-ℕ₂ y) = empty
Eq-ℕ₂ (double-plus-three-ℕ₂ x) zero-ℕ₂ = empty
Eq-ℕ₂ (double-plus-three-ℕ₂ x) one-ℕ₂ = empty
Eq-ℕ₂ (double-plus-three-ℕ₂ x) (double-plus-two-ℕ₂ y) = empty
Eq-ℕ₂ (double-plus-three-ℕ₂ x) (double-plus-three-ℕ₂ y) = Eq-ℕ₂ x y

refl-Eq-ℕ₂ : (x : ℕ₂) → Eq-ℕ₂ x x
refl-Eq-ℕ₂ zero-ℕ₂ = star
refl-Eq-ℕ₂ one-ℕ₂ = star
refl-Eq-ℕ₂ (double-plus-two-ℕ₂ x) = refl-Eq-ℕ₂ x
refl-Eq-ℕ₂ (double-plus-three-ℕ₂ x) = refl-Eq-ℕ₂ x

Eq-eq-ℕ₂ : {x y : ℕ₂} → Id x y → Eq-ℕ₂ x y
Eq-eq-ℕ₂ {x} {.x} refl = refl-Eq-ℕ₂ x

eq-Eq-ℕ₂ : {x y : ℕ₂} → Eq-ℕ₂ x y → Id x y
eq-Eq-ℕ₂ {zero-ℕ₂} {zero-ℕ₂} e = refl
eq-Eq-ℕ₂ {one-ℕ₂} {one-ℕ₂} e = refl
eq-Eq-ℕ₂ {double-plus-two-ℕ₂ x} {double-plus-two-ℕ₂ y} e =
  ap double-plus-two-ℕ₂ (eq-Eq-ℕ₂ e)
eq-Eq-ℕ₂ {double-plus-three-ℕ₂ x} {double-plus-three-ℕ₂ y} e =
  ap double-plus-three-ℕ₂ (eq-Eq-ℕ₂ e)

-- We define the strict ordering on ℕ₂

_<-ℕ₂_ : ℕ₂ → ℕ₂ → UU lzero
zero-ℕ₂ <-ℕ₂ zero-ℕ₂ = empty
zero-ℕ₂ <-ℕ₂ one-ℕ₂ = unit
zero-ℕ₂ <-ℕ₂ double-plus-two-ℕ₂ y = unit
zero-ℕ₂ <-ℕ₂ double-plus-three-ℕ₂ y = unit
one-ℕ₂ <-ℕ₂ zero-ℕ₂ = empty
one-ℕ₂ <-ℕ₂ one-ℕ₂ = empty
one-ℕ₂ <-ℕ₂ double-plus-two-ℕ₂ y = unit
one-ℕ₂ <-ℕ₂ double-plus-three-ℕ₂ y = unit
double-plus-two-ℕ₂ x <-ℕ₂ zero-ℕ₂ = empty
double-plus-two-ℕ₂ x <-ℕ₂ one-ℕ₂ = empty
double-plus-two-ℕ₂ x <-ℕ₂ double-plus-two-ℕ₂ y = x <-ℕ₂ y
double-plus-two-ℕ₂ x <-ℕ₂ double-plus-three-ℕ₂ y = x <-ℕ₂ y
double-plus-three-ℕ₂ x <-ℕ₂ zero-ℕ₂ = empty
double-plus-three-ℕ₂ x <-ℕ₂ one-ℕ₂ = empty
double-plus-three-ℕ₂ x <-ℕ₂ double-plus-two-ℕ₂ y = x <-ℕ₂ y
double-plus-three-ℕ₂ x <-ℕ₂ double-plus-three-ℕ₂ y = x <-ℕ₂ y

antireflexive-le-ℕ₂ : (x : ℕ₂) → ¬ (x <-ℕ₂ x)
antireflexive-le-ℕ₂ zero-ℕ₂ = id
antireflexive-le-ℕ₂ one-ℕ₂ = id
antireflexive-le-ℕ₂ (double-plus-two-ℕ₂ x) = antireflexive-le-ℕ₂ x
antireflexive-le-ℕ₂ (double-plus-three-ℕ₂ x) = antireflexive-le-ℕ₂ x

strong-antisymmetric-le-ℕ₂ : (x y : ℕ₂) → (x <-ℕ₂ y) → (y <-ℕ₂ x) → empty
strong-antisymmetric-le-ℕ₂ zero-ℕ₂ zero-ℕ₂ () K
strong-antisymmetric-le-ℕ₂ zero-ℕ₂ one-ℕ₂ H ()
strong-antisymmetric-le-ℕ₂ zero-ℕ₂ (double-plus-two-ℕ₂ y) H ()
strong-antisymmetric-le-ℕ₂ zero-ℕ₂ (double-plus-three-ℕ₂ y) H ()
strong-antisymmetric-le-ℕ₂ one-ℕ₂ zero-ℕ₂ () K
strong-antisymmetric-le-ℕ₂ one-ℕ₂ one-ℕ₂ () K
strong-antisymmetric-le-ℕ₂ one-ℕ₂ (double-plus-two-ℕ₂ y) H ()
strong-antisymmetric-le-ℕ₂ one-ℕ₂ (double-plus-three-ℕ₂ y) H ()
strong-antisymmetric-le-ℕ₂
  (double-plus-two-ℕ₂ x) (double-plus-two-ℕ₂ y) H K =
  strong-antisymmetric-le-ℕ₂ x y H K
strong-antisymmetric-le-ℕ₂
  (double-plus-two-ℕ₂ x) (double-plus-three-ℕ₂ y) H K =
  strong-antisymmetric-le-ℕ₂ x y H K
strong-antisymmetric-le-ℕ₂
  (double-plus-three-ℕ₂ x) (double-plus-two-ℕ₂ y) H K =
  strong-antisymmetric-le-ℕ₂ x y H K
strong-antisymmetric-le-ℕ₂
  (double-plus-three-ℕ₂ x) (double-plus-three-ℕ₂ y) H K =
  strong-antisymmetric-le-ℕ₂ x y H K

antisymmetric-le-ℕ₂ : (x y : ℕ₂) → (x <-ℕ₂ y) → (y <-ℕ₂ x) → Id x y
antisymmetric-le-ℕ₂ x y H K =
  ex-falso (strong-antisymmetric-le-ℕ₂ x y H K)

-- We define the standard binary finite types

Fin₂ : ℕ₂ → UU lzero
Fin₂ zero-ℕ₂ = empty
Fin₂ one-ℕ₂ = unit
Fin₂ (double-plus-two-ℕ₂ k) = coprod (coprod (Fin₂ k) (Fin₂ k)) (Fin two-ℕ)
Fin₂ (double-plus-three-ℕ₂ k) = coprod (coprod (Fin₂ k) (Fin₂ k)) (Fin three-ℕ)

-- We define the inclusion of the standard binary finite types into the binary
-- natural numbers

nat-Fin₂ : {k : ℕ₂} → Fin₂ k → ℕ₂
nat-Fin₂ {one-ℕ₂} x = zero-ℕ₂
nat-Fin₂ {double-plus-two-ℕ₂ k} (inl (inl x)) = nat-Fin₂ x
nat-Fin₂ {double-plus-two-ℕ₂ k} (inl (inr x)) = add-ℕ₂ (nat-Fin₂ x) k
nat-Fin₂ {double-plus-two-ℕ₂ k} (inr (inl x)) = add-ℕ₂ k k
nat-Fin₂ {double-plus-two-ℕ₂ k} (inr (inr x)) = succ-ℕ₂ (add-ℕ₂ k k)
nat-Fin₂ {double-plus-three-ℕ₂ k} (inl (inl x)) = nat-Fin₂ x
nat-Fin₂ {double-plus-three-ℕ₂ k} (inl (inr x)) = add-ℕ₂ (nat-Fin₂ x) k
nat-Fin₂ {double-plus-three-ℕ₂ k} (inr (inl (inl x))) = add-ℕ₂ k k
nat-Fin₂ {double-plus-three-ℕ₂ k} (inr (inl (inr x))) = succ-ℕ₂ (add-ℕ₂ k k)
nat-Fin₂ {double-plus-three-ℕ₂ k} (inr (inr x)) = succ-ℕ₂ (succ-ℕ₂ (add-ℕ₂ k k))

-- We show that the inclusion of Fin₂ k into ℕ₂ is bounded

{-
strict-upper-bound-nat-Fin-ℕ₂ :
  (k : ℕ₂) (x : Fin₂ k) → (nat-Fin₂ x) <-ℕ₂ k
strict-upper-bound-nat-Fin-ℕ₂ one-ℕ₂ star = star
strict-upper-bound-nat-Fin-ℕ₂ (double-plus-two-ℕ₂ k) (inl (inl x)) = {!!}
strict-upper-bound-nat-Fin-ℕ₂ (double-plus-two-ℕ₂ k) (inl (inr x)) = {!!}
strict-upper-bound-nat-Fin-ℕ₂ (double-plus-two-ℕ₂ k) (inr x) = {!!}
strict-upper-bound-nat-Fin-ℕ₂ (double-plus-three-ℕ₂ k) x = {!!}
-}
