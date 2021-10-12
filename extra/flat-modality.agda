{-# OPTIONS --without-K --exact-split #-}

module extra.flat-modality where

open import book public

{- Agda has crisp contexts which allow us to seperate crisp variables. This let's us work with (something that is hopefully) the flat modality.

  In later comments [S] denotes: Brouwer's fixed-point theorem in real-cohesive homotopy type theory, Michael Shulman

  We roughly follow the outline of [S]
-}

-- We define the flat modality as an inductive type with special care with the crispness of variables
-- It is unclear what the semantics of such a beast are but we take a leap of faith and say this is the flat modality Mike defined
data ♭ {@♭ l : Level} (@♭ A : UU l) : UU l where
  ♭-unit : (@♭ x : A) → ♭ A

♭-counit : {@♭ l : Level} {@♭ A : UU l} → ♭ A → A
♭-counit (♭-unit x) = x

-- We can turn off pattern matching for this thing but I don't see why we would need to
-- Putting this at the top will break everything {-# OPTIONS --no-flat-split #-}

-- ♭ is a functor (on crisp types)

functor-♭ : {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2} (@♭ f : A → B) → ♭ A → ♭ B
functor-♭ f (♭-unit x) = ♭-unit (f x)

functor-♭-id : {@♭ l : Level} {@♭ A : Set l} → (functor-♭ (id {A = A})) ~ (id {A = ♭ A})
functor-♭-id {l} {A} (♭-unit x) = refl

functor-♭-comp : {@♭ l1 l2 l3 : Level} {@♭ A : UU l1} {@♭ B : UU l2} {@♭ C : UU l3} (@♭ f : B → C) (@♭ g : A → B) → (functor-♭ (f ∘ g)) ~ ((functor-♭ f) ∘ (functor-♭ g))
functor-♭-comp f g (♭-unit x) = refl

-- -- 5. crisp ♭-induction

-- [S, Lemma 5.1]
-- "♭-induction C N M" corresponds to "let u^♭ := M in N" from [S]

ind-♭ : {@♭ l1 l2 : Level} {@♭ A : UU l1} (@♭ C : (@♭ x : ♭ A) → UU l2) (@♭ N : (@♭ u : A) → C (♭-unit u)) (@♭ M : ♭ A) → C M
ind-♭ C N (♭-unit x) = N x

-- [S, Lemma 5.2]
-- Commuting ind-♭ with ♭-unit

ind-♭-♭-unit : {@♭ l1 l2 : Level} {@♭ A : UU l1} (@♭ C : (@♭ x : ♭ A) → UU l2) (@♭ N : (@♭ u : A) → C (♭-unit u)) (@♭ M : ♭ A)
  → Id (♭-unit (ind-♭ C N M)) (ind-♭ (λ (@♭ x : ♭ A) → ♭ (C x)) (λ u → ♭-unit (N u)) M)
ind-♭-♭-unit C N (♭-unit x) = refl

-- [S, Lemma 5.3]
-- Commuting ind-♭ with ♭

ind-♭-♭ : {@♭ l1 l2 : Level} {@♭ A : UU l1} (@♭ N : (@♭ u : A) → UU l2) (@♭ M : ♭ A)
  → Id (♭ (ind-♭ (λ x → UU l2) N M)) (ind-♭ (λ x → UU l2) (λ (@♭ u : A) → ♭ (N u)) M )
ind-♭-♭ N (♭-unit x) = refl


-- [S, Lemma 5.4]
-- Crisp case analysis on coproducts

♭-ind-coprod : {@♭ l1 l2 l3 : Level} {@♭ A : UU l1} {@♭ B : UU l2} (@♭ C : (@♭ z : coprod A B) → UU l3)
  (@♭ N : (@♭ u : A) → C (inl u)) (@♭ P : (@♭ v : B) → C (inr v))
  (@♭ M : coprod A B) → C M
♭-ind-coprod C N P (inl x) = N x
♭-ind-coprod C N P (inr x) = P x


-- [S, Corollary 5.5]
-- flat distributes over coproducts

♭-coprod-coprod-♭ : {@♭ l1 l2 : Level} (@♭ A : UU l1) (@♭ B : UU l2) → coprod (♭ A) (♭ B) → ♭ (coprod A B)
♭-coprod-coprod-♭ A B (inl (♭-unit x)) = ♭-unit (inl x)
♭-coprod-coprod-♭ A B (inr (♭-unit x)) = ♭-unit (inr x)

coprod-♭-♭-coprod : {@♭ l1 l2 : Level} (@♭ A : UU l1) (@♭ B : UU l2) → ♭ (coprod A B) → coprod (♭ A) (♭ B)
coprod-♭-♭-coprod A B (♭-unit (inl x)) = inl (♭-unit x)
coprod-♭-♭-coprod A B (♭-unit (inr x)) = inr (♭-unit x)

issec-coprod-♭-♭-coprod : {@♭ l1 l2 : Level} (@♭ A : UU l1) (@♭ B : UU l2) → (♭-coprod-coprod-♭ A B ∘ coprod-♭-♭-coprod A B) ~ id
issec-coprod-♭-♭-coprod A B (♭-unit (inl x)) = refl
issec-coprod-♭-♭-coprod A B (♭-unit (inr x)) = refl

isretr-coprod-♭-♭-coprod : {@♭ l1 l2 : Level} (@♭ A : UU l1) (@♭ B : UU l2) → (coprod-♭-♭-coprod A B ∘ ♭-coprod-coprod-♭ A B) ~ id
isretr-coprod-♭-♭-coprod A B (inl (♭-unit x)) = refl
isretr-coprod-♭-♭-coprod A B (inr (♭-unit x)) = refl

is-equiv-♭-coprod-coprod-♭ : {@♭ l1 l2 : Level} (@♭ A : UU l1) (@♭ B : UU l2) → is-equiv (♭-coprod-coprod-♭ A B)
is-equiv-♭-coprod-coprod-♭ A B = is-equiv-has-inverse (coprod-♭-♭-coprod A B) (issec-coprod-♭-♭-coprod A B) (isretr-coprod-♭-♭-coprod A B)

equiv-♭-coprod-coprod-♭ : {@♭ l1 l2 : Level} (@♭ A : UU l1) (@♭ B : UU l2) → coprod (♭ A) (♭ B) ≃ ♭ (coprod A B)
equiv-♭-coprod-coprod-♭ A B = pair (♭-coprod-coprod-♭ A B) (is-equiv-♭-coprod-coprod-♭ A B)

-- In general we can apply the same method to most other positive type formers

-- TODO:
-- ♭ empty = empty
-- ♭ unit = unit
-- ♭ ℕ ≃ ℕ


-- [S, Theorem 5.6]
-- Crisp J-eliminator

♭-ind-Id :
  {@♭ i j : Level} {@♭ A : UU i} (@♭ x : A) (@♭ B : (@♭ y : A) (@♭ p : Id x y) → UU j) →
  (@♭ d : B x refl) → (@♭ y : A) (@♭ p : Id x y) → B y p
♭-ind-Id x B b y refl = b


-- [S, Theorem 5.7]
-- Crisp coequalizers

-- TODO


-- [S, Theorem 5.8]
-- Crisp truncations

-- TODO


-- -- 6. Discreteness and ♭

-- [S, Theorem 6.1]
-- the identity type of a flat type is the flattened identity type

-- We put the code, encode and decode functions in a module since we won't need to access them outside of the proof of the equivalence
module ♭-Id where

  -- codes for the identity type
  code : {@♭ l : Level} {@♭ A : UU l} → ♭ A → ♭ A → UU l
  code (♭-unit x) (♭-unit y) = ♭ (Id x y)

  -- reflexivity for codes
  r : {@♭ l : Level} {@♭ A : UU l} (u : ♭ A) → code u u
  r (♭-unit x) = ♭-unit refl

  -- encode
  encode : {@♭ l : Level} {@♭ A : UU l} (u v : ♭ A) → Id u v → code u v
  encode u u refl = r u

  -- decode
  decode : {@♭ l : Level} {@♭ A : UU l} (u v : ♭ A) → code u v → Id u v
  decode (♭-unit x) (♭-unit y) (♭-unit refl) = refl

  encode-decode : {@♭ l : Level} {@♭ A : UU l} (u v : ♭ A) → (encode u v ∘ decode u v) ~ id
  encode-decode (♭-unit x) (♭-unit x) (♭-unit refl) = refl

  decode-encode : {@♭ l : Level} {@♭ A : UU l} (u v : ♭ A) → (decode u v ∘ encode u v) ~ id
  decode-encode (♭-unit x) (♭-unit x) refl = refl

id-♭ : {@♭ l : Level} {@♭ A : UU l} (@♭ x y : A) → Id (♭-unit x) (♭-unit y) → ♭ (Id x y)
id-♭ x y p = ♭-Id.encode (♭-unit x) (♭-unit y) p

is-equiv-id-♭ : {@♭ l : Level} {@♭ A : UU l} (@♭ x y : A) → is-equiv (id-♭ x y)
is-equiv-id-♭ x y = is-equiv-has-inverse
                      (♭-Id.decode (♭-unit x) (♭-unit y))
                      (♭-Id.encode-decode (♭-unit x) (♭-unit y))
                      (♭-Id.decode-encode (♭-unit x) (♭-unit y))

equiv-id-♭ : {@♭ l : Level} {@♭ A : UU l} (@♭ x y : A) → Id (♭-unit x) (♭-unit y) ≃ ♭ (Id x y)
equiv-id-♭ x y = pair (id-♭ x y) (is-equiv-id-♭ x y)


-- [S, Corollary 6.2]
-- An alternative path type of ♭ A

equiv-id-♭' : {@♭ l : Level} {@♭ A : UU l} (@♭ x y : ♭ A) → Id x y ≃ ♭ (Id (♭-counit x) (♭-counit y))
equiv-id-♭' (♭-unit x) (♭-unit y) = equiv-id-♭ x y


