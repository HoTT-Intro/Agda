{-# OPTIONS --without-K --exact-split #-}

module flat-modality where

import 12-function-extensionality-solutions
open 12-function-extensionality-solutions public

{- Agda has crisp contexts which allow us to seperate crisp variables. This let's us work with the flat modality. -}

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


-- flattening crisp coproducts

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

-- and so on
