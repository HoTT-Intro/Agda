{-# OPTIONS --without-K --exact-split #-}

module flat-modality where

import 12-function-extensionality-solutions
open 12-function-extensionality-solutions public

{- Agda has crisp contexts which allow us to seperate crisp variables. This let's us work with (something that is hopefully) the flat modality.

  In later comments [S] denotes: Brouwer's fixed-point theorem in real-cohesive homotopy type theory, Michael Shulman
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


-- -- crisp ♭-induction

-- [S, Lemma 5.1]
-- "♭-induction C N M" corresponds to "let u^♭ := M in N" from [S]

♭-induction : {@♭ l1 l2 : Level} {@♭ A : UU l1} (@♭ C : (@♭ x : ♭ A) → UU l2) (N : (@♭ u : A) → C (♭-unit u)) (@♭ M : ♭ A) → C M
♭-induction C N (♭-unit x) = N x

-- [S, Lemma 5.2]
-- Commuting ♭-induction with ♭-unit

♭-induction-♭-unit : {@♭ l1 l2 : Level} {@♭ A : UU l1} (@♭ C : (@♭ x : ♭ A) → UU l2) (@♭ N : (@♭ u : A) → C (♭-unit u)) (@♭ M : ♭ A)
  → Id (♭-unit (♭-induction C N M)) (♭-induction (λ (@♭ x : ♭ A) → ♭ (C x)) (λ u → ♭-unit (N u)) M)
♭-induction-♭-unit C N (♭-unit x) = refl


