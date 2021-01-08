{-# OPTIONS --without-K --exact-split #-}

module extra.polynomial-endofunctors where

open import book public

------------------------------------------------------------------------------

module Container {l1 l2 : Level} (A : UU l1) (B : A → UU l2) where

  module Polynomial-Endofunctor {l3 : Level} (X : UU l3) where
  
    -- The polynomial endofunctor associated to a container
  
    type-polynomial-endofunctor : UU (l1 ⊔ l2 ⊔ l3)
    type-polynomial-endofunctor = Σ A (λ x → B x → X)
  
    -- We characterize the identity type of type-polynomial-endofunctor
  
    Eq-type-polynomial-endofunctor :
      (x y : type-polynomial-endofunctor) → UU (l1 ⊔ l2 ⊔ l3)
    Eq-type-polynomial-endofunctor x y =
      Σ (Id (pr1 x) (pr1 y)) (λ p → (pr2 x) ~ ((pr2 y) ∘ (tr B p)))

    refl-Eq-type-polynomial-endofunctor :
      (x : type-polynomial-endofunctor) → Eq-type-polynomial-endofunctor x x
    refl-Eq-type-polynomial-endofunctor (pair x α) = pair refl refl-htpy

    is-contr-total-Eq-type-polynomial-endofunctor :
      (x : type-polynomial-endofunctor) →
      is-contr
        ( Σ type-polynomial-endofunctor (Eq-type-polynomial-endofunctor x))
    is-contr-total-Eq-type-polynomial-endofunctor (pair x α) =
      is-contr-total-Eq-structure
        ( ( λ (y : A) (β : B y → X) (p : Id x y) → α ~ (β ∘ tr B p)))
        ( is-contr-total-path x)
        ( pair x refl)
        ( is-contr-total-htpy α)

    Eq-type-polynomial-endofunctor-eq :
      (x y : type-polynomial-endofunctor) →
      Id x y → Eq-type-polynomial-endofunctor x y
    Eq-type-polynomial-endofunctor-eq x .x refl =
      refl-Eq-type-polynomial-endofunctor x

    is-equiv-Eq-type-polynomial-endofunctor-eq :
      (x y : type-polynomial-endofunctor) →
      is-equiv (Eq-type-polynomial-endofunctor-eq x y)
    is-equiv-Eq-type-polynomial-endofunctor-eq x =
      fundamental-theorem-id x
        ( refl-Eq-type-polynomial-endofunctor x)
        ( is-contr-total-Eq-type-polynomial-endofunctor x)
        ( Eq-type-polynomial-endofunctor-eq x)

    eq-Eq-type-polynomial-endofunctor :
      (x y : type-polynomial-endofunctor) →
      Eq-type-polynomial-endofunctor x y → Id x y
    eq-Eq-type-polynomial-endofunctor x y =
      map-inv-is-equiv (is-equiv-Eq-type-polynomial-endofunctor-eq x y)

    isretr-eq-Eq-type-polynomial-endofunctor :
      (x y : type-polynomial-endofunctor) →
      ( ( eq-Eq-type-polynomial-endofunctor x y) ∘
        ( Eq-type-polynomial-endofunctor-eq x y)) ~ id
    isretr-eq-Eq-type-polynomial-endofunctor x y =
      isretr-map-inv-is-equiv (is-equiv-Eq-type-polynomial-endofunctor-eq x y)

    coh-refl-eq-Eq-type-polynomial-endofunctor :
      (x : type-polynomial-endofunctor) →
      Id ( eq-Eq-type-polynomial-endofunctor x x
           ( refl-Eq-type-polynomial-endofunctor x)) refl
    coh-refl-eq-Eq-type-polynomial-endofunctor x =
      isretr-eq-Eq-type-polynomial-endofunctor x x refl

  ------------------------------------------------------------------------------

  open Polynomial-Endofunctor public

  -- The action on morphisms of the polynomial endofunctor
  
  map-polynomial-endofunctor :
    {l3 l4 : Level} {X : UU l3} {Y : UU l4} (f : X → Y) →
    type-polynomial-endofunctor X → type-polynomial-endofunctor Y
  map-polynomial-endofunctor f (pair x α) = pair x (f ∘ α)

  -- The action on homotopies of the polynomial endofunctor
  
  htpy-polynomial-endofunctor :
    {l3 l4 : Level} {X : UU l3} {Y : UU l4} {f g : X → Y} →
    f ~ g → map-polynomial-endofunctor f ~ map-polynomial-endofunctor g
  htpy-polynomial-endofunctor {X = X} {Y} {f} {g} H (pair x α) =
    eq-Eq-type-polynomial-endofunctor Y
      ( map-polynomial-endofunctor f (pair x α))
      ( map-polynomial-endofunctor g (pair x α))
      ( pair refl (H ·r α))
  
  coh-refl-htpy-polynomial-endofunctor :
    {l3 l4 : Level} {X : UU l3} {Y : UU l4} (f : X → Y) →
    htpy-polynomial-endofunctor (refl-htpy {f = f}) ~ refl-htpy
  coh-refl-htpy-polynomial-endofunctor {X = X} {Y} f (pair x α) =
    coh-refl-eq-Eq-type-polynomial-endofunctor Y
      ( map-polynomial-endofunctor f (pair x α)) 

  -- algebras for the polynomial endofunctors
  
  algebra-polynomial-endofunctor :
    (l : Level) → UU (lsuc l ⊔ l1 ⊔ l2)
  algebra-polynomial-endofunctor l =
    Σ (UU l) (λ X → type-polynomial-endofunctor X → X)

  type-algebra-polynomial-endofunctor :
    {l : Level} → algebra-polynomial-endofunctor l → UU l
  type-algebra-polynomial-endofunctor X = pr1 X

  structure-algebra-polynomial-endofunctor :
    {l : Level} (X : algebra-polynomial-endofunctor l) →
    type-polynomial-endofunctor (type-algebra-polynomial-endofunctor X) →
    type-algebra-polynomial-endofunctor X
  structure-algebra-polynomial-endofunctor X = pr2 X

open Container public
