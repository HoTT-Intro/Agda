{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.b-systems where

import book
open book public

record system (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2) where
  coinductive
  field
    type    : UU l1
    element : type → UU l2
    slice   : (X : type) → system l1 l2

record hom-system
  {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : system l3 l4) :
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive
  field
    type    : system.type A → system.type B
    element : (X : system.type A) →
              system.element A X → system.element B (type X)
    slice   : (X : system.type A) →
              hom-system
                ( system.slice A X)
                ( system.slice B (type X))

id-hom-system :
  {l1 l2 : Level} (A : system l1 l2) → hom-system A A
hom-system.type (id-hom-system A) X = X
hom-system.element (id-hom-system A) X x = x
hom-system.slice (id-hom-system A) X = id-hom-system (system.slice A X)

comp-hom-system :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : system l1 l2} {B : system l3 l4} {C : system l5 l6}
  (g : hom-system B C) (f : hom-system A B) → hom-system A C
hom-system.type (comp-hom-system g f) =
  hom-system.type g ∘ hom-system.type f
hom-system.element (comp-hom-system g f) X =
  hom-system.element g (hom-system.type f X) ∘ hom-system.element f X
hom-system.slice (comp-hom-system g f) X =
  comp-hom-system
    ( hom-system.slice g (hom-system.type f X))
    ( hom-system.slice f X)

tr-hom-system :
  {l1 l2 : Level} {A : system l1 l2} {X Y : system.type A} (p : Id X Y) →
  hom-system (system.slice A X) (system.slice A Y)
tr-hom-system {A = A} {X = X} refl = id-hom-system (system.slice A X)

record htpy-hom-system
  {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
  (f g : hom-system A B) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive
  field
    path-type    : (X : system.type A) →
                   Id (hom-system.type f X) (hom-system.type g X)
    path-element : (X : system.type A) (x : system.element A X) →
                   Id ( tr ( system.element B)
                           ( path-type X)
                           ( hom-system.element f X x))
                      ( hom-system.element g X x)
    slice        : (X : system.type A) →
                   htpy-hom-system
                     ( comp-hom-system
                       ( tr-hom-system {A = B} (path-type X))
                       ( hom-system.slice f X))
                     ( hom-system.slice g X)

record weakening {l1 l2 : Level} (A : system l1 l2) : UU (lsuc l1 ⊔ lsuc l2)
  where
  coinductive
  field
    type  : (X : system.type A) → hom-system A (system.slice A X)
    slice : (X : system.type A) → weakening (system.slice A X)

record preserves-weakening
  {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
  (WA : weakening A) (WB : weakening B) (h : hom-system A B) :
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive
  field
    type  : (X : system.type A) →
            htpy-hom-system
              ( comp-hom-system
                ( hom-system.slice h X)
                ( weakening.type WA X))
              ( comp-hom-system
                ( weakening.type WB (hom-system.type h X))
                ( h))
    slice : (X : system.type A) →
            preserves-weakening
              ( weakening.slice WA X)
              ( weakening.slice WB (hom-system.type h X))
              ( hom-system.slice h X)

record substitution {l1 l2 : Level} (A : system l1 l2) : UU (lsuc l1 ⊔ lsuc l2)
  where
  coinductive
  field
    type  : (X : system.type A) (x : system.element A X) →
            hom-system (system.slice A X) A
    slice : (X : system.type A) → substitution (system.slice A X)

record preserves-substitution
  {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
  (SA : substitution A) (SB : substitution B) (h : hom-system A B) :
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive
  field
    type  : (X : system.type A) (x : system.element A X) →
            htpy-hom-system
              ( comp-hom-system
                ( h)
                ( substitution.type SA X x))
              ( comp-hom-system
                ( substitution.type SB
                  ( hom-system.type h X)
                  ( hom-system.element h X x))
                ( hom-system.slice h X))
    slice : (X : system.type A) →
            preserves-substitution
              ( substitution.slice SA X)
              ( substitution.slice SB (hom-system.type h X))
              ( hom-system.slice h X)

record generic-element
  {l1 l2 : Level} (A : system l1 l2) (W : weakening A) :
  UU (l1 ⊔ l2)
  where
  coinductive
  field
    id-type  : (X : system.type A) →
               system.element
                 ( system.slice A X)
                 ( hom-system.type (weakening.type W X) X)
    id-slice : (X : system.type A) →
               generic-element (system.slice A X) (weakening.slice W X)

record preserves-generic-element
  {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
  (WA : weakening A) (δA : generic-element A WA)
  (WB : weakening B) (δB : generic-element B WB)
  (h : hom-system A B) (Wh : preserves-weakening WA WB h) :
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive
  field
    id-type  : (X : system.type A) →
               Id ( tr
                    ( system.element (system.slice B (hom-system.type h X)))
                    ( htpy-hom-system.path-type
                      ( preserves-weakening.type Wh X)
                      ( X))
                    ( hom-system.element
                      ( hom-system.slice h X)
                      ( hom-system.type (weakening.type WA X) X)
                      ( generic-element.id-type δA X)))
                  ( generic-element.id-type δB (hom-system.type h X))
    id-slice : (X : system.type A) → {!!}

--------------------------------------------------------------------------------

data unit-UU (l : Level) : UU l where
  star-UU : unit-UU l

context-system : {l1 l2 : Level} (A : system l1 l2) (n : ℕ) → UU l1
context-system {l1} {l2} A zero-ℕ = unit-UU _
context-system {l1} {l2} A (succ-ℕ zero-ℕ) = system.type A
context-system {l1} {l2} A (succ-ℕ (succ-ℕ n)) = 
  Σ ( system.type A)
    ( λ X → context-system (system.slice A X) (succ-ℕ n))

pred-ℕ : ℕ → ℕ
pred-ℕ zero-ℕ = zero-ℕ
pred-ℕ (succ-ℕ n) = n

truncate-context-system : {l1 l2 : Level} (A : system l1 l2) (n : ℕ) →
  context-system A n → context-system A (pred-ℕ n)
truncate-context-system A zero-ℕ Γ = Γ
truncate-context-system A (succ-ℕ zero-ℕ) Γ = star-UU
truncate-context-system A (succ-ℕ (succ-ℕ zero-ℕ)) (pair A₀ Γ) = A₀
truncate-context-system A (succ-ℕ (succ-ℕ (succ-ℕ n))) (pair A₀ Γ) =
  pair
    ( A₀)
    (truncate-context-system (system.slice A A₀) (succ-ℕ (succ-ℕ n)) Γ)

record B-frame (l : Level) : UU (lsuc l) where
  field
    type-B : ℕ → UU l
    element-B : (n : ℕ) → UU l
    ft-B : (n : ℕ) → type-B (succ-ℕ n) → type-B n
    ∂-B : (n : ℕ) → element-B n → type-B n

record hom-B-frame {l1 l2 : Level} (A : B-frame l1) (B : B-frame l2) :
  UU (l1 ⊔ l2) where
  field
    hom-type-B : (n : ℕ) → B-frame.type-B A n → B-frame.type-B B n
    hom-element-B : (n : ℕ) → B-frame.element-B A n → B-frame.element-B B n
    hom-ft-B : (n : ℕ) (X : B-frame.type-B A (succ-ℕ n)) →
      Id ( B-frame.ft-B B n (hom-type-B (succ-ℕ n) X))
         ( hom-type-B n (B-frame.ft-B A n X))
    hom-∂-B : (n : ℕ) (t : B-frame.element-B A n) →
      Id ( B-frame.∂-B B n (hom-element-B n t))
         ( hom-type-B n (B-frame.∂-B A n t))

{-
iterated-ft-B :
  {l : Level} (A : B-frame l) (n k : ℕ) (X : B-frame.type-B A (add-ℕ n x))
-}

slice-B :
  {l : Level} (A : B-frame l) (n : ℕ) (X : B-frame.type-B A n) → B-frame l
slice-B A n X =
  record
    { type-B = λ x → Σ (B-frame.type-B A (succ-ℕ (add-ℕ n x))) (λ Y → Id {!!} X) ;
      element-B = {!!} ;
      ft-B = {!!} ;
      ∂-B = {!!} }
    
