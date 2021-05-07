{-# OPTIONS --without-K --exact-split #-}

module extra.b-systems where

import book
open book public

--------------------------------------------------------------------------------

-- (Dependency) systems are the backbone of a dependent type theory

record system (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2) where
  coinductive
  field
    type    : UU l1
    element : type → UU l2
    slice   : (X : type) → system l1 l2

--------------------------------------------------------------------------------

-- We introduce morphisms of systems

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
    type    : (X : system.type A) →
              Id (hom-system.type f X) (hom-system.type g X)
    element : (X : system.type A) (x : system.element A X) →
              Id ( tr ( system.element B)
                      ( type X)
                      ( hom-system.element f X x))
                 ( hom-system.element g X x)
    slice   : (X : system.type A) →
              htpy-hom-system
                ( comp-hom-system
                  ( tr-hom-system {A = B} (type X))
                  ( hom-system.slice f X))
                ( hom-system.slice g X)

--------------------------------------------------------------------------------

-- We introduce weakening structure on systems

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

--------------------------------------------------------------------------------

-- We introduce substitution structure on a system

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

--------------------------------------------------------------------------------

{- We introduce the structure of a generic element on a system equipped with
   weakening structure -}
              
record generic-element
  {l1 l2 : Level} (A : system l1 l2) (W : weakening A) :
  UU (l1 ⊔ l2)
  where
  coinductive
  field
    type  : (X : system.type A) →
               system.element
                 ( system.slice A X)
                 ( hom-system.type (weakening.type W X) X)
    slice : (X : system.type A) →
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
    type  : (X : system.type A) →
               Id ( tr
                    ( system.element (system.slice B (hom-system.type h X)))
                    ( htpy-hom-system.type
                      ( preserves-weakening.type Wh X)
                      ( X))
                    ( hom-system.element
                      ( hom-system.slice h X)
                      ( hom-system.type (weakening.type WA X) X)
                      ( generic-element.type δA X)))
                  ( generic-element.type δB (hom-system.type h X))
    slice : (X : system.type A) →
               preserves-generic-element
                 ( weakening.slice WA X)
                 ( generic-element.slice δA X)
                 ( weakening.slice WB (hom-system.type h X))
                 ( generic-element.slice δB (hom-system.type h X))
                 ( hom-system.slice h X)
                 ( preserves-weakening.slice Wh X)

--------------------------------------------------------------------------------

-- We now state the laws for weakening, substitution, and the generic element

record weakening-preserves-weakening
  {l1 l2 : Level} (A : system l1 l2) (W : weakening A) : UU (l1 ⊔ l2)
  where
  coinductive
  field
    type  : (X : system.type A) →
            preserves-weakening W (weakening.slice W X) (weakening.type W X)
    slice : (X : system.type A) →
            weakening-preserves-weakening
              ( system.slice A X)
              ( weakening.slice W X)

record substitution-preserves-substitution
  {l1 l2 : Level} (A : system l1 l2) (S : substitution A) : UU (l1 ⊔ l2)
  where
  coinductive
  field
    type  : (X : system.type A) (x : system.element A X) →
            preserves-substitution
              ( substitution.slice S X)
              ( S)
              ( substitution.type S X x)
    slice : (X : system.type A) →
            substitution-preserves-substitution
              ( system.slice A X)
              ( substitution.slice S X)

record weakening-preserves-substitution
  {l1 l2 : Level} (A : system l1 l2) (S : substitution A) (W : weakening A) :
  UU (l1 ⊔ l2)
  where
  coinductive
  field
    type  : (X : system.type A) →
            preserves-substitution
              ( S)
              ( substitution.slice S X)
              ( weakening.type W X)
    slice : (X : system.type A) →
            weakening-preserves-substitution
              ( system.slice A X)
              ( substitution.slice S X)
              ( weakening.slice W X)

record substitution-preserves-weakening
  {l1 l2 : Level} (A : system l1 l2) (W : weakening A) (S : substitution A) :
  UU (l1 ⊔ l2)
  where
  coinductive
  field
    type  : (X : system.type A) (x : system.element A X) →
            preserves-weakening
              ( weakening.slice W X)
              ( W)
              ( substitution.type S X x)
    slice : (X : system.type A) →
            substitution-preserves-weakening
              ( system.slice A X)
              ( weakening.slice W X)
              ( substitution.slice S X)

record weakening-preserves-generic-element
  {l1 l2 : Level} (A : system l1 l2) (W : weakening A)
  (WW : weakening-preserves-weakening A W) (δ : generic-element A W) :
  UU (l1 ⊔ l2)
  where
  coinductive
  field
    type  : (X : system.type A) →
            preserves-generic-element
              ( W)
              ( δ)
              ( weakening.slice W X)
              ( generic-element.slice δ X)
              ( weakening.type W X)
              ( weakening-preserves-weakening.type WW X)
    slice : (X : system.type A) →
            weakening-preserves-generic-element
              ( system.slice A X)
              ( weakening.slice W X)
              ( weakening-preserves-weakening.slice WW X)
              ( generic-element.slice δ X)

record substitution-preserves-generic-element
  {l1 l2 : Level} (A : system l1 l2) (W : weakening A)
  (δ : generic-element A W) (S : substitution A)
  (SW : substitution-preserves-weakening A W S) :
  UU (l1 ⊔ l2)
  where
  coinductive
  field
    type  : (X : system.type A) (x : system.element A X) →
            preserves-generic-element
              ( weakening.slice W X)
              ( generic-element.slice δ X)
              ( W)
              ( δ)
              ( substitution.type S X x)
              ( substitution-preserves-weakening.type SW X x)
    slice : (X : system.type A) →
            substitution-preserves-generic-element
              ( system.slice A X)
              ( weakening.slice W X)
              ( generic-element.slice δ X)
              ( substitution.slice S X)
              ( substitution-preserves-weakening.slice SW X)

record substitution-cancels-weakening
  {l1 l2 : Level} (A : system l1 l2) (W : weakening A) (S : substitution A) :
  UU (l1 ⊔ l2)
  where
  coinductive
  field
    type  : (X : system.type A) (x : system.element A X) →
            htpy-hom-system
              ( comp-hom-system
                ( substitution.type S X x)
                ( weakening.type W X))
              ( id-hom-system A)
    slice : (X : system.type A) →
            substitution-cancels-weakening
              ( system.slice A X)
              ( weakening.slice W X)
              ( substitution.slice S X)

record generic-element-is-identity
  {l1 l2 : Level} (A : system l1 l2) (W : weakening A) (S : substitution A)
  (δ : generic-element A W) (S!W : substitution-cancels-weakening A W S) :
  UU (l1 ⊔ l2)
  where
  coinductive
  field
    type  : (X : system.type A) (x : system.element A X) →
            Id ( tr
                 ( system.element A)
                 ( htpy-hom-system.type
                   ( substitution-cancels-weakening.type S!W X x) X)
                 ( hom-system.element
                   ( substitution.type S X x)
                   ( hom-system.type (weakening.type W X) X)
                   ( generic-element.type δ X))) x
    slice : (X : system.type A) →
            generic-element-is-identity
              ( system.slice A X)
              ( weakening.slice W X)
              ( substitution.slice S X)
              ( generic-element.slice δ X)
              ( substitution-cancels-weakening.slice S!W X)

record substitution-by-generic-element
  {l1 l2 : Level} (A : system l1 l2) (W : weakening A) (S : substitution A)
  (δ : generic-element A W) :
  UU (l1 ⊔ l2)
  where
  coinductive
  field
    type  : (X : system.type A) →
            htpy-hom-system
              ( comp-hom-system
                ( substitution.type
                  ( substitution.slice S X)
                  ( hom-system.type (weakening.type W X) X)
                  ( generic-element.type δ X))
                ( weakening.type
                  ( weakening.slice W X)
                  ( hom-system.type (weakening.type W X) X)))
              ( id-hom-system (system.slice A X))
    slice : (X : system.type A) →
            substitution-by-generic-element
              ( system.slice A X)
              ( weakening.slice W X)
              ( substitution.slice S X)
              ( generic-element.slice δ X)

--------------------------------------------------------------------------------

-- We complete the definition of a dependent type theory

record dependent-type-theory
  (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2)
  where
  field
    sys : system l1 l2
    W   : weakening sys
    S   : substitution sys
    δ   : generic-element sys W
    WW  : weakening-preserves-weakening sys W
    SS  : substitution-preserves-substitution sys S
    WS  : weakening-preserves-substitution sys S W
    SW  : substitution-preserves-weakening sys W S
    Wδ  : weakening-preserves-generic-element sys W WW δ
    Sδ  : substitution-preserves-generic-element sys W δ S SW
    S!W : substitution-cancels-weakening sys W S
    δid : generic-element-is-identity sys W S δ S!W
    Sδ! : substitution-by-generic-element sys W S δ

--------------------------------------------------------------------------------
