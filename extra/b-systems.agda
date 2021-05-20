{-# OPTIONS --without-K --exact-split #-}

module extra.b-systems where

import book
open book public

--------------------------------------------------------------------------------

{- (Dependency) systems are the structure around which a dependent type theory
   is built.

    Ã₀       Ã₁       Ã₂   
    |        |        |
    |        |        |
    V        V        V
    A₀ <---- A₁ <---- A₂ <---- ⋯

-}

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

--------------------------------------------------------------------------------

-- We first introduce heterogeneous homotopies, and then the actual homotopies

tr-hom-system :
  {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' : system l3 l4}
  (p : Id B B') (f : hom-system A B) (X : system.type A) →
  Id ( system.slice B (hom-system.type f X))
     ( system.slice B' (hom-system.type (tr (hom-system A) p f) X))
tr-hom-system refl f X = refl

record htpy-hom-system'
  {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' : system l3 l4} (p : Id B B')
  (f : hom-system A B) (g : hom-system A B') : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive
  field
    type    : hom-system.type (tr (hom-system A) p f) ~ hom-system.type g
    element : (X : system.type A) (x : system.element A X) →
              Id ( tr ( system.element B')
                      ( type X)
                      ( hom-system.element
                        ( tr (hom-system A) p f)
                        X x))
                 ( hom-system.element g X x)
    slice   : (X : system.type A) →
              htpy-hom-system'
                ( ( tr-hom-system p f X) ∙
                  ( ap (system.slice B') (type X)))
                ( hom-system.slice f X)
                ( hom-system.slice g X)

htpy-hom-system :
  {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
  (f g : hom-system A B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
htpy-hom-system f g = htpy-hom-system' refl f g

module htpy-hom-system
  {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
  {f g : hom-system A B}
  where

  type : htpy-hom-system f g →
         hom-system.type f ~ hom-system.type g
  type H = htpy-hom-system'.type H

  element : (H : htpy-hom-system f g) →
            (X : system.type A) (x : system.element A X) →
            Id ( tr (system.element B) (type H X) (hom-system.element f X x))
               ( hom-system.element g X x)
  element H = htpy-hom-system'.element H

  slice : (H : htpy-hom-system f g) (X : system.type A) →
          htpy-hom-system'
            ( ap (system.slice B) (type H X))
            ( hom-system.slice f X)
            ( hom-system.slice g X)
  slice H = htpy-hom-system'.slice H

refl-htpy-hom-system :
  {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
  (f : hom-system A B) → htpy-hom-system f f
htpy-hom-system'.type (refl-htpy-hom-system f) = refl-htpy
htpy-hom-system'.element (refl-htpy-hom-system f) X = refl-htpy
htpy-hom-system'.slice (refl-htpy-hom-system f) X =
  refl-htpy-hom-system (hom-system.slice f X)

--------------------------------------------------------------------------------

{- Dependent type theories are systems equipped with weakening and substitution
   structure, and with the structure of generic elements (the variable rule). 
-}

--------------------------------------------------------------------------------

-- We introduce weakening structure on systems

record weakening {l1 l2 : Level} (A : system l1 l2) : UU (lsuc l1 ⊔ lsuc l2)
  where
  coinductive
  field
    type  : (X : system.type A) → hom-system A (system.slice A X)
    slice : (X : system.type A) → weakening (system.slice A X)

-- We state what it means for a morphism to preserve weakening structure

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

-- We state what it means for a morphism to preserve substitution structure

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

{- In a dependent type theory, every weakening morphism and every substitution
   morphism preserve both the weakening and substitution structure, and they
   also preserve generic elements.

   For example, the rule that states that weakening preserves weakening (on
   types) can be displayed as follows:

          Γ ⊢ A type          Γ,Δ ⊢ B type          Γ,Δ,Ε ⊢ C type
   ------------------------------------------------------------------------
    Γ,A,W(A,Δ),W(A,B),W(W(A,B),W(A,E)) ⊢ W(W(A,B),W(A,C))=W(A,W(B,C)) type

   Furthermore, there are laws that state that substitution by a:A cancels 
   weakening by A, that substituting a:A in the generic element of A gives us
   the element a back, and that substituting by the generic element of A cancels
   weakening by A.

   We will now state these laws.
-}

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
                   ( generic-element.type δ X)))
               ( x)
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

closed-type-dtt :
  {l1 l2 : Level} (A : dependent-type-theory l1 l2) → UU l1
closed-type-dtt A = system.type (dependent-type-theory.sys A)

global-element-dtt :
  {l1 l2 : Level} (A : dependent-type-theory l1 l2) → closed-type-dtt A → UU l2
global-element-dtt A = system.element (dependent-type-theory.sys A)

weakening-dtt :
  {l1 l2 : Level} (A : dependent-type-theory l1 l2) (X : closed-type-dtt A) →
  hom-system
    ( dependent-type-theory.sys A)
    ( system.slice (dependent-type-theory.sys A) X)
weakening-dtt A = weakening.type (dependent-type-theory.W A)

--------------------------------------------------------------------------------

-- We introduce the slice of a dependent type theory

slice-dtt :
  {l1 l2 : Level} (A : dependent-type-theory l1 l2)
  (X : system.type (dependent-type-theory.sys A)) →
  dependent-type-theory l1 l2
dependent-type-theory.sys (slice-dtt A X) =
  system.slice (dependent-type-theory.sys A) X
dependent-type-theory.W (slice-dtt A X) =
  weakening.slice (dependent-type-theory.W A) X
dependent-type-theory.S (slice-dtt A X) =
  substitution.slice (dependent-type-theory.S A) X
dependent-type-theory.δ (slice-dtt A X) =
  generic-element.slice (dependent-type-theory.δ A) X
dependent-type-theory.WW (slice-dtt A X) =
  weakening-preserves-weakening.slice (dependent-type-theory.WW A) X
dependent-type-theory.SS (slice-dtt A X) =
  substitution-preserves-substitution.slice (dependent-type-theory.SS A) X
dependent-type-theory.WS (slice-dtt A X) =
  weakening-preserves-substitution.slice (dependent-type-theory.WS A) X
dependent-type-theory.SW (slice-dtt A X) =
  substitution-preserves-weakening.slice (dependent-type-theory.SW A) X
dependent-type-theory.Wδ (slice-dtt A X) =
  weakening-preserves-generic-element.slice (dependent-type-theory.Wδ A) X
dependent-type-theory.Sδ (slice-dtt A X) =
  substitution-preserves-generic-element.slice (dependent-type-theory.Sδ A) X
dependent-type-theory.S!W (slice-dtt A X) =
  substitution-cancels-weakening.slice (dependent-type-theory.S!W A) X
dependent-type-theory.δid (slice-dtt A X) =
  generic-element-is-identity.slice (dependent-type-theory.δid A) X
dependent-type-theory.Sδ! (slice-dtt A X) =
  substitution-by-generic-element.slice (dependent-type-theory.Sδ! A) X

--------------------------------------------------------------------------------

-- We introduce simple type theories

record is-simple-dependent-type-theory 
  {l1 l2 : Level} (A : dependent-type-theory l1 l2) : UU l1
  where
  coinductive
  field
    type  : (X : system.type (dependent-type-theory.sys A)) →
            is-equiv
              ( hom-system.type (weakening.type (dependent-type-theory.W A) X))
    slice : (X : system.type (dependent-type-theory.sys A)) →
            is-simple-dependent-type-theory (slice-dtt A X)

record simple-type-theory (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2)
  where
  field
    dtt : dependent-type-theory l1 l2
    is-simple : is-simple-dependent-type-theory dtt

--------------------------------------------------------------------------------

{- We introduce the condiction that the action on elements of a morphism of
   dependent type theories is an equivalence -}

record is-equiv-on-elements-hom-system
  {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : system l3 l4)
  (h : hom-system A B) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive
  field
    type  : (X : system.type A) → is-equiv (hom-system.element h X)
    slice : (X : system.type A) →
            is-equiv-on-elements-hom-system
              ( system.slice A X)
              ( system.slice B (hom-system.type h X))
              ( hom-system.slice h X)

--------------------------------------------------------------------------------

-- We introduce unary type theories

record unary-type-theory
  {l1 l2 : Level} (A : dependent-type-theory l1 l2) : UU (lsuc l1 ⊔ lsuc l2)
  where
  field
    dtt       : dependent-type-theory l1 l2
    is-simple : is-simple-dependent-type-theory A
    is-unary  : (X Y : system.type (dependent-type-theory.sys A)) →
                is-equiv-on-elements-hom-system
                  ( system.slice (dependent-type-theory.sys A) Y)
                  ( system.slice (system.slice (dependent-type-theory.sys A) X)
                    ( hom-system.type
                      ( weakening.type (dependent-type-theory.W A) X) Y))
                  ( hom-system.slice
                    ( weakening.type (dependent-type-theory.W A) X)
                    ( Y))

--------------------------------------------------------------------------------

record dependent-system
  {l1 l2 : Level} (l3 l4 : Level) (A : system l1 l2) :
  UU (l1 ⊔ l2 ⊔ (lsuc l3) ⊔ (lsuc l4))
  where
  coinductive
  field
    type    : system.type A → UU l3
    element : (X : system.type A) → type X → system.element A X → UU l4
    slice   : (X : system.type A) → type X →
              dependent-system l3 l4 (system.slice A X)

record section-system
  {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : dependent-system l3 l4 A) :
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive
  field
    type    : (X : system.type A) → dependent-system.type B X
    element : (X : system.type A) (Y : dependent-system.type B X)
              (x : system.element A X) → dependent-system.element B X Y x
    slice   : (X : system.type A) (Y : dependent-system.type B X) →
              section-system (system.slice A X) (dependent-system.slice B X Y)

system-slice-UU : {l : Level} (X : UU l) → system (lsuc l) l
system.type (system-slice-UU {l} X) = X → UU l
system.element (system-slice-UU {l} X) Y = (x : X) → Y x
system.slice (system-slice-UU {l} X) Y = system-slice-UU (Σ X Y)

{-
hom-system-weakening-system-slice-UU :
  {l : Level} (X : UU l) (Y : X → UU l) →
  hom-system (system-slice-UU X) (system-slice-UU (Σ X Y))
hom-system.type (hom-system-weakening-system-slice-UU X Y) Z (pair x y) =
  Z x
hom-system.element (hom-system-weakening-system-slice-UU X Y) Z g (pair x y) =
  g x
hom-system.type (hom-system.slice (hom-system-weakening-system-slice-UU X Y) Z) W (pair (pair x y) z) = W (pair x z)
hom-system.element (hom-system.slice (hom-system-weakening-system-slice-UU X Y) Z) W h (pair (pair x y) z) = h (pair x z)
hom-system.slice (hom-system.slice (hom-system-weakening-system-slice-UU X Y) Z) W = {!hom-system.slice (hom-system-weakening-system-slice-UU X Y) ?!}

weakening-system-slice-UU :
  {l : Level} (X : UU l) → weakening (system-slice-UU X)
weakening.type (weakening-system-slice-UU X) Y =
  hom-system-weakening-system-slice-UU X Y
weakening.slice (weakening-system-slice-UU X) = {!!}

system-UU : (l : Level) → system (lsuc l) l
system.type (system-UU l) = UU l
system.element (system-UU l) X = X
system.slice (system-UU l) X = system-slice-UU X

weakening-type-UU :
  {l : Level} (X : UU l) →
  hom-system (system-UU l) (system.slice (system-UU l) X)
hom-system.type (weakening-type-UU X) Y x = Y
hom-system.element (weakening-type-UU X) Y y x = y
hom-system.slice (weakening-type-UU X) Y = {!!}

weakening-UU : (l : Level) → weakening (system-UU l)
hom-system.type (weakening.type (weakening-UU l) X) Y x = Y
hom-system.element (weakening.type (weakening-UU l) X) Y y x = y
hom-system.type (hom-system.slice (weakening.type (weakening-UU l) X) Y) Z t =
  Z (pr2 t)
hom-system.element
  ( hom-system.slice (weakening.type (weakening-UU l) X) Y) Z f t =
  f (pr2 t)
hom-system.slice (hom-system.slice (weakening.type (weakening-UU l) X) Y) Z =
  {!!}
hom-system.type
  ( weakening.type (weakening.slice (weakening-UU l) X) Y) Z (pair x y) =
  Z x
hom-system.element
  ( weakening.type (weakening.slice (weakening-UU l) X) Y) Z f (pair x y) =
  f x
hom-system.slice (weakening.type (weakening.slice (weakening-UU l) X) Y) Z =
  {!!}
weakening.slice (weakening.slice (weakening-UU l) X) Y = weakening.slice (weakening-UU l) (Σ X Y)
-}

--------------------------------------------------------------------------------

-- We introduce morphisms of dependent type theories

record hom-dtt
  {l1 l2 l3 l4 : Level} (A : dependent-type-theory l1 l2)
  (B : dependent-type-theory l3 l4) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  field
    sys : hom-system (dependent-type-theory.sys A) (dependent-type-theory.sys B)
    W   : preserves-weakening
            ( dependent-type-theory.W A)
            ( dependent-type-theory.W B)
            ( sys)
    S   : preserves-substitution
            ( dependent-type-theory.S A)
            ( dependent-type-theory.S B)
            ( sys)
    δ   : preserves-generic-element
            ( dependent-type-theory.W A)
            ( dependent-type-theory.δ A)
            ( dependent-type-theory.W B)
            ( dependent-type-theory.δ B)
            ( sys)
            ( W)

{-
preserves-weakening-id-hom-system :
  {l1 l2 : Level} (A : system l1 l2) (W : weakening A) →
  preserves-weakening W W (id-hom-system A)
preserves-weakening.type (preserves-weakening-id-hom-system A W) X = {!!}
preserves-weakening.slice (preserves-weakening-id-hom-system A W) = {!!}

id-hom-dtt : {l1 l2 : Level} (A : dependent-type-theory l1 l2) → hom-dtt A A
hom-dtt.sys (id-hom-dtt A) = id-hom-system (dependent-type-theory.sys A)
hom-dtt.W (id-hom-dtt A) = {!!}
hom-dtt.S (id-hom-dtt A) = {!!}
hom-dtt.δ (id-hom-dtt A) = {!!}
-}

--------------------------------------------------------------------------------

-- We define what it means for a dependent type theory to have Π-types

record function-types
  {l1 l2 : Level} (A : dependent-type-theory l1 l2) : UU (l1 ⊔ l2)
  where
  coinductive
  field
    sys   : (X : system.type (dependent-type-theory.sys A)) →
            hom-dtt (slice-dtt A X) A
    app   : (X : system.type (dependent-type-theory.sys A)) →
            is-equiv-on-elements-hom-system
              ( dependent-type-theory.sys (slice-dtt A X))
              ( dependent-type-theory.sys A)
              ( hom-dtt.sys (sys X))
    slice : (X : system.type (dependent-type-theory.sys A)) →
            function-types (slice-dtt A X)

{-
record preserves-function-types
  {l1 l2 l3 l4 : Level} {A : dependent-type-theory l1 l2}
  {B : dependent-type-theory l3 l4} (ΠA : function-types A)
  (ΠB : function-types B) (h : hom-dtt A B) : UU {!!}
  where
  coinductive
  field
    sys   : {!!}
    slice : {!!}
-}

--------------------------------------------------------------------------------

record natural-numbers
  {l1 l2 : Level} (A : dependent-type-theory l1 l2) (Π : function-types A) :
  UU (l1 ⊔ l2)
  where
    field
      N    : closed-type-dtt A
      zero : global-element-dtt A N
      succ : global-element-dtt A
               ( hom-system.type
                 ( hom-dtt.sys (function-types.sys Π N))
                 ( hom-system.type
                   ( weakening.type (dependent-type-theory.W A) N)
                   ( N)))

{-
natural-numbers-slice :
  {l1 l2 : Level} (A : dependent-type-theory l1 l2) (Π : function-types A)
  (N : natural-numbers A Π) (X : closed-type-dtt A) →
  natural-numbers (slice-dtt A X) (function-types.slice Π X)
natural-numbers.N (natural-numbers-slice A Π N X) =
  hom-system.type
    ( weakening.type (dependent-type-theory.W A) X)
    ( natural-numbers.N N)
natural-numbers.zero (natural-numbers-slice A Π N X) =
  hom-system.element
    ( weakening.type (dependent-type-theory.W A) X)
    ( natural-numbers.N N)
    ( natural-numbers.zero N)
natural-numbers.succ (natural-numbers-slice A Π N X) =
  tr ( system.element (dependent-type-theory.sys (slice-dtt A X)))
     {! (htpy-hom-system.type (preserves-weakening.type (hom-dtt.W (function-types.sys Π (natural-numbers.N N))) ?) ?)!}
{-
  Id ( hom-system.type 
       ( weakening.type (dependent-type-theory.W A) X)
       ( hom-system.type
         ( hom-dtt.sys (function-types.sys Π (natural-numbers.N N)))
         ( hom-system.type
           ( weakening.type (dependent-type-theory.W A) (natural-numbers.N N))
           (natural-numbers.N N))))
     ( hom-system.type
       ( hom-dtt.sys
         ( function-types.sys (function-types.slice Π X)
           ( natural-numbers.N (natural-numbers-slice A Π N X))))
       ( hom-system.type
         ( weakening.type 
           ( dependent-type-theory.W (slice-dtt A X))
           ( natural-numbers.N (natural-numbers-slice A Π N X)))
         ( natural-numbers.N (natural-numbers-slice A Π N X))))
-}
     ( hom-system.element
       ( weakening.type (dependent-type-theory.W A) X)
       ( hom-system.type
         ( hom-dtt.sys (function-types.sys Π (natural-numbers.N N)))
         ( hom-system.type
           ( weakening.type (dependent-type-theory.W A) (natural-numbers.N N))
           ( natural-numbers.N N)))
       ( natural-numbers.succ N))
-}

--------------------------------------------------------------------------------

{-

concat-htpy-hom-system' :
  {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' B'' : system l3 l4}
  (p : Id B B') (q : Id B' B'') {f : hom-system A B} {g : hom-system A B'}
  {h : hom-system A B''} → htpy-hom-system' p f g → htpy-hom-system' q g h →
  htpy-hom-system' (p ∙ q) f h
htpy-hom-system'.type (concat-htpy-hom-system' refl refl H K) =
  htpy-hom-system'.type H ∙h htpy-hom-system'.type K
htpy-hom-system'.element
  ( concat-htpy-hom-system' {A = A} {B} {.B} refl refl {f} H K) X x =
  ( ( tr-concat
      ( htpy-hom-system.type H X)
      ( htpy-hom-system.type K X)
      ( hom-system.element (tr (hom-system A) refl f) X x)) ∙
    ( ap
      ( tr (system.element B) (htpy-hom-system.type K X))
      ( htpy-hom-system.element H X x))) ∙
  ( htpy-hom-system.element K X x)
htpy-hom-system'.slice (concat-htpy-hom-system' p q H K) = {!!}

concat-htpy-hom-system :
  {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
  {f g h : hom-system A B} (H : htpy-hom-system f g)
  (K : htpy-hom-system g h) → htpy-hom-system f h
htpy-hom-system'.type (concat-htpy-hom-system H K) =
  htpy-hom-system.type H ∙h htpy-hom-system.type K
htpy-hom-system'.element (concat-htpy-hom-system {A = A} {B = B} {f} H K) X x =
  ( ( tr-concat
      ( htpy-hom-system.type H X)
      ( htpy-hom-system.type K X)
      ( hom-system.element (tr (hom-system A) refl f) X x)) ∙
    ( ap
      ( tr (system.element B) (htpy-hom-system.type K X))
      ( htpy-hom-system.element H X x))) ∙
  ( htpy-hom-system.element K X x)
htpy-hom-system'.slice (concat-htpy-hom-system H K) X = {!!}
-}
