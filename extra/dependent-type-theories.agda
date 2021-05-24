{-# OPTIONS --without-K --exact-split #-}

module extra.dependent-type-theories where

import book
open book public

module dependent where
  
  ------------------------------------------------------------------------------
  
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

  record fibered-system
    {l1 l2 : Level} (l3 l4 : Level) (A : system l1 l2) :
    UU (l1 ⊔ l2 ⊔ (lsuc l3) ⊔ (lsuc l4))
    where
    coinductive
    field
      type    : system.type A → UU l3
      element : (X : system.type A) → type X → system.element A X → UU l4
      slice   : (X : system.type A) → type X →
                fibered-system l3 l4 (system.slice A X)

  record section-system
    {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : fibered-system l3 l4 A) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type    : (X : system.type A) → fibered-system.type B X
      element : (X : system.type A) (x : system.element A X) →
                fibered-system.element B X (type X) x
      slice   : (X : system.type A) →
                section-system
                  ( system.slice A X)
                  ( fibered-system.slice B X (type X))

  ------------------------------------------------------------------------------

  -- We introduce homotopies of sections of fibered systems

  tr-fibered-system-slice :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' : fibered-system l3 l4 A}
    (α : Id B B') (f : section-system A B) (X : system.type A) →
    Id ( fibered-system.slice B X (section-system.type f X))
       ( fibered-system.slice B' X
         ( section-system.type (tr (section-system A) α f) X))
  tr-fibered-system-slice refl f X = refl

  Eq-fibered-system' :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' : fibered-system l3 l4 A}
    (α : Id B B') (f : section-system A B) (g : section-system A B') →
    fibered-system l3 l4 A
  fibered-system.type (Eq-fibered-system' {A = A} α f g) X =
    Id ( section-system.type (tr (section-system A) α f) X)
       ( section-system.type g X)
  fibered-system.element (Eq-fibered-system' {A = A} {B} {B'} α f g) X p x =
    Id ( tr (λ t → fibered-system.element B' X t x)
            ( p)
            ( section-system.element (tr (section-system A) α f) X x))
       ( section-system.element g X x)
  fibered-system.slice (Eq-fibered-system' {A = A} {B} {B'} α f g) X p =
    Eq-fibered-system'
      ( tr-fibered-system-slice α f X ∙ ap (fibered-system.slice B' X) p)
      ( section-system.slice f X)
      ( section-system.slice g X)

  htpy-section-system' :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' : fibered-system l3 l4 A}
    (α : Id B B') (f : section-system A B) (g : section-system A B') →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-section-system' {A = A} α f g =
    section-system A (Eq-fibered-system' α f g)

  concat-htpy-section-system' :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' B'' : fibered-system l3 l4 A}
    {α : Id B B'} {β : Id B' B''} (γ : Id B B'') (δ : Id (α ∙ β) γ)
    {f : section-system A B} {g : section-system A B'}
    {h : section-system A B''}
    (G : htpy-section-system' α f g) (H : htpy-section-system' β g h) →
    htpy-section-system' γ f h
  section-system.type
    ( concat-htpy-section-system' {α = refl} {refl} refl refl G H) =
    section-system.type G ∙h section-system.type H
  section-system.element
    ( concat-htpy-section-system'
      {B = B} {α = refl} {refl} refl refl {f} G H) X x =
    ( tr-concat
      ( section-system.type G X)
      ( section-system.type H X)
      ( section-system.element f X x)) ∙
    ( ( ap ( tr ( λ t → fibered-system.element B X t x)
                ( section-system.type H X))
           ( section-system.element G X x)) ∙
      ( section-system.element H X x))
  section-system.slice
    ( concat-htpy-section-system' {B = B} {α = refl} {refl} refl refl G H) X =
    concat-htpy-section-system'
      ( ap ( fibered-system.slice B X)
           ( section-system.type G X ∙ section-system.type H X))
      ( inv
        ( ap-concat
          ( fibered-system.slice B X)
          ( section-system.type G X)
          ( section-system.type H X)))
      ( section-system.slice G X)
      ( section-system.slice H X)

  Eq-fibered-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
    (f g : section-system A B) → fibered-system l3 l4 A
  fibered-system.type (Eq-fibered-system f g) X =
    Id (section-system.type f X) (section-system.type g X)
  fibered-system.element (Eq-fibered-system {B = B} f g) X p x =
    Id ( tr (λ t → fibered-system.element B X t x)
            ( p)
            ( section-system.element f X x))
       ( section-system.element g X x)
  fibered-system.slice (Eq-fibered-system {A = A} {B} f g) X p =
    Eq-fibered-system
      ( tr ( λ t →
             section-system (system.slice A X) (fibered-system.slice B X t))
           ( p)
           ( section-system.slice f X))
      ( section-system.slice g X)

  htpy-section-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
    (f g : section-system A B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-section-system {A = A} {B} f g =
    htpy-section-system' refl f g

  refl-htpy-section-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
    (f : section-system A B) → htpy-section-system f f
  section-system.type (refl-htpy-section-system f) X = refl
  section-system.element (refl-htpy-section-system f) X x = refl
  section-system.slice (refl-htpy-section-system f) X =
    refl-htpy-section-system (section-system.slice f X)

  concat-htpy-section-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
    {f g h : section-system A B} (G : htpy-section-system f g)
    (H : htpy-section-system g h) → htpy-section-system f h
  concat-htpy-section-system G H =
    concat-htpy-section-system' refl refl G H

  ------------------------------------------------------------------------------

  -- We introduce the total system of a fibered dependency system

  total-system :
    {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : fibered-system l3 l4 A) →
    system (l1 ⊔ l3) (l2 ⊔ l4)
  system.type (total-system A B) =
    Σ (system.type A) (fibered-system.type B)
  system.element (total-system A B) (pair X Y) =
    Σ (system.element A X) (fibered-system.element B X Y)
  system.slice (total-system A B) (pair X Y) =
    total-system (system.slice A X) (fibered-system.slice B X Y)

  ------------------------------------------------------------------------------

  -- We introduce morphisms of systems

  constant-fibered-system :
    {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : system l3 l4) →
    fibered-system l3 l4 A
  fibered-system.type (constant-fibered-system A B) X = system.type B
  fibered-system.element (constant-fibered-system A B) X Y x =
    system.element B Y
  fibered-system.slice (constant-fibered-system A B) X Y =
    constant-fibered-system (system.slice A X) (system.slice B Y)
  
  hom-system :
    {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : system l3 l4) → 
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-system A B =
    section-system A (constant-fibered-system A B)

  ------------------------------------------------------------------------------

  {- Homotopies of morphisms of systems are defined as an instance of
     homotopies of sections of fibered systems
  -}
  
  htpy-hom-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    (f g : hom-system A B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-system f g = htpy-section-system f g
  
  module htpy-hom-system
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    {f g : hom-system A B}
    where
    
    type : htpy-hom-system f g →
           section-system.type f ~ section-system.type g
    type H = section-system.type H

    element : (H : htpy-hom-system f g) →
              (X : system.type A) (x : system.element A X) →
            Id ( tr (system.element B) (type H X) (section-system.element f X x))
                 ( section-system.element g X x)
    element H = section-system.element H

  refl-htpy-hom-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    (f : hom-system A B) → htpy-hom-system f f
  refl-htpy-hom-system f = refl-htpy-section-system f

  ------------------------------------------------------------------------------

  -- We show that systems form a category

  id-hom-system :
    {l1 l2 : Level} (A : system l1 l2) → hom-system A A
  section-system.type (id-hom-system A) X = X
  section-system.element (id-hom-system A) X x = x
  section-system.slice (id-hom-system A) X = id-hom-system (system.slice A X)
  
  comp-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level}
    {A : system l1 l2} {B : system l3 l4} {C : system l5 l6}
    (g : hom-system B C) (f : hom-system A B) → hom-system A C
  section-system.type (comp-hom-system g f) =
    section-system.type g ∘ section-system.type f
  section-system.element (comp-hom-system g f) X =
    section-system.element g (section-system.type f X) ∘ section-system.element f X
  section-system.slice (comp-hom-system g f) X =
    comp-hom-system
      ( section-system.slice g (section-system.type f X))
      ( section-system.slice f X)

  ------------------------------------------------------------------------------

  -- Morphisms of fibered systems

  record hom-fibered-system
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2} {A' : system l3 l4}
    (f : hom-system A A') (B : fibered-system l5 l6 A)
    (B' : fibered-system l7 l8 A') : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8)
    where
    coinductive
    field
      type    : (X : system.type A) → fibered-system.type B X →
                fibered-system.type B' (section-system.type f X)
      element : (X : system.type A) (x : system.element A X) →
                (Y : fibered-system.type B X) →
                fibered-system.element B X Y x →
                fibered-system.element B'
                  ( section-system.type f X)
                  ( type X Y)
                  ( section-system.element f X x)
      slice   : (X : system.type A) (Y : fibered-system.type B X) →
                hom-fibered-system
                  ( section-system.slice f X)
                  ( fibered-system.slice B X Y)
                  ( fibered-system.slice B'
                    ( section-system.type f X)
                    ( type X Y))
  
  ------------------------------------------------------------------------------
  
  {- Dependent type theories are systems equipped with weakening and 
     substitution structure, and with the structure of generic elements (the 
     variable rule). 
  -}
  
  ------------------------------------------------------------------------------
  
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
                  ( section-system.slice h X)
                  ( weakening.type WA X))
                ( comp-hom-system
                  ( weakening.type WB (section-system.type h X))
                  ( h))
      slice : (X : system.type A) →
              preserves-weakening
                ( weakening.slice WA X)
                ( weakening.slice WB (section-system.type h X))
                ( section-system.slice h X)
  
  ------------------------------------------------------------------------------
  
  -- We introduce substitution structure on a system
  
  record substitution {l1 l2 : Level} (A : system l1 l2) :
    UU (lsuc l1 ⊔ lsuc l2)
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
                    ( section-system.type h X)
                    ( section-system.element h X x))
                  ( section-system.slice h X))
      slice : (X : system.type A) →
              preserves-substitution
                ( substitution.slice SA X)
                ( substitution.slice SB (section-system.type h X))
                ( section-system.slice h X)

  ------------------------------------------------------------------------------

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
                  ( section-system.type (weakening.type W X) X)
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
                   ( system.element (system.slice B (section-system.type h X)))
                   ( htpy-hom-system.type
                     ( preserves-weakening.type Wh X)
                     ( X))
                   ( section-system.element
                     ( section-system.slice h X)
                     ( section-system.type (weakening.type WA X) X)
                     ( generic-element.type δA X)))
                 ( generic-element.type δB (section-system.type h X))
      slice : (X : system.type A) →
              preserves-generic-element
                ( weakening.slice WA X)
                ( generic-element.slice δA X)
                ( weakening.slice WB (section-system.type h X))
                ( generic-element.slice δB (section-system.type h X))
                ( section-system.slice h X)
                ( preserves-weakening.slice Wh X)

  ------------------------------------------------------------------------------

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
     the element a back, and that substituting by the generic element of A 
     cancels weakening by A.

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
                   ( section-system.element
                     ( substitution.type S X x)
                     ( section-system.type (weakening.type W X) X)
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
                    ( section-system.type (weakening.type W X) X)
                    ( generic-element.type δ X))
                  ( weakening.type
                    ( weakening.slice W X)
                    ( section-system.type (weakening.type W X) X)))
                ( id-hom-system (system.slice A X))
      slice : (X : system.type A) →
              substitution-by-generic-element
                ( system.slice A X)
                ( weakening.slice W X)
                ( substitution.slice S X)
                ( generic-element.slice δ X)
  
  ------------------------------------------------------------------------------

  -- We complete the definition of a dependent type theory
  
  record type-theory
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
    {l1 l2 : Level} (A : type-theory l1 l2) → UU l1
  closed-type-dtt A = system.type (type-theory.sys A)
  
  global-element-dtt :
    {l1 l2 : Level} (A : type-theory l1 l2) → closed-type-dtt A →
    UU l2
  global-element-dtt A = system.element (type-theory.sys A)
  
  weakening-dtt :
    {l1 l2 : Level} (A : type-theory l1 l2) (X : closed-type-dtt A) →
    hom-system
      ( type-theory.sys A)
      ( system.slice (type-theory.sys A) X)
  weakening-dtt A = weakening.type (type-theory.W A)

  ------------------------------------------------------------------------------

  -- We introduce the slice of a dependent type theory
  
  slice-dtt :
    {l1 l2 : Level} (A : type-theory l1 l2)
    (X : system.type (type-theory.sys A)) →
    type-theory l1 l2
  type-theory.sys (slice-dtt A X) =
    system.slice (type-theory.sys A) X
  type-theory.W (slice-dtt A X) =
    weakening.slice (type-theory.W A) X
  type-theory.S (slice-dtt A X) =
    substitution.slice (type-theory.S A) X
  type-theory.δ (slice-dtt A X) =
    generic-element.slice (type-theory.δ A) X
  type-theory.WW (slice-dtt A X) =
    weakening-preserves-weakening.slice (type-theory.WW A) X
  type-theory.SS (slice-dtt A X) =
    substitution-preserves-substitution.slice (type-theory.SS A) X
  type-theory.WS (slice-dtt A X) =
    weakening-preserves-substitution.slice (type-theory.WS A) X
  type-theory.SW (slice-dtt A X) =
    substitution-preserves-weakening.slice (type-theory.SW A) X
  type-theory.Wδ (slice-dtt A X) =
    weakening-preserves-generic-element.slice (type-theory.Wδ A) X
  type-theory.Sδ (slice-dtt A X) =
    substitution-preserves-generic-element.slice (type-theory.Sδ A) X
  type-theory.S!W (slice-dtt A X) =
    substitution-cancels-weakening.slice (type-theory.S!W A) X
  type-theory.δid (slice-dtt A X) =
    generic-element-is-identity.slice (type-theory.δid A) X
  type-theory.Sδ! (slice-dtt A X) =
    substitution-by-generic-element.slice (type-theory.Sδ! A) X

  ------------------------------------------------------------------------------

  -- We introduce simple type theories
  
  record is-simple-type-theory 
    {l1 l2 : Level} (A : type-theory l1 l2) : UU l1
    where
    coinductive
    field
      type  : (X : system.type (type-theory.sys A)) →
              is-equiv
                ( section-system.type
                  ( weakening.type (type-theory.W A) X))
      slice : (X : system.type (type-theory.sys A)) →
              is-simple-type-theory (slice-dtt A X)
  
  record simple-type-theory (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2)
    where
    field
      dtt : type-theory l1 l2
      is-simple : is-simple-type-theory dtt

  ------------------------------------------------------------------------------

  {- We introduce the condiction that the action on elements of a morphism of
     dependent type theories is an equivalence -}
  
  record is-equiv-on-elements-hom-system
    {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : system l3 l4)
    (h : hom-system A B) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type  : (X : system.type A) → is-equiv (section-system.element h X)
      slice : (X : system.type A) →
              is-equiv-on-elements-hom-system
                ( system.slice A X)
                ( system.slice B (section-system.type h X))
                ( section-system.slice h X)

  ------------------------------------------------------------------------------

  -- We introduce unary type theories
  
  record unary-type-theory
    {l1 l2 : Level} (A : type-theory l1 l2) : UU (lsuc l1 ⊔ lsuc l2)
    where
    field
      dtt       : type-theory l1 l2
      is-simple : is-simple-type-theory A
      is-unary  : (X Y : system.type (type-theory.sys A)) →
                  is-equiv-on-elements-hom-system
                    ( system.slice (type-theory.sys A) Y)
                    ( system.slice
                      ( system.slice (type-theory.sys A) X)
                      ( section-system.type
                        ( weakening.type (type-theory.W A) X) Y))
                    ( section-system.slice
                      ( weakening.type (type-theory.W A) X)
                      ( Y))

  ------------------------------------------------------------------------------

  system-slice-UU : {l : Level} (X : UU l) → system (lsuc l) l
  system.type (system-slice-UU {l} X) = X → UU l
  system.element (system-slice-UU {l} X) Y = (x : X) → Y x
  system.slice (system-slice-UU {l} X) Y = system-slice-UU (Σ X Y)
  
  {-
  hom-system-weakening-system-slice-UU :
    {l : Level} (X : UU l) (Y : X → UU l) →
    hom-system (system-slice-UU X) (system-slice-UU (Σ X Y))
  section-system.type (hom-system-weakening-system-slice-UU X Y) Z (pair x y) =
    Z x
  section-system.element (hom-system-weakening-system-slice-UU X Y) Z g (pair x y) =
    g x
  section-system.type (section-system.slice (hom-system-weakening-system-slice-UU X Y) Z) W (pair (pair x y) z) = W (pair x z)
  section-system.element (section-system.slice (hom-system-weakening-system-slice-UU X Y) Z) W h (pair (pair x y) z) = h (pair x z)
  section-system.slice (section-system.slice (hom-system-weakening-system-slice-UU X Y) Z) W = {!section-system.slice (hom-system-weakening-system-slice-UU X Y) ?!}

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
  section-system.type (weakening-type-UU X) Y x = Y
  section-system.element (weakening-type-UU X) Y y x = y
  section-system.slice (weakening-type-UU X) Y = {!!}
  
  weakening-UU : (l : Level) → weakening (system-UU l)
  section-system.type (weakening.type (weakening-UU l) X) Y x = Y
  section-system.element (weakening.type (weakening-UU l) X) Y y x = y
  section-system.type (section-system.slice (weakening.type (weakening-UU l) X) Y) Z t =
    Z (pr2 t)
  section-system.element
    ( section-system.slice (weakening.type (weakening-UU l) X) Y) Z f t =
    f (pr2 t)
  section-system.slice (section-system.slice (weakening.type (weakening-UU l) X) Y) Z =
    {!!}
  section-system.type
    ( weakening.type (weakening.slice (weakening-UU l) X) Y) Z (pair x y) =
    Z x
  section-system.element
    ( weakening.type (weakening.slice (weakening-UU l) X) Y) Z f (pair x y) =
    f x
  section-system.slice (weakening.type (weakening.slice (weakening-UU l) X) Y) Z =
    {!!}
  weakening.slice (weakening.slice (weakening-UU l) X) Y = weakening.slice (weakening-UU l) (Σ X Y)
-}

  ------------------------------------------------------------------------------

  -- We introduce morphisms of dependent type theories
  
  record hom-dtt
    {l1 l2 l3 l4 : Level} (A : type-theory l1 l2)
    (B : type-theory l3 l4) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    field
      sys : hom-system
              ( type-theory.sys A)
              ( type-theory.sys B)
      W   : preserves-weakening
              ( type-theory.W A)
              ( type-theory.W B)
              ( sys)
      S   : preserves-substitution
              ( type-theory.S A)
              ( type-theory.S B)
              ( sys)
      δ   : preserves-generic-element
              ( type-theory.W A)
              ( type-theory.δ A)
              ( type-theory.W B)
              ( type-theory.δ B)
              ( sys)
              ( W)

  {-
  preserves-weakening-id-hom-system :
    {l1 l2 : Level} (A : system l1 l2) (W : weakening A) →
    preserves-weakening W W (id-hom-system A)
  preserves-weakening.type (preserves-weakening-id-hom-system A W) X = {!!}
  preserves-weakening.slice (preserves-weakening-id-hom-system A W) = {!!}

  id-hom-dtt : {l1 l2 : Level} (A : type-theory l1 l2) → hom-dtt A A
  hom-dtt.sys (id-hom-dtt A) = id-hom-system (type-theory.sys A)
  hom-dtt.W (id-hom-dtt A) = {!!}
  hom-dtt.S (id-hom-dtt A) = {!!}
  hom-dtt.δ (id-hom-dtt A) = {!!}
  -}

  ------------------------------------------------------------------------------

  -- We define what it means for a dependent type theory to have Π-types
  
  record function-types
    {l1 l2 : Level} (A : type-theory l1 l2) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      sys   : (X : system.type (type-theory.sys A)) →
              hom-dtt (slice-dtt A X) A
      app   : (X : system.type (type-theory.sys A)) →
              is-equiv-on-elements-hom-system
                ( type-theory.sys (slice-dtt A X))
                ( type-theory.sys A)
                ( hom-dtt.sys (sys X))
      slice : (X : system.type (type-theory.sys A)) →
              function-types (slice-dtt A X)

  {-
  record preserves-function-types
    {l1 l2 l3 l4 : Level} {A : type-theory l1 l2}
    {B : type-theory l3 l4} (ΠA : function-types A)
    (ΠB : function-types B) (h : hom-dtt A B) : UU {!!}
    where
    coinductive
    field
      sys   : {!!}
      slice : {!!}
  -}

  ------------------------------------------------------------------------------

  record natural-numbers
    {l1 l2 : Level} (A : type-theory l1 l2) (Π : function-types A) :
    UU (l1 ⊔ l2)
    where
    field
      N    : closed-type-dtt A
      zero : global-element-dtt A N
      succ : global-element-dtt A
               ( section-system.type
                 ( hom-dtt.sys (function-types.sys Π N))
                 ( section-system.type
                   ( weakening.type (type-theory.W A) N)
                   ( N)))

  {-
  natural-numbers-slice :
    {l1 l2 : Level} (A : type-theory l1 l2) (Π : function-types A)
    (N : natural-numbers A Π) (X : closed-type-dtt A) →
    natural-numbers (slice-dtt A X) (function-types.slice Π X)
  natural-numbers.N (natural-numbers-slice A Π N X) =
    section-system.type
      ( weakening.type (type-theory.W A) X)
      ( natural-numbers.N N)
  natural-numbers.zero (natural-numbers-slice A Π N X) =
    section-system.element
      ( weakening.type (type-theory.W A) X)
      ( natural-numbers.N N)
      ( natural-numbers.zero N)
  natural-numbers.succ (natural-numbers-slice A Π N X) =
    tr ( system.element (type-theory.sys (slice-dtt A X)))
       {! (htpy-hom-system.type (preserves-weakening.type (hom-dtt.W (function-types.sys Π (natural-numbers.N N))) ?) ?)!}
    {-
    Id ( section-system.type 
         ( weakening.type (type-theory.W A) X)
         ( section-system.type
           ( hom-dtt.sys (function-types.sys Π (natural-numbers.N N)))
           ( section-system.type
             ( weakening.type (type-theory.W A) (natural-numbers.N N))
             (natural-numbers.N N))))
       ( section-system.type
         ( hom-dtt.sys
           ( function-types.sys (function-types.slice Π X)
             ( natural-numbers.N (natural-numbers-slice A Π N X))))
         ( section-system.type
           ( weakening.type 
             ( type-theory.W (slice-dtt A X))
             ( natural-numbers.N (natural-numbers-slice A Π N X)))
           ( natural-numbers.N (natural-numbers-slice A Π N X))))
  -}
       ( section-system.element
         ( weakening.type (type-theory.W A) X)
         ( section-system.type
           ( hom-dtt.sys (function-types.sys Π (natural-numbers.N N)))
           ( section-system.type
             ( weakening.type (type-theory.W A) (natural-numbers.N N))
             ( natural-numbers.N N)))
         ( natural-numbers.succ N))
  -}

  ------------------------------------------------------------------------------

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
        ( section-system.element (tr (hom-system A) refl f) X x)) ∙
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
        ( section-system.element (tr (hom-system A) refl f) X x)) ∙
      ( ap
        ( tr (system.element B) (htpy-hom-system.type K X))
        ( htpy-hom-system.element H X x))) ∙
    ( htpy-hom-system.element K X x)
  htpy-hom-system'.slice (concat-htpy-hom-system H K) X = {!!}
  -}
