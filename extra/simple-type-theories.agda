{-# OPTIONS --without-K --exact-split #-}

module extra.simple-type-theories where

open import book public

module simple where
  
  record system
    {l1 : Level} (l2 : Level) (A : UU l1) : UU (l1 ⊔ lsuc l2)
    where
    coinductive
    field
      element : A → UU l2
      slice   : (X : A) → system l2 A
  
  record hom-system
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f : A → B)
    (σ : system l3 A) (T : system l4 B) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      element : (X : A) → system.element σ X → system.element T (f X)
      slice   : (X : A) → hom-system f (system.slice σ X) (system.slice T (f X))
  
  id-hom-system :
    {l1 l2 : Level} {A : UU l1} (σ : system l2 A) → hom-system id σ σ
  hom-system.element (id-hom-system σ) X = id
  hom-system.slice (id-hom-system σ) X = id-hom-system (system.slice σ X)
  
  comp-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {g : B → C}
    {f : A → B} {σ : system l4 A} {τ : system l5 B} {υ : system l6 C}
    (β : hom-system g τ υ) (α : hom-system f σ τ) → hom-system (g ∘ f) σ υ
  hom-system.element (comp-hom-system {f = f} β α) X =
    hom-system.element β (f X) ∘ hom-system.element α X
  hom-system.slice (comp-hom-system {f = f} β α) X =
    comp-hom-system (hom-system.slice β (f X)) (hom-system.slice α X)
  
  record htpy-hom-system
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {f : A → B}
    {σ : system l3 A} {τ : system l4 B} (g h : hom-system f σ τ) :
    UU (l1 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      element : (X : A) → hom-system.element g X ~ hom-system.element h X
      slice   : (X : A) →
                htpy-hom-system (hom-system.slice g X) (hom-system.slice h X)
  
  record weakening
    {l1 l2 : Level} {A : UU l1} (σ : system l2 A) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : (X : A) → hom-system id σ (system.slice σ X)
      slice   : (X : A) → weakening (system.slice σ X)
  
  record preserves-weakening
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {f : A → B}
    {σ : system l3 A} {τ : system l4 B} (Wσ : weakening σ) (Wτ : weakening τ)
    (h : hom-system f σ τ) : UU (l1 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      element : (X : A) →
                htpy-hom-system
                  ( comp-hom-system
                    ( hom-system.slice h X)
                    ( weakening.element Wσ X))
                  ( comp-hom-system
                    ( weakening.element Wτ (f X))
                    ( h))
      slice   : (X : A) →
                preserves-weakening
                  ( weakening.slice Wσ X)
                  ( weakening.slice Wτ (f X))
                  ( hom-system.slice h X)
  
  record substitution
    {l1 l2 : Level} {A : UU l1} (σ : system l2 A) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : (X : A) (x : system.element σ X) →
                hom-system id (system.slice σ X) σ
      slice   : (X : A) → substitution (system.slice σ X)
  
  record preserves-substitution
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {f : A → B} {σ : system l3 A}
    {τ : system l4 B} (Sσ : substitution σ) (Sτ : substitution τ)
    (h : hom-system f σ τ) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      element : (X : A) (x : system.element σ X) →
                htpy-hom-system
                  ( comp-hom-system
                    ( h)
                    ( substitution.element Sσ X x))
                  ( comp-hom-system
                    ( substitution.element Sτ
                      ( f X)
                      ( hom-system.element h X x))
                    ( hom-system.slice h X))
      slice   : (X : A) →
                preserves-substitution
                  ( substitution.slice Sσ X)
                  ( substitution.slice Sτ (f X))
                  ( hom-system.slice h X)
  
  record generic-element
    {l1 l2 : Level} {A : UU l1} (σ : system l2 A) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : (X : A) → system.element (system.slice σ X) X
      slice   : (X : A) → generic-element (system.slice σ X)
  
  record preserves-generic-element
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {f : A → B}
    {σ : system l3 A} {τ : system l4 B} (δσ : generic-element σ)
    (δτ : generic-element τ) (h : hom-system f σ τ) : UU (l1 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      element : (X : A) →
                Id ( hom-system.element
                     ( hom-system.slice h X)
                     ( X)
                     ( generic-element.element δσ X))
                   ( generic-element.element δτ (f X))
      slice   : (X : A) →
                preserves-generic-element
                  ( generic-element.slice δσ X)
                  ( generic-element.slice δτ (f X))
                  ( hom-system.slice h X)
  
  record weakening-preserves-weakening
    {l1 l2 : Level} {A : UU l1} {σ : system l2 A} (W : weakening σ) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : (X : A) →
                preserves-weakening
                  ( W)
                  ( weakening.slice W X)
                  ( weakening.element W X)
      slice   : (X : A) → weakening-preserves-weakening (weakening.slice W  X)
  
  record substitution-preserves-substitution
    {l1 l2 : Level} {A : UU l1} {σ : system l2 A} (S : substitution σ) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : (X : A) (x : system.element σ X) →
                preserves-substitution
                  ( substitution.slice S X)
                  ( S)
                  ( substitution.element S X x)
      slice   : (X : A) →
                substitution-preserves-substitution (substitution.slice S X)
  
  record weakening-preserves-substitution
    {l1 l2 : Level} {A : UU l1} {σ : system l2 A} (W : weakening σ)
    (S : substitution σ) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : (X : A) →
                preserves-substitution
                  ( S)
                  ( substitution.slice S X)
                  ( weakening.element W X)
      slice   : (X : A) →
                weakening-preserves-substitution
                  ( weakening.slice W X)
                  ( substitution.slice S X)
  
  record substitution-preserves-weakening
    {l1 l2 : Level} {A : UU l1} {σ : system l2 A} (W : weakening σ)
    (S : substitution σ) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : (X : A) (x : system.element σ X) →
                preserves-weakening
                  ( weakening.slice W X)
                  ( W)
                  ( substitution.element S X x)
      slice   : (X : A) →
                substitution-preserves-weakening
                  ( weakening.slice W X)
                  ( substitution.slice S X)
  
  record weakening-preserves-generic-element
    {l1 l2 : Level} {A : UU l1} {σ : system l2 A} (W : weakening σ)
    (δ : generic-element σ) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : (X : A) →
                preserves-generic-element
                  ( δ)
                  ( generic-element.slice δ X)
                  ( weakening.element W X)
      slice   : (X : A) →
                weakening-preserves-generic-element
                  ( weakening.slice W X)
                  ( generic-element.slice δ X)
  
  record substitution-preserves-generic-element
    {l1 l2 : Level} {A : UU l1} {σ : system l2 A} (S : substitution σ)
    (δ : generic-element σ) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : (X : A) (x : system.element σ X) →
                preserves-generic-element
                  ( generic-element.slice δ X)
                  ( δ)
                  ( substitution.element S X x)
      slice   : (X : A) →
                substitution-preserves-generic-element
                  ( substitution.slice S X)
                  ( generic-element.slice δ X)
  
  record substitution-cancels-weakening
    {l1 l2 : Level} {A : UU l1} {σ : system l2 A} (W : weakening σ)
    (S : substitution σ) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : (X : A) (x : system.element σ X) →
                htpy-hom-system
                  ( comp-hom-system
                    ( substitution.element S X x)
                    ( weakening.element W X))
                  ( id-hom-system σ)
      slice   : (X : A) →
                substitution-cancels-weakening
                  ( weakening.slice W X)
                  ( substitution.slice S X)
  
  record generic-element-is-identity
    {l1 l2 : Level} {A : UU l1} {σ : system l2 A} (S : substitution σ)
    (δ : generic-element σ) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : (X : A) (x : system.element σ X) →
                Id ( hom-system.element
                     ( substitution.element S X x)
                     ( X)
                     ( generic-element.element δ X))
                   ( x)
      slice   : (X : A) →
                generic-element-is-identity
                  ( substitution.slice S X)
                  ( generic-element.slice δ X)
  
  record substitution-by-generic-element
    {l1 l2 : Level} {A : UU l1} {σ : system l2 A} (W : weakening σ)
    (S : substitution σ) (δ : generic-element σ) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : (X : A) →
                htpy-hom-system
                  ( comp-hom-system
                    ( substitution.element
                      ( substitution.slice S X)
                      ( X)
                      ( generic-element.element δ X))
                    ( weakening.element (weakening.slice W X) X))
                  ( id-hom-system (system.slice σ X))
      slice   : (X : A) →
                substitution-by-generic-element
                  ( weakening.slice W X)
                  ( substitution.slice S X)
                  ( generic-element.slice δ X)
  
  record simple-type-theory
    (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc  l2)
    where
    field
      typ : UU l1
      sys : system l2 typ
      W   : weakening sys
      S   : substitution sys
      δ   : generic-element sys
      WW  : weakening-preserves-weakening W
      SS  : substitution-preserves-substitution S
      WS  : weakening-preserves-substitution W S
      SW  : substitution-preserves-weakening W S
      Wδ  : weakening-preserves-generic-element W δ
      Sδ  : substitution-preserves-generic-element S δ
      S!W : substitution-cancels-weakening W S
      δid : generic-element-is-identity S δ
      Sδ! : substitution-by-generic-element W S δ

  slice-simple-type-theory :
    {l1 l2 : Level} (T : simple-type-theory l1 l2)
    (X : simple-type-theory.typ T) →
    simple-type-theory l1 l2
  simple-type-theory.typ (slice-simple-type-theory T X) =
    simple-type-theory.typ T
  simple-type-theory.sys (slice-simple-type-theory T X) =
    system.slice (simple-type-theory.sys T) X
  simple-type-theory.W (slice-simple-type-theory T X) =
    weakening.slice (simple-type-theory.W T) X
  simple-type-theory.S (slice-simple-type-theory T X) =
    substitution.slice (simple-type-theory.S T) X
  simple-type-theory.δ (slice-simple-type-theory T X) =
    generic-element.slice (simple-type-theory.δ T) X
  simple-type-theory.WW (slice-simple-type-theory T X) =
    weakening-preserves-weakening.slice (simple-type-theory.WW T) X
  simple-type-theory.SS (slice-simple-type-theory T X) =
    substitution-preserves-substitution.slice (simple-type-theory.SS T) X
  simple-type-theory.WS (slice-simple-type-theory T X) =
    weakening-preserves-substitution.slice (simple-type-theory.WS T) X
  simple-type-theory.SW (slice-simple-type-theory T X) =
    substitution-preserves-weakening.slice (simple-type-theory.SW T) X
  simple-type-theory.Wδ (slice-simple-type-theory T X) =
    weakening-preserves-generic-element.slice (simple-type-theory.Wδ T) X
  simple-type-theory.Sδ (slice-simple-type-theory T X) =
    substitution-preserves-generic-element.slice (simple-type-theory.Sδ T) X
  simple-type-theory.S!W (slice-simple-type-theory T X) =
    substitution-cancels-weakening.slice (simple-type-theory.S!W T) X
  simple-type-theory.δid (slice-simple-type-theory T X) =
    generic-element-is-identity.slice (simple-type-theory.δid T) X
  simple-type-theory.Sδ! (slice-simple-type-theory T X) =
    substitution-by-generic-element.slice (simple-type-theory.Sδ! T) X

open import extra.b-systems

module dependent-simple
  where

  system-simple-system :
    {l1 l2 : Level} {A : UU l1} → simple.system l2 A → system l1 l2
  system.type (system-simple-system {A = A} σ) = A
  system.element (system-simple-system σ) X = simple.system.element σ X
  system.slice (system-simple-system σ) X =
    system-simple-system (simple.system.slice σ X)

  hom-simple-hom-system :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l3} {f : A → B}
    {σ : simple.system l2 A} {τ : simple.system l4 B} →
    simple.hom-system f σ τ →
    hom-system (system-simple-system σ) (system-simple-system τ)
  hom-system.type (hom-simple-hom-system {f = f} h) = f
  hom-system.element (hom-simple-hom-system h) X =
    simple.hom-system.element h X
  hom-system.slice (hom-simple-hom-system h) X =
    hom-simple-hom-system (simple.hom-system.slice h X)

  weakening-simple-weakening :
    {l1 l2 : Level} {A : UU l1} {σ : simple.system l2 A}
    (W : simple.weakening σ) → weakening (system-simple-system σ)
  weakening.type (weakening-simple-weakening W) X =
    hom-simple-hom-system (simple.weakening.element W X)
  weakening.slice (weakening-simple-weakening W) X =
    weakening-simple-weakening (simple.weakening.slice W X)
