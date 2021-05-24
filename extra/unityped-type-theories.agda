{-# OPTIONS --without-K --exact-split #-}

module extra.unityped-type-theories where

open import book public

module unityped where
  
  record system (l : Level) : UU (lsuc l)
    where
    coinductive
    field
      element : UU l
      slice   : system l
  
  record hom-system
    {l1 l2 : Level} (σ : system l1) (T : system l2) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : system.element σ → system.element T
      slice   : hom-system (system.slice σ) (system.slice T)
  
  id-hom-system :
    {l : Level} (σ : system l) → hom-system σ σ
  hom-system.element (id-hom-system σ) = id
  hom-system.slice (id-hom-system σ) = id-hom-system (system.slice σ)
  
  comp-hom-system :
    {l1 l2 l3 : Level} {σ : system l1} {τ : system l2} {υ : system l3}
    (β : hom-system τ υ) (α : hom-system σ τ) → hom-system σ υ
  hom-system.element (comp-hom-system β α) =
    hom-system.element β ∘ hom-system.element α
  hom-system.slice (comp-hom-system β α) =
    comp-hom-system (hom-system.slice β) (hom-system.slice α)
  
  record htpy-hom-system
    {l1 l2 : Level} {σ : system l1} {τ : system l2} (g h : hom-system σ τ) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : hom-system.element g ~ hom-system.element h
      slice   : htpy-hom-system (hom-system.slice g) (hom-system.slice h)
  
  record weakening
    {l : Level} (σ : system l) : UU l
    where
    coinductive
    field
      element : hom-system σ (system.slice σ)
      slice   : weakening (system.slice σ)
  
  record preserves-weakening
    {l1 l2 : Level} {σ : system l1} {τ : system l2} (Wσ : weakening σ)
    (Wτ : weakening τ) (h : hom-system σ τ) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : htpy-hom-system
                  ( comp-hom-system
                    ( hom-system.slice h)
                    ( weakening.element Wσ))
                  ( comp-hom-system
                    ( weakening.element Wτ)
                    ( h))
      slice   : preserves-weakening
                  ( weakening.slice Wσ)
                  ( weakening.slice Wτ)
                  ( hom-system.slice h)
  
  record substitution
    {l : Level} (σ : system l) : UU l
    where
    coinductive
    field
      element : (x : system.element σ) →
                hom-system (system.slice σ) σ
      slice   : substitution (system.slice σ)
  
  record preserves-substitution
    {l1 l2 : Level} {σ : system l1} {τ : system l2} (Sσ : substitution σ)
    (Sτ : substitution τ) (h : hom-system σ τ) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : (x : system.element σ) →
                htpy-hom-system
                  ( comp-hom-system
                    ( h)
                    ( substitution.element Sσ x))
                  ( comp-hom-system
                    ( substitution.element Sτ
                      ( hom-system.element h x))
                    ( hom-system.slice h))
      slice   : preserves-substitution
                  ( substitution.slice Sσ)
                  ( substitution.slice Sτ)
                  ( hom-system.slice h)
  
  record generic-element
    {l : Level} (σ : system l) : UU l
    where
    coinductive
    field
      element : system.element (system.slice σ)
      slice   : generic-element (system.slice σ)
  
  record preserves-generic-element
    {l1 l2 : Level} {σ : system l1} {τ : system l2} (δσ : generic-element σ)
    (δτ : generic-element τ) (h : hom-system σ τ) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : Id ( hom-system.element
                     ( hom-system.slice h)
                     ( generic-element.element δσ))
                   ( generic-element.element δτ)
      slice   : preserves-generic-element
                  ( generic-element.slice δσ)
                  ( generic-element.slice δτ)
                  ( hom-system.slice h)
  
  record weakening-preserves-weakening
    {l : Level} {σ : system l} (W : weakening σ) : UU l
    where
    coinductive
    field
      element : preserves-weakening
                  ( W)
                  ( weakening.slice W)
                  ( weakening.element W)
      slice   : weakening-preserves-weakening (weakening.slice W)
  
  record substitution-preserves-substitution
    {l : Level} {σ : system l} (S : substitution σ) : UU l
    where
    coinductive
    field
      element : (x : system.element σ) →
                preserves-substitution
                  ( substitution.slice S)
                  ( S)
                  ( substitution.element S x)
      slice   : substitution-preserves-substitution (substitution.slice S)
  
  record weakening-preserves-substitution
    {l : Level} {σ : system l} (W : weakening σ) (S : substitution σ) : UU l
    where
    coinductive
    field
      element : preserves-substitution
                  ( S)
                  ( substitution.slice S)
                  ( weakening.element W)
      slice   : weakening-preserves-substitution
                  ( weakening.slice W)
                  ( substitution.slice S)
  
  record substitution-preserves-weakening
    {l : Level} {σ : system l} (W : weakening σ) (S : substitution σ) : UU l
    where
    coinductive
    field
      element : (x : system.element σ) →
                preserves-weakening
                  ( weakening.slice W)
                  ( W)
                  ( substitution.element S x)
      slice   : substitution-preserves-weakening
                  ( weakening.slice W)
                  ( substitution.slice S)
  
  record weakening-preserves-generic-element
    {l : Level} {σ : system l} (W : weakening σ) (δ : generic-element σ) : UU l
    where
    coinductive
    field
      element : preserves-generic-element
                  ( δ)
                  ( generic-element.slice δ)
                  ( weakening.element W)
      slice   : weakening-preserves-generic-element
                  ( weakening.slice W)
                  ( generic-element.slice δ)
  
  record substitution-preserves-generic-element
    {l : Level} {σ : system l} (S : substitution σ) (δ : generic-element σ) :
    UU l
    where
    coinductive
    field
      element : (x : system.element σ) →
                preserves-generic-element
                  ( generic-element.slice δ)
                  ( δ)
                  ( substitution.element S x)
      slice   : substitution-preserves-generic-element
                  ( substitution.slice S)
                  ( generic-element.slice δ)
  
  record substitution-cancels-weakening
    {l : Level} {σ : system l} (W : weakening σ) (S : substitution σ) : UU l
    where
    coinductive
    field
      element : (x : system.element σ) →
                htpy-hom-system
                  ( comp-hom-system
                    ( substitution.element S x)
                    ( weakening.element W))
                  ( id-hom-system σ)
      slice   : substitution-cancels-weakening
                  ( weakening.slice W)
                  ( substitution.slice S)
  
  record generic-element-is-identity
    {l : Level} {σ : system l} (S : substitution σ) (δ : generic-element σ) :
    UU l
    where
    coinductive
    field
      element : (x : system.element σ) →
                Id ( hom-system.element
                     ( substitution.element S x)
                     ( generic-element.element δ))
                   ( x)
      slice   : generic-element-is-identity
                  ( substitution.slice S)
                  ( generic-element.slice δ)
  
  record substitution-by-generic-element
    {l : Level} {σ : system l} (W : weakening σ) (S : substitution σ)
    (δ : generic-element σ) : UU l
    where
    coinductive
    field
      element : htpy-hom-system
                  ( comp-hom-system
                    ( substitution.element
                      ( substitution.slice S)
                      ( generic-element.element δ))
                    ( weakening.element (weakening.slice W)))
                  ( id-hom-system (system.slice σ))
      slice   : substitution-by-generic-element
                  ( weakening.slice W)
                  ( substitution.slice S)
                  ( generic-element.slice δ)
  
  record type-theory
    (l : Level) : UU (lsuc l)
    where
    field
      sys : system l
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

  slice-type-theory :
    {l : Level} (T : type-theory l) → type-theory l
  type-theory.sys (slice-type-theory T) =
    system.slice (type-theory.sys T)
  type-theory.W (slice-type-theory T) =
    weakening.slice (type-theory.W T)
  type-theory.S (slice-type-theory T) =
    substitution.slice (type-theory.S T)
  type-theory.δ (slice-type-theory T) =
    generic-element.slice (type-theory.δ T)
  type-theory.WW (slice-type-theory T) =
    weakening-preserves-weakening.slice (type-theory.WW T)
  type-theory.SS (slice-type-theory T) =
    substitution-preserves-substitution.slice (type-theory.SS T)
  type-theory.WS (slice-type-theory T ) =
    weakening-preserves-substitution.slice (type-theory.WS T)
  type-theory.SW (slice-type-theory T ) =
    substitution-preserves-weakening.slice (type-theory.SW T)
  type-theory.Wδ (slice-type-theory T ) =
    weakening-preserves-generic-element.slice (type-theory.Wδ T)
  type-theory.Sδ (slice-type-theory T ) =
    substitution-preserves-generic-element.slice (type-theory.Sδ T)
  type-theory.S!W (slice-type-theory T) =
    substitution-cancels-weakening.slice (type-theory.S!W T)
  type-theory.δid (slice-type-theory T) =
    generic-element-is-identity.slice (type-theory.δid T)
  type-theory.Sδ! (slice-type-theory T) =
    substitution-by-generic-element.slice (type-theory.Sδ! T)

record stream (l : Level) : Set (lsuc l)
  where
  coinductive
  field
    type  : Set l
    slice : stream l

total-stream : {l : Level} → stream l → UU l
total-stream A = coprod (stream.type A) (total-stream (stream.slice A))

ℕ-stream : stream lzero
stream.type ℕ-stream = unit
stream.slice ℕ-stream = ℕ-stream
