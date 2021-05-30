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
      element : {X : A} → system.element σ X → system.element T (f X)
      slice   : (X : A) → hom-system f (system.slice σ X) (system.slice T (f X))
  
  id-hom-system :
    {l1 l2 : Level} {A : UU l1} (σ : system l2 A) → hom-system id σ σ
  hom-system.element (id-hom-system σ) {X} = id
  hom-system.slice (id-hom-system σ) X = id-hom-system (system.slice σ X)
  
  comp-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {g : B → C}
    {f : A → B} {σ : system l4 A} {τ : system l5 B} {υ : system l6 C}
    (β : hom-system g τ υ) (α : hom-system f σ τ) → hom-system (g ∘ f) σ υ
  hom-system.element (comp-hom-system {f = f} β α) {X} =
    hom-system.element β {f X} ∘ hom-system.element α {X}
  hom-system.slice (comp-hom-system {f = f} β α) X =
    comp-hom-system (hom-system.slice β (f X)) (hom-system.slice α X)
  
  record htpy-hom-system
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {f : A → B}
    {σ : system l3 A} {τ : system l4 B} (g h : hom-system f σ τ) :
    UU (l1 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      element : (X : A) → hom-system.element g {X} ~ hom-system.element h {X}
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
      element : {X : A} (x : system.element σ X) →
                hom-system id (system.slice σ X) σ
      slice   : (X : A) → substitution (system.slice σ X)
  
  record preserves-substitution
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {f : A → B} {σ : system l3 A}
    {τ : system l4 B} (Sσ : substitution σ) (Sτ : substitution τ)
    (h : hom-system f σ τ) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      element : {X : A} (x : system.element σ X) →
                htpy-hom-system
                  ( comp-hom-system
                    ( h)
                    ( substitution.element Sσ x))
                  ( comp-hom-system
                    ( substitution.element Sτ
                      ( hom-system.element h x))
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
      element : {X : A} (x : system.element σ X) →
                preserves-substitution
                  ( substitution.slice S X)
                  ( S)
                  ( substitution.element S x)
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
      element : {X : A} (x : system.element σ X) →
                preserves-weakening
                  ( weakening.slice W X)
                  ( W)
                  ( substitution.element S x)
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
      element : {X : A} (x : system.element σ X) →
                preserves-generic-element
                  ( generic-element.slice δ X)
                  ( δ)
                  ( substitution.element S x)
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
      element : {X : A} (x : system.element σ X) →
                htpy-hom-system
                  ( comp-hom-system
                    ( substitution.element S x)
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
      element : {X : A} (x : system.element σ X) →
                Id ( hom-system.element
                     ( substitution.element S x)
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
                      ( generic-element.element δ X))
                    ( weakening.element (weakening.slice W X) X))
                  ( id-hom-system (system.slice σ X))
      slice   : (X : A) →
                substitution-by-generic-element
                  ( weakening.slice W X)
                  ( substitution.slice S X)
                  ( generic-element.slice δ X)
  
  record type-theory
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

  slice-type-theory :
    {l1 l2 : Level} (T : type-theory l1 l2)
    (X : type-theory.typ T) →
    type-theory l1 l2
  type-theory.typ (slice-type-theory T X) =
    type-theory.typ T
  type-theory.sys (slice-type-theory T X) =
    system.slice (type-theory.sys T) X
  type-theory.W (slice-type-theory T X) =
    weakening.slice (type-theory.W T) X
  type-theory.S (slice-type-theory T X) =
    substitution.slice (type-theory.S T) X
  type-theory.δ (slice-type-theory T X) =
    generic-element.slice (type-theory.δ T) X
  type-theory.WW (slice-type-theory T X) =
    weakening-preserves-weakening.slice (type-theory.WW T) X
  type-theory.SS (slice-type-theory T X) =
    substitution-preserves-substitution.slice (type-theory.SS T) X
  type-theory.WS (slice-type-theory T X) =
    weakening-preserves-substitution.slice (type-theory.WS T) X
  type-theory.SW (slice-type-theory T X) =
    substitution-preserves-weakening.slice (type-theory.SW T) X
  type-theory.Wδ (slice-type-theory T X) =
    weakening-preserves-generic-element.slice (type-theory.Wδ T) X
  type-theory.Sδ (slice-type-theory T X) =
    substitution-preserves-generic-element.slice (type-theory.Sδ T) X
  type-theory.S!W (slice-type-theory T X) =
    substitution-cancels-weakening.slice (type-theory.S!W T) X
  type-theory.δid (slice-type-theory T X) =
    generic-element-is-identity.slice (type-theory.δid T) X
  type-theory.Sδ! (slice-type-theory T X) =
    substitution-by-generic-element.slice (type-theory.Sδ! T) X

open import extra.dependent-type-theories

dependent-system-simple-system :
  {l1 l2 : Level} {A : UU l1} → simple.system l2 A → dependent.system l1 l2
dependent.system.type (dependent-system-simple-system {A = A} σ) = A
dependent.system.element (dependent-system-simple-system σ) X =
  simple.system.element σ X
dependent.system.slice (dependent-system-simple-system σ) X =
  dependent-system-simple-system (simple.system.slice σ X)
                                              
dependent-hom-system-simple-hom-system :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l3} {f : A → B}
  {σ : simple.system l2 A} {τ : simple.system l4 B} →
  simple.hom-system f σ τ →
  dependent.hom-system
    ( dependent-system-simple-system σ)
    ( dependent-system-simple-system τ)
dependent.section-system.type
  ( dependent-hom-system-simple-hom-system {f = f} h) = f
dependent.section-system.element
  ( dependent-hom-system-simple-hom-system h) =
  simple.hom-system.element h
dependent.section-system.slice (dependent-hom-system-simple-hom-system h) X =
  dependent-hom-system-simple-hom-system (simple.hom-system.slice h X)

comp-dependent-hom-system-simple-hom-system :
  {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B} {σ : simple.system l4 A} {τ : simple.system l5 B}
  {υ : simple.system l6 C} (k : simple.hom-system g τ υ)
  (h : simple.hom-system f σ τ) →
  dependent.htpy-hom-system
    ( dependent-hom-system-simple-hom-system
      ( simple.comp-hom-system k h))
    ( dependent.comp-hom-system
      ( dependent-hom-system-simple-hom-system k)
      ( dependent-hom-system-simple-hom-system h))
dependent.section-system.type
  ( comp-dependent-hom-system-simple-hom-system k h) X =
  refl
dependent.section-system.element
  ( comp-dependent-hom-system-simple-hom-system k h) x =
  refl
dependent.section-system.slice
  ( comp-dependent-hom-system-simple-hom-system {f = f} k h) X =
  comp-dependent-hom-system-simple-hom-system
    ( simple.hom-system.slice k (f X))
    ( simple.hom-system.slice h X)

dependent-htpy-hom-system-simple-htpy-hom-system :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  {σ : simple.system l3 A} {τ : simple.system l4 B}
  {g h : simple.hom-system f σ τ} →
  simple.htpy-hom-system g h →
  dependent.htpy-hom-system
    ( dependent-hom-system-simple-hom-system g)
    ( dependent-hom-system-simple-hom-system h)
dependent.section-system.type
  ( dependent-htpy-hom-system-simple-htpy-hom-system H) = refl-htpy
dependent.section-system.element
  ( dependent-htpy-hom-system-simple-htpy-hom-system H) {X} =
  simple.htpy-hom-system.element H X
dependent.section-system.slice
  ( dependent-htpy-hom-system-simple-htpy-hom-system H) X =
  dependent-htpy-hom-system-simple-htpy-hom-system
    ( simple.htpy-hom-system.slice H X)

dependent-weakening-simple-weakening :
  {l1 l2 : Level} {A : UU l1} {σ : simple.system l2 A}
  (W : simple.weakening σ) →
  dependent.weakening (dependent-system-simple-system σ)
dependent.weakening.type (dependent-weakening-simple-weakening W) X =
  dependent-hom-system-simple-hom-system (simple.weakening.element W X)
dependent.weakening.slice (dependent-weakening-simple-weakening W) X =
  dependent-weakening-simple-weakening (simple.weakening.slice W X)

dependent-substitution-simple-substitution :
  {l1 l2 : Level} {A : UU l1} {σ : simple.system l2 A} →
  simple.substitution σ →
  dependent.substitution (dependent-system-simple-system σ)
dependent.substitution.type (dependent-substitution-simple-substitution S) x =
  dependent-hom-system-simple-hom-system (simple.substitution.element S x)
dependent.substitution.slice (dependent-substitution-simple-substitution S) X =
  dependent-substitution-simple-substitution (simple.substitution.slice S X)

dependent-generic-element-simple-generic-element :
  {l1 l2 : Level} {A : UU l1} {σ : simple.system l2 A} →
  (W : simple.weakening σ) → simple.generic-element σ →
  dependent.generic-element
    ( dependent-weakening-simple-weakening W)
dependent.generic-element.type
  ( dependent-generic-element-simple-generic-element W δ) X =
  simple.generic-element.element δ X
dependent.generic-element.slice
  ( dependent-generic-element-simple-generic-element W δ) X =
  dependent-generic-element-simple-generic-element
    ( simple.weakening.slice W X)
    ( simple.generic-element.slice δ X)

dependent-preserves-weakening-simple-preserves-weakening :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  {σ : simple.system l3 A} {τ : simple.system l4 B}
  {Wσ : simple.weakening σ} {Wτ : simple.weakening τ}
  {g : simple.hom-system f σ τ} →
  simple.preserves-weakening Wσ Wτ g →
  dependent.preserves-weakening
    ( dependent-weakening-simple-weakening Wσ)
    ( dependent-weakening-simple-weakening Wτ)
    ( dependent-hom-system-simple-hom-system g)
dependent.preserves-weakening.type
  ( dependent-preserves-weakening-simple-preserves-weakening Wg) X =
  {!!}
dependent.preserves-weakening.slice
  ( dependent-preserves-weakening-simple-preserves-weakening Wg) X =
  {!!}

dependent-wpw-simple-wpw :
  {l1 l2 : Level} {A : UU l1} {σ : simple.system l2 A}
  {W : simple.weakening σ} →
  simple.weakening-preserves-weakening W →
  dependent.weakening-preserves-weakening
    ( dependent-weakening-simple-weakening W)
dependent.weakening-preserves-weakening.type (dependent-wpw-simple-wpw WW) X =
  {!dependent.concat-htpy-hom-system ? ?!}
dependent.weakening-preserves-weakening.slice (dependent-wpw-simple-wpw WW) = {!!}
