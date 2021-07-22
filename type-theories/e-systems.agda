{-# OPTIONS --with-K --exact-split --allow-unsolved-metas #-}

module type-theories.e-systems where

import book
open book public

module E where

record system (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2)
  where
  field
    context : UU l1
    dependent-context : context → UU l1
    element : (Γ : context) → dependent-context Γ → UU l2
    empty-context : context
    context-extension : (Γ : context) → dependent-context Γ → context
    empty-dependent-context : (Γ : context) → dependent-context Γ
    dependent-context-extension : {Γ : context} (Δ : dependent-context Γ) →
      dependent-context (context-extension Γ Δ) → dependent-context Γ
    associative-context-extension :
      (Γ : context) (Δ : dependent-context Γ)
      (P : dependent-context (context-extension Γ Δ)) →
      Id (context-extension (context-extension Γ Δ) P)
         (context-extension Γ (dependent-context-extension Δ P))
    associative-dependent-context-extension :
      {Γ : context} (Δ : dependent-context Γ)
      (P : dependent-context (context-extension Γ Δ))
      (Q : dependent-context (context-extension (context-extension Γ Δ) P)) →
      Id ( dependent-context-extension
           ( dependent-context-extension Δ P)
           ( tr dependent-context (associative-context-extension Γ Δ P) Q))
         (dependent-context-extension Δ (dependent-context-extension P Q))

ap-context-extension :
  {l1 l2 : Level} {A : system l1 l2} {Γ Γ' : system.context A}
  (p : Id Γ Γ') {Δ : system.dependent-context A Γ}
  {Δ' : system.dependent-context A Γ'}
  (q : Id (tr (system.dependent-context A) p Δ) Δ') →
  Id (system.context-extension A Γ Δ) (system.context-extension A Γ' Δ')
ap-context-extension refl refl = refl

slice : {l1 l2 : Level} (A : system l1 l2) (Γ : system.context A) →
  system l1 l2
system.context (slice A Γ) =
  system.dependent-context A Γ
system.dependent-context (slice A Γ) Δ =
  system.dependent-context A (system.context-extension A Γ Δ)
system.element (slice A Γ) Δ =
  system.element A (system.context-extension A Γ Δ)
system.empty-context (slice A Γ) =
  system.empty-dependent-context A Γ
system.context-extension (slice A Γ) =
  system.dependent-context-extension A
system.empty-dependent-context (slice A Γ) Δ =
  system.empty-dependent-context A (system.context-extension A Γ Δ)
system.dependent-context-extension (slice A Γ) {Δ} P Q =
  system.dependent-context-extension A
    { system.context-extension A Γ Δ}
    ( P)
    ( tr ( system.dependent-context A)
         ( inv (system.associative-context-extension A Γ Δ P))
         ( Q))
system.associative-context-extension (slice A Γ) Δ P Q =
  ( ap ( system.dependent-context-extension A
         ( system.dependent-context-extension A Δ P))
       ( ( ap ( λ t → tr (system.dependent-context A) t Q)
              ( inv
                ( left-inv
                  ( system.associative-context-extension A Γ Δ P)))) ∙
         ( tr-concat
           ( inv (system.associative-context-extension A Γ Δ P))
           ( system.associative-context-extension A Γ Δ P)
           ( Q)))) ∙
  ( system.associative-dependent-context-extension A {Γ} Δ P 
    ( tr ( system.dependent-context A) 
         ( inv (system.associative-context-extension A Γ Δ P)) 
         ( Q))) 
system.associative-dependent-context-extension (slice A Γ) {Δ} P Q R =
  {!!} ∙
  ( ( system.associative-dependent-context-extension A
      { system.context-extension A Γ Δ}
      ( P)
      ( tr ( system.dependent-context A)
           ( inv (system.associative-context-extension A Γ Δ P))
           ( Q))
      ( tr ( system.dependent-context A)
           ( ap-context-extension
             { Γ = system.context-extension A Γ (system.dependent-context-extension A Δ P)}
             { Γ' = system.context-extension A (system.context-extension A Γ Δ) P}
             ( inv (system.associative-context-extension A Γ Δ P))
             {Δ = Q}
             { Δ' = tr (system.dependent-context A) (inv (system.associative-context-extension A Γ Δ P)) Q}
             ( refl))
           ( R))) ∙
    {!!})

{- 

(Γ.(Δ.P)).Q = ((Γ.Δ).P).Q'
system.associative-dependent-context-extension A {Γ} Δ P 
  ( tr ( system.dependent-context A) 
       ( inv (system.associative-context-extension A Γ Δ P)) 
       ( Q)) :
Id
(system.dependent-context-extension A
 (system.dependent-context-extension A Δ P)
 (tr (system.dependent-context A)
  (system.associative-context-extension A Γ Δ P)
  (tr (system.dependent-context A)
   (inv (system.associative-context-extension A Γ Δ P)) Q)))
(system.dependent-context-extension A Δ
 (system.dependent-context-extension A P
  (tr (system.dependent-context A)
   (inv (system.associative-context-extension A Γ Δ P)) Q)))
-}

