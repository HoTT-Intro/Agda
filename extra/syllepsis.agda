{-# OPTIONS --without-K --exact-split #-}

module extra.syllepsis where

import book
open book public

--------------------------------------------------------------------------------

{- Identity types of identity types -}

vertical-concat :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} (α : Id p q) (β : Id q r) →
  Id p r
vertical-concat α β = α ∙ β

ap-vertical-concat :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} {α α' : Id p q}
  (s : Id α α') {β β' : Id q r} (t : Id β β') →
  Id (vertical-concat α β) (vertical-concat α' β')
ap-vertical-concat s t = ap-binary vertical-concat s t

horizontal-concat :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z} →
  Id p q → Id u v → Id (p ∙ u) (q ∙ v)
horizontal-concat refl refl = refl

left-unit-law-horizontal-concat :
  {l : Level} {A : UU l} {x y z : A} {p : Id x y} {u v : Id y z} (γ : Id u v) →
  Id (horizontal-concat (refl {x = p}) γ) (ap (concat p z) γ)
left-unit-law-horizontal-concat refl = refl

right-unit-law-horizontal-concat :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} (α : Id p q) {u : Id y z} →
  Id (horizontal-concat α (refl {x = u})) (ap (concat' x u) α)
right-unit-law-horizontal-concat refl = refl

ap-horizontal-concat :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z} →
  {α α' : Id p q} (s : Id α α') {β β' : Id u v} (t : Id β β') →
  Id (horizontal-concat α β) (horizontal-concat α' β')
ap-horizontal-concat s t = ap-binary horizontal-concat s t

interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q r : Id x y} {u v w : Id y z}
  (α : Id p q) (β : Id q r) (γ : Id u v) (δ : Id v w) →
  Id ( horizontal-concat (vertical-concat α β) (vertical-concat γ δ))
     ( vertical-concat (horizontal-concat α γ) (horizontal-concat β δ))
interchange-Id² refl refl refl refl = refl

--------------------------------------------------------------------------------

{- The double loop space -}

vertical-concat-Ω² :
  {l : Level} {A : UU l} {a : A} → type-Ω² a → type-Ω² a → type-Ω² a
vertical-concat-Ω² α β = vertical-concat α β

left-unit-law-vertical-concat-Ω² :
  {l : Level} {A : UU l} {a : A} {α : type-Ω² a} →
  Id (vertical-concat-Ω² refl-Ω² α) α
left-unit-law-vertical-concat-Ω² = left-unit

right-unit-law-vertical-concat-Ω² :
  {l : Level} {A : UU l} {a : A} {α : type-Ω² a} →
  Id (vertical-concat-Ω² α refl-Ω²) α
right-unit-law-vertical-concat-Ω² = right-unit

horizontal-concat-Ω² :
  {l : Level} {A : UU l} {a : A} → type-Ω² a → type-Ω² a → type-Ω² a
horizontal-concat-Ω² α β = horizontal-concat α β

left-unit-law-horizontal-concat-Ω² :
  {l : Level} {A : UU l} {a : A} {α : type-Ω² a} →
  Id (horizontal-concat-Ω² refl-Ω² α) α
left-unit-law-horizontal-concat-Ω² {α = α} =
  ( left-unit-law-horizontal-concat α) ∙ (ap-id α)

right-unit-law-horizontal-concat-Ω² :
  {l : Level} {A : UU l} {a : A} {α : type-Ω² a} →
  Id (horizontal-concat-Ω² α refl-Ω²) α
right-unit-law-horizontal-concat-Ω² {α = α} =
  ( right-unit-law-horizontal-concat α) ∙
  ( ( inv right-unit) ∙
    ( ( inv (htpy-nat {g = id} (λ t → right-unit) α)) ∙
      ( ap (concat right-unit refl) (ap-id α))))

interchange-Ω² :
  {l : Level} {A : UU l} {a : A} (α β γ δ : type-Ω² a) →
  Id ( horizontal-concat-Ω² (vertical-concat-Ω² α β) (vertical-concat-Ω² γ δ))
     ( vertical-concat-Ω² (horizontal-concat-Ω² α γ) (horizontal-concat-Ω² β δ))
interchange-Ω² α β γ δ = interchange-Id² α β γ δ

eckmann-hilton-Ω² :
  {l : Level} {A : UU l} {a : A} (α β : type-Ω² a) →
  Id (α ∙ β) (β ∙ α)
eckmann-hilton-Ω² α β =
  ( ap-vertical-concat
    ( inv (right-unit-law-horizontal-concat-Ω² {α = α}))
    ( inv left-unit-law-horizontal-concat-Ω²)) ∙
  ( ( inv (interchange-Ω² α refl-Ω² refl-Ω² β)) ∙
    ( ( ap-horizontal-concat right-unit (inv right-unit)) ∙
      ( ( interchange-Ω² refl-Ω² α β refl-Ω²) ∙
        ( ap-vertical-concat
          ( left-unit-law-horizontal-concat-Ω² {α = β})
          ( right-unit-law-horizontal-concat-Ω² {α = α})))))

--------------------------------------------------------------------------------

-- Identity types of identity types of identity types

x-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} {α β γ : Id p q} →
  Id α β → Id β γ → Id α γ
x-concat-Id³ σ τ = σ ∙ τ

left-unit-law-x-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} {α β : Id p q} {τ : Id α β} →
  Id (x-concat-Id³ refl τ) τ
left-unit-law-x-concat-Id³ = left-unit

right-unit-law-x-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} {α β : Id p q} {τ : Id α β} →
  Id (x-concat-Id³ τ refl) τ
right-unit-law-x-concat-Id³ = right-unit

y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} {α β : Id p q}
  {γ δ : Id q r} → Id α β → Id γ δ → Id (α ∙ γ) (β ∙ δ)
y-concat-Id³ σ τ = horizontal-concat σ τ

ap-y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} {α β : Id p q}
  {γ δ : Id q r} {σ σ' : Id α β} (s : Id σ σ') {τ τ' : Id γ δ} (t : Id τ τ') →
  Id (y-concat-Id³ σ τ) (y-concat-Id³ σ' τ')
ap-y-concat-Id³ s t = ap-horizontal-concat s t

left-unit-law-y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} {α : Id p q} {γ δ : Id q r}
  {τ : Id γ δ} → Id (y-concat-Id³ (refl {x = α}) τ) (ap (concat α r) τ)
left-unit-law-y-concat-Id³ {τ = τ} = left-unit-law-horizontal-concat τ

right-unit-law-y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} {α β : Id p q} {γ : Id q r}
  {σ : Id α β} → Id (y-concat-Id³ σ (refl {x = γ})) (ap (concat' p γ) σ)
right-unit-law-y-concat-Id³ {σ = σ} = right-unit-law-horizontal-concat σ

z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z}
  {α β : Id p q} {γ δ : Id u v} →
  Id α β → Id γ δ → Id (horizontal-concat α γ) (horizontal-concat β δ)
z-concat-Id³ refl refl = refl

ap-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z}
  {α β : Id p q} {γ δ : Id u v} {σ σ' : Id α β} {τ τ' : Id γ δ} →
  Id σ σ' → Id τ τ' → Id (z-concat-Id³ σ τ) (z-concat-Id³ σ' τ')
ap-z-concat-Id³ s t = ap-binary z-concat-Id³ s t

left-unit-law-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z}
  {α : Id p q} {γ δ : Id u v} (τ : Id γ δ) →
  Id (z-concat-Id³ (refl {x = α}) τ) (ap (horizontal-concat α) τ)
left-unit-law-z-concat-Id³ refl = refl

right-unit-law-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z}
  {α β : Id p q} {γ : Id u v} (σ : Id α β) →
  Id (z-concat-Id³ σ (refl {x = γ})) (ap (λ ω → horizontal-concat ω γ) σ)
right-unit-law-z-concat-Id³ refl = refl

interchange-x-y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} {α β γ : Id p q}
  {δ ε ζ : Id q r} (σ : Id α β) (τ : Id β γ) (υ : Id δ ε) (ϕ : Id ε ζ) →
  Id ( y-concat-Id³ (x-concat-Id³ σ τ) (x-concat-Id³ υ ϕ))
     ( x-concat-Id³ (y-concat-Id³ σ υ) (y-concat-Id³ τ ϕ))
interchange-x-y-concat-Id³ = interchange-Id²

interchange-x-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z}
  {α β γ : Id p q} {δ ε ζ : Id u v} (σ : Id α β) (τ : Id β γ) (υ : Id δ ε)
  (ϕ : Id ε ζ) →
  Id ( z-concat-Id³ (x-concat-Id³ σ τ) (x-concat-Id³ υ ϕ))
     ( x-concat-Id³ (z-concat-Id³ σ υ) (z-concat-Id³ τ ϕ))
interchange-x-z-concat-Id³ refl τ refl ϕ = refl

interchange-y-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q r : Id x y} {u v w : Id y z}
  {α β : Id p q} {γ δ : Id q r} {ε ζ : Id u v} {η θ : Id v w}
  (σ : Id α β) (τ : Id γ δ) (υ : Id ε ζ) (ϕ : Id η θ) →
  Id ( ( z-concat-Id³ (y-concat-Id³ σ τ) (y-concat-Id³ υ ϕ)) ∙
       ( interchange-Id² β δ ζ θ))
     ( ( interchange-Id² α γ ε η) ∙
       ( y-concat-Id³ (z-concat-Id³ σ υ) (z-concat-Id³ τ ϕ)))
interchange-y-z-concat-Id³ refl refl refl refl = inv right-unit

source-coherence-interchange-Id³ :
  {l : Level} {X : UU l} {x y z : X} {p q r : Id x y} {u v w : Id y z}
  {α β γ : Id p q} {δ ε ζ : Id q r} {η θ ι : Id u v} {κ μ ν : Id v w}
  (A : Id α β) (B : Id β γ) (C : Id δ ε) (D : Id ε ζ) (E : Id η θ) (F : Id θ ι)
  (G : Id κ μ) (H : Id μ ν) →
  Id ( ( ( z-concat-Id³
           ( y-concat-Id³ (x-concat-Id³ A B) (x-concat-Id³ C D))
           ( y-concat-Id³ (x-concat-Id³ E F) (x-concat-Id³ G H))) ∙
         ( interchange-Id² γ ζ ι ν)))
     ( ( interchange-Id² α δ η κ) ∙
       ( x-concat-Id³
         ( y-concat-Id³ (z-concat-Id³ A E) (z-concat-Id³ C G))
         ( y-concat-Id³ (z-concat-Id³ B F) (z-concat-Id³ D H))))
source-coherence-interchange-Id³ {l} {X} {x} {y} {z} {p} {q} {r} {u} {v} {w}
  {α} {β} {γ} {δ} {ε} {ζ} {η} {θ} {ι} {κ} {μ} {ν} A B C D E F G H =
  ( interchange-y-z-concat-Id³ (A ∙ B) (C ∙ D) (E ∙ F) (G ∙ H)) ∙
  ( ( ap ( concat
           ( interchange-Id² α δ η κ)
           ( horizontal-concat γ ι ∙ horizontal-concat ζ ν))
         ( ( ap-horizontal-concat
             ( interchange-x-z-concat-Id³ A B E F)
             ( interchange-x-z-concat-Id³ C D G H)) ∙
           ( interchange-x-y-concat-Id³
             ( z-concat-Id³ A E)
             ( z-concat-Id³ B F)
             ( z-concat-Id³ C G)
             ( z-concat-Id³ D H)))))

target-coherence-interchange-Id³ :
  {l : Level} {X : UU l} {x y z : X} {p q r : Id x y} {u v w : Id y z}
  {α β γ : Id p q} {δ ε ζ : Id q r} {η θ ι : Id u v} {κ μ ν : Id v w}
  (A : Id α β) (B : Id β γ) (C : Id δ ε) (D : Id ε ζ) (E : Id η θ) (F : Id θ ι)
  (G : Id κ μ) (H : Id μ ν) →
  Id ( ( ( z-concat-Id³
           ( y-concat-Id³ (x-concat-Id³ A B) (x-concat-Id³ C D))
           ( y-concat-Id³ (x-concat-Id³ E F) (x-concat-Id³ G H))) ∙
         ( interchange-Id² γ ζ ι ν)))
     ( ( interchange-Id² α δ η κ) ∙
       ( x-concat-Id³
         ( y-concat-Id³ (z-concat-Id³ A E) (z-concat-Id³ C G))
         ( y-concat-Id³ (z-concat-Id³ B F) (z-concat-Id³ D H))))
target-coherence-interchange-Id³ {l} {X} {x} {y} {z} {p} {q} {r} {u} {v} {w}
  {α} {β} {γ} {δ} {ε} {ζ} {η} {θ} {ι} {κ} {μ} {ν} A B C D E F G H =
  ( ( ap
      ( concat'
        ( horizontal-concat (α ∙ δ) (η ∙ κ))
        ( interchange-Id² γ ζ ι ν))
      ( ap-z-concat-Id³
        ( interchange-x-y-concat-Id³ A B C D)
        ( interchange-x-y-concat-Id³ E F G H))) ∙
    ( ( ap
        ( concat'
          ( horizontal-concat (α ∙ δ) (η ∙ κ))
          ( interchange-Id² γ ζ ι ν))
        ( interchange-x-z-concat-Id³
          ( y-concat-Id³ A C)
          ( y-concat-Id³ B D)
          ( y-concat-Id³ E G)
          ( y-concat-Id³ F H))) ∙
      ( ( assoc
          ( z-concat-Id³ (y-concat-Id³ A C) (y-concat-Id³ E G))
          ( z-concat-Id³ (y-concat-Id³ B D) (y-concat-Id³ F H))
          ( interchange-Id² γ ζ ι ν)) ∙
        ( ( ap ( concat
                 ( z-concat-Id³ (y-concat-Id³ A C) (y-concat-Id³ E G))
                 ( horizontal-concat γ ι ∙ horizontal-concat ζ ν))
               ( interchange-y-z-concat-Id³ B D F H)) ∙
          ( ( inv
              ( assoc
                ( z-concat-Id³ (y-concat-Id³ A C) (y-concat-Id³ E G))
                ( interchange-Id² β ε θ μ)
                ( y-concat-Id³ (z-concat-Id³ B F) (z-concat-Id³ D H)))) ∙
            ( ap
              ( concat'
                ( horizontal-concat (α ∙ δ) (η ∙ κ))
                ( y-concat-Id³ (z-concat-Id³ B F) (z-concat-Id³ D H)))
              ( interchange-y-z-concat-Id³ A C E G))))))) ∙
  ( assoc
    ( interchange-Id² α δ η κ)
    ( y-concat-Id³ (z-concat-Id³ A E) (z-concat-Id³ C G))
    ( y-concat-Id³ (z-concat-Id³ B F) (z-concat-Id³ D H)))
  
coherence-interchange-Id³ :
  {l : Level} {X : UU l} {x y z : X} {p q r : Id x y} {u v w : Id y z}
  {α β γ : Id p q} {δ ε ζ : Id q r} {η θ ι : Id u v} {κ μ ν : Id v w}
  (A : Id α β) (B : Id β γ) (C : Id δ ε) (D : Id ε ζ) (E : Id η θ) (F : Id θ ι)
  (G : Id κ μ) (H : Id μ ν) →
  Id ( source-coherence-interchange-Id³ A B C D E F G H)
     ( target-coherence-interchange-Id³ A B C D E F G H)
coherence-interchange-Id³
  {l} {X} {x} {y} {z} {p} {.p} {.p} {u} {.u} {.u} {refl} {.refl} {.refl} {refl}
  {.refl} {.refl} {refl} {.refl} {.refl} {refl} {.refl} {.refl} refl refl refl
  refl refl refl refl refl = refl

--------------------------------------------------------------------------------

-- Unit laws for the associator

unit-law-assoc-011 :
  {l : Level} {X : UU l} {x y z : X} (p : Id x y) (q : Id y z) →
  Id (assoc refl p q) refl
unit-law-assoc-011 p q = refl

unit-law-assoc-101 :
  {l : Level} {X : UU l} {x y z : X} (p : Id x y) (q : Id y z) →
  Id (assoc p refl q) (ap (concat' x q) right-unit)
unit-law-assoc-101 refl refl = refl

unit-law-assoc-101' :
  {l : Level} {X : UU l} {x y z : X} (p : Id x y) (q : Id y z) →
  Id (inv (assoc p refl q)) (ap (concat' x q) (inv right-unit))
unit-law-assoc-101' refl refl = refl

unit-law-assoc-110 :
  {l : Level} {X : UU l} {x y z : X} (p : Id x y) (q : Id y z) →
  Id (assoc p q refl ∙ ap (concat p z) right-unit) right-unit
unit-law-assoc-110 refl refl = refl

unit-law-assoc-110' :
  {l : Level} {X : UU l} {x y z : X} (p : Id x y) (q : Id y z) →
  Id (inv right-unit ∙ assoc p q refl) (ap (concat p z) (inv right-unit))
unit-law-assoc-110' refl refl = refl

--------------------------------------------------------------------------------

-- Triple loop spaces

x-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} → type-Ω³ a → type-Ω³ a → type-Ω³ a
x-concat-Ω³ = x-concat-Id³

ap-x-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} {α α' β β' : type-Ω³ a}
  (s : Id α α') (t : Id β β') → Id (x-concat-Ω³ α β) (x-concat-Ω³ α' β')
ap-x-concat-Ω³ s t = ap-binary x-concat-Ω³ s t

y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} → type-Ω³ a → type-Ω³ a → type-Ω³ a
y-concat-Ω³ = y-concat-Id³

ap-y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} {α α' β β' : type-Ω³ a}
  (s : Id α α') (t : Id β β') → Id (y-concat-Ω³ α β) (y-concat-Ω³ α' β')
ap-y-concat-Ω³ s t = ap-y-concat-Id³ s t

z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} → type-Ω³ a → type-Ω³ a → type-Ω³ a
z-concat-Ω³ = z-concat-Id³

ap-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} {α α' β β' : type-Ω³ a}
  (s : Id α α') (t : Id β β') → Id (z-concat-Ω³ α β) (z-concat-Ω³ α' β')
ap-z-concat-Ω³ s t = ap-z-concat-Id³ s t

-- The interchange laws for Ω³

interchange-x-y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α β γ δ : type-Ω³ a) →
  Id ( y-concat-Ω³ (x-concat-Ω³ α β) (x-concat-Ω³ γ δ))
     ( x-concat-Ω³ (y-concat-Ω³ α γ) (y-concat-Ω³ β δ))
interchange-x-y-concat-Ω³ = interchange-x-y-concat-Id³

interchange-x-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α β γ δ : type-Ω³ a) →
  Id ( z-concat-Ω³ (x-concat-Ω³ α β) (x-concat-Ω³ γ δ))
     ( x-concat-Ω³ (z-concat-Ω³ α γ) (z-concat-Ω³ β δ))
interchange-x-z-concat-Ω³ = interchange-x-z-concat-Id³

interchange-y-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α β γ δ : type-Ω³ a) →
  Id ( z-concat-Ω³ (y-concat-Ω³ α β) (y-concat-Ω³ γ δ))
     ( y-concat-Ω³ (z-concat-Ω³ α γ) (z-concat-Ω³ β δ))
interchange-y-z-concat-Ω³ α β γ δ =
  inv right-unit ∙ interchange-y-z-concat-Id³ α β γ δ

coherence-interchange-Ω³ :
  {l : Level} {A : UU l} {a : A} (α β γ δ ε ζ η θ : type-Ω³ a) →
  Id ( ( interchange-y-z-concat-Ω³
         ( x-concat-Ω³ α β)
         ( x-concat-Ω³ γ δ)
         ( x-concat-Ω³ ε ζ)
         ( x-concat-Ω³ η θ)) ∙
       ( ( ap-y-concat-Ω³
           ( interchange-x-z-concat-Ω³ α β ε ζ)
           ( interchange-x-z-concat-Ω³ γ δ η θ)) ∙
         ( interchange-x-y-concat-Ω³
           ( z-concat-Ω³ α ε)
           ( z-concat-Ω³ β ζ)
           ( z-concat-Ω³ γ η)
           ( z-concat-Ω³ δ θ))))
     ( ( ap-z-concat-Ω³
         ( interchange-x-y-concat-Ω³ α β γ δ)
         ( interchange-x-y-concat-Ω³ ε ζ η θ)) ∙
       ( ( interchange-x-z-concat-Ω³
           ( y-concat-Ω³ α γ)
           ( y-concat-Ω³ β δ)
           ( y-concat-Ω³ ε η)
           ( y-concat-Ω³ ζ θ)) ∙
         ( ap-x-concat-Ω³
           ( interchange-y-z-concat-Ω³ α γ ε η)
           ( interchange-y-z-concat-Ω³ β δ ζ θ))))
coherence-interchange-Ω³ α β γ δ ε ζ η θ =
  ( assoc
    ( inv right-unit)
    ( interchange-y-z-concat-Id³
      ( x-concat-Id³ α β)
      ( x-concat-Id³ γ δ)
      ( x-concat-Id³ ε ζ)
      ( x-concat-Id³ η θ))
    ( ( ap-y-concat-Id³
        ( interchange-x-z-concat-Id³ α β ε ζ)
        ( interchange-x-z-concat-Id³ γ δ η θ)) ∙
      ( interchange-x-y-concat-Id³
        ( z-concat-Id³ α ε)
        ( z-concat-Id³ β ζ)
        ( z-concat-Id³ γ η)
        ( z-concat-Id³ δ θ)))) ∙
  ( ( ap
      ( concat
        ( inv right-unit)
        ( ( y-concat-Id³ (z-concat-Id³ α ε) (z-concat-Id³ γ η)) ∙
          ( y-concat-Id³ (z-concat-Id³ β ζ) (z-concat-Id³ δ θ)))) 
      ( ( inv
          ( ap
            ( concat
              ( interchange-y-z-concat-Id³
                ( x-concat-Id³ α β)
                ( x-concat-Id³ γ δ)
                ( x-concat-Id³ ε ζ)
                ( x-concat-Id³ η θ))
              ( ( y-concat-Id³ (z-concat-Id³ α ε) (z-concat-Id³ γ η)) ∙
                ( y-concat-Id³ (z-concat-Id³ β ζ) (z-concat-Id³ δ θ))))
            ( ap-id
              ( ( ap-binary horizontal-concat
                  ( interchange-x-z-concat-Id³ α β ε ζ)
                  ( interchange-x-z-concat-Id³ γ δ η θ)) ∙
                ( interchange-Id²
                  ( z-concat-Id³ α ε)
                  ( z-concat-Id³ β ζ)
                  ( z-concat-Id³ γ η)
                  ( z-concat-Id³ δ θ)))))) ∙
        ( coherence-interchange-Id³ α β γ δ ε ζ η θ))) ∙
    ( ( ap
        ( concat
          ( inv right-unit)
          ( x-concat-Id³
            ( y-concat-Id³ (z-concat-Id³ α ε) (z-concat-Id³ γ η))
            ( y-concat-Id³ (z-concat-Id³ β ζ) (z-concat-Id³ δ θ))))
        ( right-unit)) ∙
      ( ( inv
          ( assoc
            ( inv right-unit)
            ( ap
              ( concat' refl refl)
              ( ap-z-concat-Id³ 
                ( interchange-x-y-concat-Id³ α β γ δ)
                ( interchange-x-y-concat-Id³ ε ζ η θ)))
            ( ( ap 
                ( concat' refl refl)
                ( interchange-x-z-concat-Id³ 
                  ( y-concat-Id³ α γ) 
                  ( y-concat-Id³ β δ)
                  ( y-concat-Id³ ε η) 
                  ( y-concat-Id³ ζ θ))) ∙
              ( ( assoc 
                  ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η))
                  ( z-concat-Id³ (y-concat-Id³ β δ) (y-concat-Id³ ζ θ)) 
                  ( refl)) ∙
                ( ( ap
                    ( concat
                      ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η))
                      ( refl))
                    ( interchange-y-z-concat-Id³ β δ ζ θ)) ∙
                  ( ( inv
                      ( assoc 
                        ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η)) 
                        ( refl)
                        ( y-concat-Id³
                          ( z-concat-Id³ β ζ)
                          ( z-concat-Id³ δ θ)))) ∙
                    ( ap
                      ( concat'
                        ( refl)
                        ( y-concat-Id³ (z-concat-Id³ β ζ) (z-concat-Id³ δ θ)))
                      ( interchange-y-z-concat-Id³ α γ ε η))))))) ∙
          ( ap
            ( concat'
              ( z-concat-Id³
                ( y-concat-Id³ (x-concat-Id³ α β) (x-concat-Id³ γ δ))
                ( y-concat-Id³ (x-concat-Id³ ε ζ) (x-concat-Id³ η θ)))
              ( ( ap
                  ( concat'
                    ( refl)
                    ( refl))
                  ( interchange-x-z-concat-Id³
                    ( y-concat-Id³ α γ)
                    ( y-concat-Id³ β δ)
                    ( y-concat-Id³ ε η)
                    ( y-concat-Id³ ζ θ))) ∙
                ( ( assoc
                    ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η))
                    ( z-concat-Id³ (y-concat-Id³ β δ) (y-concat-Id³ ζ θ))
                    ( refl)) ∙
                  ( ( ap
                      ( concat
                        ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η))
                        ( refl))
                      ( interchange-y-z-concat-Id³ β δ ζ θ)) ∙
                    ( ( inv
                        ( assoc
                          ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η))
                          ( refl)
                          ( y-concat-Id³
                            ( z-concat-Id³ β ζ)
                            ( z-concat-Id³ δ θ)))) ∙
                      ( ap
                        ( concat'
                          ( refl)
                          ( y-concat-Id³
                            ( z-concat-Id³ β ζ)
                            ( z-concat-Id³ δ θ)))
                        ( interchange-y-z-concat-Id³ α γ ε η))))))))
          ( ( htpy-nat
              ( λ x → inv right-unit)
              ( ap-z-concat-Id³
                ( interchange-x-y-concat-Id³ α β γ δ)
                ( interchange-x-y-concat-Id³ ε ζ η θ))) ∙
            ( ap
              ( concat'
                ( z-concat-Id³
                  ( y-concat-Id³ (x-concat-Id³ α β) (x-concat-Id³ γ δ))
                  ( y-concat-Id³ (x-concat-Id³ ε ζ) (x-concat-Id³ η θ)))
                ( inv right-unit))
              ( ap-id
                ( ap-z-concat-Id³
                  ( interchange-x-y-concat-Id³ α β γ δ)
                  ( interchange-x-y-concat-Id³ ε ζ η θ)))))) ∙
        ( ( assoc
            ( ap-z-concat-Ω³
              ( interchange-x-y-concat-Ω³ α β γ δ)
              ( interchange-x-y-concat-Ω³ ε ζ η θ))
            ( inv right-unit)
            ( _)) ∙
          ( ap
            ( concat
              ( ap-z-concat-Ω³
                ( interchange-x-y-concat-Ω³ α β γ δ)
                ( interchange-x-y-concat-Ω³ ε ζ η θ))
              ( x-concat-Ω³
                ( y-concat-Ω³ (z-concat-Ω³ α ε) (z-concat-Ω³ γ η))
                ( y-concat-Ω³ (z-concat-Ω³ β ζ) (z-concat-Ω³ δ θ))))
            ( ( ( inv
                  ( assoc
                    ( inv right-unit)
                    ( ap
                      ( concat' refl refl)
                      ( interchange-x-z-concat-Id³
                        ( y-concat-Id³ α γ)
                        ( y-concat-Id³ β δ)
                        ( y-concat-Id³ ε η)
                        ( y-concat-Id³ ζ θ)))
                    ( ( ( assoc 
                          ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η))
                          ( z-concat-Id³ (y-concat-Id³ β δ) (y-concat-Id³ ζ θ)) 
                          ( refl)) ∙
                        ( ( ap
                            ( concat
                              ( z-concat-Id³
                                ( y-concat-Id³ α γ)
                                ( y-concat-Id³ ε η))
                              ( refl))
                            ( interchange-y-z-concat-Id³ β δ ζ θ)) ∙
                          ( ( inv
                              ( assoc 
                                ( z-concat-Id³
                                  ( y-concat-Id³ α γ)
                                  ( y-concat-Id³ ε η)) 
                                ( refl)
                                ( y-concat-Id³
                                  ( z-concat-Id³ β ζ)
                                  ( z-concat-Id³ δ θ)))) ∙
                            ( ap
                              ( concat'
                                ( refl)
                                ( y-concat-Id³
                                  ( z-concat-Id³ β ζ)
                                  ( z-concat-Id³ δ θ)))
                              ( interchange-y-z-concat-Id³ α γ ε η)))))))) ∙
                ( ap
                  ( concat'
                    ( z-concat-Ω³
                      ( x-concat-Ω³ (y-concat-Ω³ α γ) (y-concat-Ω³ β δ))
                      ( x-concat-Ω³ (y-concat-Ω³ ε η) (y-concat-Ω³ ζ θ)))
                    ( ( ( assoc 
                  ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η))
                  ( z-concat-Id³ (y-concat-Id³ β δ) (y-concat-Id³ ζ θ)) 
                  ( refl)) ∙
                ( ( ap
                    ( concat
                      ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η))
                      ( refl))
                    ( interchange-y-z-concat-Id³ β δ ζ θ)) ∙
                  ( ( inv
                      ( assoc 
                        ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η)) 
                        ( refl)
                        ( y-concat-Id³
                          ( z-concat-Id³ β ζ)
                          ( z-concat-Id³ δ θ)))) ∙
                    ( ap
                      ( concat'
                        ( refl)
                        ( y-concat-Id³ (z-concat-Id³ β ζ) (z-concat-Id³ δ θ)))
                      ( interchange-y-z-concat-Id³ α γ ε η))))))))
                ( ( htpy-nat
                    ( λ x → inv right-unit)
                    ( interchange-x-z-concat-Ω³
                      ( y-concat-Ω³ α γ)
                      ( y-concat-Ω³ β δ)
                      ( y-concat-Ω³ ε η)
                      ( y-concat-Ω³ ζ θ))) ∙
                  ( ap
                    ( concat'
                      ( z-concat-Ω³
                        ( x-concat-Ω³ (y-concat-Ω³ α γ) (y-concat-Ω³ β δ))
                        ( x-concat-Ω³ (y-concat-Ω³ ε η) (y-concat-Ω³ ζ θ)))
                      ( inv right-unit))
                    ( ap-id
                      ( interchange-x-z-concat-Ω³
                        ( y-concat-Ω³ α γ)
                        ( y-concat-Ω³ β δ)
                        ( y-concat-Ω³ ε η)
                        ( y-concat-Ω³ ζ θ)))))) ∙
              ( ( assoc
                  ( interchange-x-z-concat-Ω³
                    ( y-concat-Ω³ α γ)
                    ( y-concat-Ω³ β δ)
                    ( y-concat-Ω³ ε η)
                    ( y-concat-Ω³ ζ θ))
                  ( inv right-unit)
                  ( _)) ∙
                ( ap
                  ( concat
                    ( interchange-x-z-concat-Ω³
                      ( y-concat-Ω³ α γ)
                      ( y-concat-Ω³ β δ)
                      ( y-concat-Ω³ ε η)
                      ( y-concat-Ω³ ζ θ))
                    ( x-concat-Ω³
                      ( y-concat-Ω³ (z-concat-Ω³ α ε) (z-concat-Ω³ γ η))
                      ( y-concat-Ω³ (z-concat-Ω³ β ζ) (z-concat-Ω³ δ θ))))
                  ( ( inv
                      ( assoc
                        ( inv right-unit)
                        ( assoc
                          ( z-concat-Ω³ (y-concat-Ω³ α γ) (y-concat-Ω³ ε η))
                          ( z-concat-Ω³ (y-concat-Ω³ β δ) (y-concat-Ω³ ζ θ))
                          ( refl))
                        ( _))) ∙
                    ( ( ap
                        ( concat'
                          ( x-concat-Ω³
                            ( z-concat-Ω³ (y-concat-Ω³ α γ) (y-concat-Ω³ ε η))
                            ( z-concat-Ω³ (y-concat-Ω³ β δ) (y-concat-Ω³ ζ θ)))
                          ( ( ap
                              ( concat
                                ( z-concat-Ω³
                                  ( y-concat-Ω³ α γ)
                                  ( y-concat-Ω³ ε η))
                                ( refl))
                              ( interchange-y-z-concat-Id³ β δ ζ θ)) ∙
                            ( ( inv
                                ( assoc
                                  ( z-concat-Ω³
                                    ( y-concat-Ω³ α γ)
                                    ( y-concat-Ω³ ε η))
                                  ( refl)
                                  ( y-concat-Ω³
                                    ( z-concat-Ω³ β ζ)
                                    ( z-concat-Ω³ δ θ)))) ∙
                              ( ap
                                ( concat'
                                  ( refl)
                                  ( y-concat-Ω³
                                    ( z-concat-Ω³ β ζ)
                                    ( z-concat-Ω³ δ θ)))
                                ( interchange-y-z-concat-Id³ α γ ε η)))))
                        ( unit-law-assoc-110'
                          ( z-concat-Ω³ (y-concat-Ω³ α γ) (y-concat-Ω³ ε η))
                          ( z-concat-Ω³ (y-concat-Ω³ β δ) (y-concat-Ω³ ζ θ)))) ∙
                      ( ( inv
                          ( assoc
                            ( ap
                              ( concat
                                ( z-concat-Ω³
                                  ( y-concat-Ω³ α γ)
                                  ( y-concat-Ω³ ε η))
                                ( refl))
                              ( inv right-unit))
                            ( ap
                              ( concat
                                ( z-concat-Ω³
                                  ( y-concat-Ω³ α γ)
                                  ( y-concat-Ω³ ε η))
                                ( refl))
                              ( interchange-y-z-concat-Id³ β δ ζ θ))
                            ( _))) ∙
                        ( ( ap
                            ( concat'
                              ( x-concat-Ω³
                                ( z-concat-Ω³
                                  ( y-concat-Ω³ α γ)
                                  ( y-concat-Ω³ ε η))
                                ( z-concat-Ω³
                                  ( y-concat-Ω³ β δ)
                                  ( y-concat-Ω³ ζ θ)))
                              ( ( inv
                                  ( assoc
                                    ( z-concat-Ω³
                                      ( y-concat-Ω³ α γ)
                                      ( y-concat-Ω³ ε η))
                                    ( refl)
                                    ( y-concat-Ω³
                                      ( z-concat-Ω³ β ζ)
                                      ( z-concat-Ω³ δ θ)))) ∙
                                ( ap
                                  ( concat'
                                    ( refl)
                                    ( y-concat-Ω³
                                      ( z-concat-Ω³ β ζ)
                                      ( z-concat-Ω³ δ θ)))
                                  ( interchange-y-z-concat-Id³ α γ ε η))))
                            { x = ( ap
                                    ( concat
                                      ( z-concat-Ω³
                                        ( y-concat-Ω³ α γ)
                                        ( y-concat-Ω³ ε η))
                                      ( refl))
                                    ( inv right-unit)) ∙
                                  ( ap
                                    ( concat
                                      ( z-concat-Ω³
                                        ( y-concat-Ω³ α γ)
                                        ( y-concat-Ω³ ε η))
                                      ( refl))
                                    ( interchange-y-z-concat-Id³ β δ ζ θ))}
                            { y = ( ap
                                    ( concat
                                      ( z-concat-Ω³
                                        ( y-concat-Ω³ α γ)
                                        ( y-concat-Ω³ ε η))
                                      ( refl))
                                    ( interchange-y-z-concat-Ω³ β δ ζ θ))}
                            ( inv
                              ( ap-concat
                                ( concat
                                  ( z-concat-Ω³
                                    ( y-concat-Ω³ α γ)
                                    ( y-concat-Ω³ ε η))
                                  ( refl))
                                ( inv right-unit)
                                ( interchange-y-z-concat-Id³ β δ ζ θ)))) ∙
                          ( ( ap
                              ( concat
                                ( ap
                                  ( concat
                                    ( z-concat-Ω³
                                      ( y-concat-Ω³ α γ)
                                      ( y-concat-Ω³ ε η))
                                    ( refl))
                                  ( interchange-y-z-concat-Ω³ β δ ζ θ))
                                ( x-concat-Ω³
                                  ( y-concat-Ω³
                                    ( z-concat-Ω³ α ε)
                                    ( z-concat-Ω³ γ η))
                                  ( y-concat-Ω³
                                    ( z-concat-Ω³ β ζ)
                                    ( z-concat-Ω³ δ θ))))
                              { x = ( inv
                                      ( assoc
                                        ( z-concat-Ω³
                                          ( y-concat-Ω³ α γ)
                                          ( y-concat-Ω³ ε η))
                                        ( refl)
                                        ( y-concat-Ω³
                                          ( z-concat-Ω³ β ζ)
                                          ( z-concat-Ω³ δ θ)))) ∙
                                    ( ap
                                      ( concat'
                                        ( refl)
                                        ( y-concat-Ω³
                                          ( z-concat-Ω³ β ζ)
                                          ( z-concat-Ω³ δ θ)))
                                      ( interchange-y-z-concat-Id³ α γ ε η))}
                              { y = ap
                                    ( concat'
                                      ( refl)
                                      ( y-concat-Ω³
                                        ( z-concat-Ω³ β ζ)
                                        ( z-concat-Ω³ δ θ)))
                                    ( interchange-y-z-concat-Ω³ α γ ε η)}
                              ( ( ap
                                  ( concat'
                                    ( x-concat-Ω³
                                      ( z-concat-Ω³
                                        ( y-concat-Ω³ α γ)
                                        ( y-concat-Ω³ ε η))
                                      ( y-concat-Ω³
                                        ( z-concat-Ω³ β ζ)
                                        ( z-concat-Ω³ δ θ)))
                                    ( ap
                                      ( concat'
                                        ( refl)
                                        ( y-concat-Ω³
                                          ( z-concat-Ω³ β ζ)
                                          ( z-concat-Ω³ δ θ)))
                                      ( interchange-y-z-concat-Id³ α γ ε η)))
                                  ( unit-law-assoc-101'
                                    ( z-concat-Ω³
                                      ( y-concat-Ω³ α γ)
                                      ( y-concat-Ω³ ε η))
                                    ( y-concat-Ω³
                                      ( z-concat-Id³ β ζ)
                                      ( z-concat-Id³ δ θ)))) ∙
                                ( inv
                                  ( ap-concat
                                    ( concat'
                                      ( refl)
                                      ( y-concat-Ω³
                                        ( z-concat-Ω³ β ζ)
                                        ( z-concat-Ω³ δ θ)))
                                    ( inv right-unit)
                                    ( interchange-y-z-concat-Id³ α γ ε η))))) ∙
                            ( inv
                              ( triangle-ap-binary'
                                ( x-concat-Ω³)
                                ( interchange-y-z-concat-Ω³ α γ ε η)
                                ( interchange-y-z-concat-Ω³ β δ ζ θ)
                              )))))))))))))))

-- syllepsis

{-
syllepsis :
  {l : Level} {A : UU l} {a : A} (s t : type-Ω³ a) →
  Id (eckmann-hilton-Ω² s t ∙ eckmann-hilton-Ω² t s) refl-Ω³
syllepsis s t = {!!}
-}
