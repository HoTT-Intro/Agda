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
ap-vertical-concat refl refl = refl

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
ap-horizontal-concat refl refl = refl

interchange-concat :
  {l : Level} {A : UU l} {x y z : A} {p q r : Id x y} {u v w : Id y z}
  (α : Id p q) (β : Id q r) (γ : Id u v) (δ : Id v w) →
  Id ( horizontal-concat (vertical-concat α β) (vertical-concat γ δ))
     ( vertical-concat (horizontal-concat α γ) (horizontal-concat β δ))
interchange-concat refl refl refl refl = refl

--------------------------------------------------------------------------------

{- The double loop space -}

Ω² : {l : Level} {A : UU l} (a : A) → UU l
Ω² a = Id (refl {x = a}) (refl {x = a})

vertical-concat-Ω² :
  {l : Level} {A : UU l} {a : A} → Ω² a → Ω² a → Ω² a
vertical-concat-Ω² α β = vertical-concat α β

refl-Ω² : {l : Level} {A : UU l} {a : A} → Ω² a
refl-Ω² {l} {A} {a} = refl

left-unit-law-vertical-concat-Ω² :
  {l : Level} {A : UU l} {a : A} {α : Ω² a} →
  Id (vertical-concat-Ω² refl-Ω² α) α
left-unit-law-vertical-concat-Ω² = left-unit

right-unit-law-vertical-concat-Ω² :
  {l : Level} {A : UU l} {a : A} {α : Ω² a} →
  Id (vertical-concat-Ω² α refl-Ω²) α
right-unit-law-vertical-concat-Ω² = right-unit

horizontal-concat-Ω² :
  {l : Level} {A : UU l} {a : A} → Ω² a → Ω² a → Ω² a
horizontal-concat-Ω² α β = horizontal-concat α β

left-unit-law-horizontal-concat-Ω² :
  {l : Level} {A : UU l} {a : A} {α : Ω² a} →
  Id (horizontal-concat-Ω² refl-Ω² α) α
left-unit-law-horizontal-concat-Ω² {α = α} =
  ( left-unit-law-horizontal-concat α) ∙ (ap-id α)

right-unit-law-horizontal-concat-Ω² :
  {l : Level} {A : UU l} {a : A} {α : Ω² a} →
  Id (horizontal-concat-Ω² α refl-Ω²) α
right-unit-law-horizontal-concat-Ω² {α = α} =
  ( right-unit-law-horizontal-concat α) ∙
  ( ( inv right-unit) ∙
    ( ( inv (htpy-nat {g = id} (λ t → right-unit) α)) ∙
      ( ap (concat right-unit refl) (ap-id α))))

eckmann-hilton-Ω² :
  {l : Level} {A : UU l} {x : A} (α β : Id (refl {x = x}) (refl {x = x})) →
  Id (α ∙ β) (β ∙ α)
eckmann-hilton-Ω² α β =
  ( ap-vertical-concat
    ( inv (right-unit-law-horizontal-concat-Ω² {α = α}))
    ( inv left-unit-law-horizontal-concat-Ω²)) ∙
  ( ( inv (interchange-concat α refl-Ω² refl-Ω² β)) ∙
    ( ( ap-horizontal-concat right-unit (inv right-unit)) ∙
      ( ( interchange-concat refl-Ω² α β refl-Ω²) ∙
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
interchange-x-y-concat-Id³ = interchange-concat

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
       ( interchange-concat β δ ζ θ))
     ( ( interchange-concat α γ ε η) ∙
       ( y-concat-Id³ (z-concat-Id³ σ υ) (z-concat-Id³ τ ϕ)))
interchange-y-z-concat-Id³ refl refl refl refl = inv right-unit

--------------------------------------------------------------------------------

-- Triple loop spaces

Ω³ : {l : Level} {A : UU l} → A → UU l
Ω³ a = Ω² (refl {x = a})

refl-Ω³ : {l : Level} {A : UU l} (a : A) → Ω³ a
refl-Ω³ a = refl-Ω² {a = refl}

x-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} → Ω³ a → Ω³ a → Ω³ a
x-concat-Ω³ = x-concat-Id³

y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} → Ω³ a → Ω³ a → Ω³ a
y-concat-Ω³ = y-concat-Id³

z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} → Ω³ a → Ω³ a → Ω³ a
z-concat-Ω³ = z-concat-Id³
