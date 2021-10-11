{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.interchange where

import book
open book public

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

{- Identity types of identity types -}

{- Binary equivalences and binary embeddings -}

fix-left :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  A → B → C
fix-left f a = f a

fix-right :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  B → A → C
fix-right f b a = f a b

is-binary-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (A → B → C) → UU (l1 ⊔ l2 ⊔ l3)
is-binary-equiv {A = A} {B = B} f =
  ((b : B) → is-equiv (fix-right f b)) × ((a : A) → is-equiv (fix-left f a))

is-equiv-fix-left :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  is-binary-equiv f → {a : A} → is-equiv (fix-left f a)
is-equiv-fix-left f H {a} = pr2 H a

is-emb-fix-left-is-binary-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  is-binary-equiv f → {a : A} → is-emb (fix-left f a)
is-emb-fix-left-is-binary-equiv f H {a} =
  is-emb-is-equiv (is-equiv-fix-left f H)

is-equiv-fix-right :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  is-binary-equiv f → {b : B} → is-equiv (fix-right f b)
is-equiv-fix-right f H {b} = pr1 H b

is-emb-fix-right-is-binary-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  is-binary-equiv f → {b : B} → is-emb (fix-right f b)
is-emb-fix-right-is-binary-equiv f H {b} =
  is-emb-is-equiv (is-equiv-fix-right f H)

is-binary-equiv-concat :
  {l : Level} {A : UU l} {x y z : A} →
  is-binary-equiv (λ (p : Id x y) (q : Id y z) → p ∙ q)
is-binary-equiv-concat {l} {A} {x} {y} {z} =
  pair (λ q → is-equiv-concat' x q) (λ p → is-equiv-concat p z)

is-binary-emb :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (A → B → C) → UU (l1 ⊔ l2 ⊔ l3)
is-binary-emb {A = A} {B = B} f =
  {x x' : A} {y y' : B} →
    is-binary-equiv (λ (p : Id x x') (q : Id y y') → ap-binary f p q)

is-binary-emb-is-binary-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  is-binary-equiv f → is-binary-emb f
is-binary-emb-is-binary-equiv f H {x} {x'} {y} {y'} =
  pair
    ( λ q →
      is-equiv-comp
        ( λ p → ap-binary f p q)
        ( concat' (f x y) (ap (fix-left f x') q))
        ( λ p → ap (fix-right f y) p)
        ( λ p → triangle-ap-binary f p q)
        ( is-emb-fix-right-is-binary-equiv f H x x')
        ( is-equiv-concat' (f x y) (ap (fix-left f x') q)))
    ( λ p →
      is-equiv-comp
        ( λ q → ap-binary f p q)
        ( concat (ap (fix-right f y) p) (f x' y'))
        ( λ q → ap (fix-left f x') q)
        ( λ q → triangle-ap-binary f p q)
        ( is-emb-fix-left-is-binary-equiv f H y y')
        ( is-equiv-concat (ap (fix-right f y) p) (f x' y')))

--------------------------------------------------------------------------------

{- Vertical and horizontal concatenation in identity types of identity types -}

vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} → Id p q → Id q r → Id p r
vertical-concat-Id² α β = α ∙ β

horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z} →
  Id p q → Id u v → Id (p ∙ u) (q ∙ v)
horizontal-concat-Id² α β = ap-binary (λ s t → s ∙ t) α β

-- both operations are binary equivalences

is-binary-equiv-vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} →
  is-binary-equiv (vertical-concat-Id² {l} {A} {x} {y} {p} {q} {r})
is-binary-equiv-vertical-concat-Id² = is-binary-equiv-concat

is-binary-equiv-horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z} →
  is-binary-equiv (horizontal-concat-Id² {l} {A} {x} {y} {z} {p} {q} {u} {v})
is-binary-equiv-horizontal-concat-Id² =
  is-binary-emb-is-binary-equiv (λ s t → s ∙ t) is-binary-equiv-concat

-- both operations satisfy unit laws

left-unit-law-vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} {β : Id p q} →
  Id (vertical-concat-Id² refl β) β
left-unit-law-vertical-concat-Id² = left-unit

right-unit-law-vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} {α : Id p q} →
  Id (vertical-concat-Id² α refl) α
right-unit-law-vertical-concat-Id² = right-unit

left-unit-law-horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p : Id x y} {u v : Id y z} (γ : Id u v) →
  Id (horizontal-concat-Id² (refl {x = p}) γ) (ap (concat p z) γ)
left-unit-law-horizontal-concat-Id² γ = left-unit-ap-binary (λ s t → s ∙ t) γ

right-unit-law-horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} (α : Id p q) {u : Id y z} →
  Id (horizontal-concat-Id² α (refl {x = u})) (ap (concat' x u) α)
right-unit-law-horizontal-concat-Id² α = right-unit-ap-binary (λ s t → s ∙ t) α

--------------------------------------------------------------------------------

{- Three ways to concatenate in triple identity types -}

{- We name the three concatenations of triple identity types x-, y-, and z-
   concatenation, after the standard names for the three axis in 3-dimensional
   space. -}

x-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} {α β γ : Id p q} →
  Id α β → Id β γ → Id α γ
x-concat-Id³ σ τ = vertical-concat-Id² σ τ

y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} {α β : Id p q}
  {γ δ : Id q r} → Id α β → Id γ δ → Id (α ∙ γ) (β ∙ δ)
y-concat-Id³ σ τ = horizontal-concat-Id² σ τ

z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z}
  {α β : Id p q} {γ δ : Id u v} →
  Id α β → Id γ δ → Id (horizontal-concat-Id² α γ) (horizontal-concat-Id² β δ)
z-concat-Id³ σ τ = ap-binary (λ s t → horizontal-concat-Id² s t) σ τ

-- All three operations satisfy unit laws

left-unit-law-x-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} {α β : Id p q} {σ : Id α β} →
  Id (x-concat-Id³ refl σ) σ
left-unit-law-x-concat-Id³ = left-unit-law-vertical-concat-Id²

right-unit-law-x-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} {α β : Id p q} {τ : Id α β} →
  Id (x-concat-Id³ τ refl) τ
right-unit-law-x-concat-Id³ = right-unit-law-vertical-concat-Id²

left-unit-law-y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} {α : Id p q} {γ δ : Id q r}
  {τ : Id γ δ} → Id (y-concat-Id³ (refl {x = α}) τ) (ap (concat α r) τ)
left-unit-law-y-concat-Id³ {τ = τ} = left-unit-law-horizontal-concat-Id² τ

right-unit-law-y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} {α β : Id p q} {γ : Id q r}
  {σ : Id α β} → Id (y-concat-Id³ σ (refl {x = γ})) (ap (concat' p γ) σ)
right-unit-law-y-concat-Id³ {σ = σ} = right-unit-law-horizontal-concat-Id² σ

left-unit-law-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z}
  {α : Id p q} {γ δ : Id u v} (τ : Id γ δ) →
  Id (z-concat-Id³ (refl {x = α}) τ) (ap (horizontal-concat-Id² α) τ)
left-unit-law-z-concat-Id³ τ =
  left-unit-ap-binary (λ s t → horizontal-concat-Id² s t) τ

right-unit-law-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z}
  {α β : Id p q} {γ : Id u v} (σ : Id α β) →
  Id (z-concat-Id³ σ (refl {x = γ})) (ap (λ ω → horizontal-concat-Id² ω γ) σ)
right-unit-law-z-concat-Id³ σ =
  right-unit-ap-binary (λ s t → horizontal-concat-Id² s t) σ

--------------------------------------------------------------------------------

{- Four ways to concatenatie in quadruple identity types -}

{- We name the three non-standard concatenations in quadruple identity types
   i-, j-, and k-concatenation, after the standard names for the quaternions
   i, j, and k. -}

concat-Id⁴ :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} {α β : Id p q}
  {r s t : Id α β} → Id r s → Id s t → Id r t
concat-Id⁴ σ τ = x-concat-Id³ σ τ

i-concat-Id⁴ :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} {α β γ : Id p q} →
  {s s' : Id α β} (σ : Id s s') {t t' : Id β γ} (τ : Id t t') →
  Id (x-concat-Id³ s t) (x-concat-Id³ s' t')
i-concat-Id⁴ σ τ = y-concat-Id³ σ τ

j-concat-Id⁴ :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} {α β : Id p q}
  {γ δ : Id q r} {s s' : Id α β} (σ : Id s s') {t t' : Id γ δ} (τ : Id t t') →
  Id (y-concat-Id³ s t) (y-concat-Id³ s' t')
j-concat-Id⁴ σ τ = z-concat-Id³ σ τ

k-concat-Id⁴ :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z}
  {α β : Id p q} {γ δ : Id u v} {s s' : Id α β} (σ : Id s s') {t t' : Id γ δ}
  (τ : Id t t') → Id (z-concat-Id³ s t) (z-concat-Id³ s' t')
k-concat-Id⁴ σ τ = ap-binary (λ m n → z-concat-Id³ m n) σ τ

--------------------------------------------------------------------------------

{- The interchange law at the level of identity types of identity types -}

interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q r : Id x y} {u v w : Id y z}
  (α : Id p q) (β : Id q r) (γ : Id u v) (δ : Id v w) →
  Id ( horizontal-concat-Id²
       ( vertical-concat-Id² α β)
       ( vertical-concat-Id² γ δ))
     ( vertical-concat-Id²
       ( horizontal-concat-Id² α γ)
       ( horizontal-concat-Id² β δ))
interchange-Id² refl refl refl refl = refl

unit-law-α-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} (α : Id p q) (u : Id y z) →
  Id ( ( interchange-Id² α refl (refl {x = u}) refl) ∙
       ( right-unit ∙ right-unit-law-horizontal-concat-Id² α))
     ( ( right-unit-law-horizontal-concat-Id² (α ∙ refl)) ∙
       ( ap (ap (concat' x u)) right-unit))
unit-law-α-interchange-Id² refl u = refl

unit-law-β-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} (β : Id p q) (u : Id y z) →
  Id ( interchange-Id² refl β (refl {x = u}) refl) refl
unit-law-β-interchange-Id² refl u = refl

unit-law-γ-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} (p : Id x y) {u v : Id y z} (γ : Id u v) →
  Id ( ( interchange-Id² (refl {x = p}) refl γ refl) ∙
       ( right-unit ∙ left-unit-law-horizontal-concat-Id² γ))
     ( ( left-unit-law-horizontal-concat-Id² (γ ∙ refl)) ∙
       ( ap (ap (concat p z)) right-unit))
unit-law-γ-interchange-Id² p refl = refl

unit-law-δ-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} (p : Id x y) {u v : Id y z} (δ : Id u v) →
  Id ( interchange-Id² (refl {x = p}) refl refl δ) refl
unit-law-δ-interchange-Id² p refl = refl

--------------------------------------------------------------------------------

{- The double loop space -}

vertical-concat-Ω² :
  {l : Level} {A : UU l} {a : A} → type-Ω² a → type-Ω² a → type-Ω² a
vertical-concat-Ω² α β = vertical-concat-Id² α β

horizontal-concat-Ω² :
  {l : Level} {A : UU l} {a : A} → type-Ω² a → type-Ω² a → type-Ω² a
horizontal-concat-Ω² α β = horizontal-concat-Id² α β

left-unit-law-vertical-concat-Ω² :
  {l : Level} {A : UU l} {a : A} {α : type-Ω² a} →
  Id (vertical-concat-Ω² refl-Ω² α) α
left-unit-law-vertical-concat-Ω² = left-unit

right-unit-law-vertical-concat-Ω² :
  {l : Level} {A : UU l} {a : A} {α : type-Ω² a} →
  Id (vertical-concat-Ω² α refl-Ω²) α
right-unit-law-vertical-concat-Ω² = right-unit

left-unit-law-horizontal-concat-Ω² :
  {l : Level} {A : UU l} {a : A} {α : type-Ω² a} →
  Id (horizontal-concat-Ω² refl-Ω² α) α
left-unit-law-horizontal-concat-Ω² {α = α} =
  ( left-unit-law-horizontal-concat-Id² α) ∙ (ap-id α)

naturality-right-unit :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} (α : Id p q) →
  Id (ap (concat' x refl) α ∙ right-unit) (right-unit ∙ α)
naturality-right-unit {p = refl} refl = refl

naturality-right-unit-Ω² :
  {l : Level} {A : UU l} {x : A} (α :  type-Ω² x) →
  Id (ap (concat' x refl) α) α
naturality-right-unit-Ω² α = inv right-unit ∙ naturality-right-unit α

right-unit-law-horizontal-concat-Ω² :
  {l : Level} {A : UU l} {a : A} {α : type-Ω² a} →
  Id (horizontal-concat-Ω² α refl-Ω²) α
right-unit-law-horizontal-concat-Ω² {α = α} =
  ( right-unit-law-horizontal-concat-Id² α) ∙ (naturality-right-unit-Ω² α)

interchange-Ω² :
  {l : Level} {A : UU l} {a : A} (α β γ δ : type-Ω² a) →
  Id ( horizontal-concat-Ω² (vertical-concat-Ω² α β) (vertical-concat-Ω² γ δ))
     ( vertical-concat-Ω² (horizontal-concat-Ω² α γ) (horizontal-concat-Ω² β δ))
interchange-Ω² α β γ δ = interchange-Id² α β γ δ

outer-eckmann-hilton-connection-Ω² :
  {l : Level} {A : UU l} {a : A} (α δ : type-Ω² a) →
  Id (horizontal-concat-Ω² α δ) (vertical-concat-Ω² α δ)
outer-eckmann-hilton-connection-Ω² α δ =
  ( z-concat-Id³ (inv right-unit) (inv left-unit)) ∙
  ( ( interchange-Ω² α refl refl δ) ∙
    ( y-concat-Id³
      ( right-unit-law-horizontal-concat-Ω² {α = α})
      ( left-unit-law-horizontal-concat-Ω² {α = δ})))

inner-eckmann-hilton-connection-Ω² :
  {l : Level} {A : UU l} {a : A} (β γ : type-Ω² a) →
  Id ( horizontal-concat-Ω² β γ) (vertical-concat-Ω² γ β)
inner-eckmann-hilton-connection-Ω² β γ =
  ( z-concat-Id³ (inv left-unit) (inv right-unit)) ∙
  ( ( interchange-Ω² refl β γ refl) ∙
    ( y-concat-Id³
      ( left-unit-law-horizontal-concat-Ω² {α = γ})
      ( right-unit-law-horizontal-concat-Ω² {α = β})))

eckmann-hilton-Ω² :
  {l : Level} {A : UU l} {a : A} (α β : type-Ω² a) →
  Id (α ∙ β) (β ∙ α)
eckmann-hilton-Ω² α β =
  ( inv (outer-eckmann-hilton-connection-Ω² α β)) ∙
  ( inner-eckmann-hilton-connection-Ω² α β)

--------------------------------------------------------------------------------

-- Identity types of identity types of identity types

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

--------------------------------------------------------------------------------

-- Triple loop spaces

x-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} → type-Ω³ a → type-Ω³ a → type-Ω³ a
x-concat-Ω³ = x-concat-Id³

y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} → type-Ω³ a → type-Ω³ a → type-Ω³ a
y-concat-Ω³ = y-concat-Id³

z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} → type-Ω³ a → type-Ω³ a → type-Ω³ a
z-concat-Ω³ = z-concat-Id³

ap-x-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} {α α' β β' : type-Ω³ a}
  (s : Id α α') (t : Id β β') → Id (x-concat-Ω³ α β) (x-concat-Ω³ α' β')
ap-x-concat-Ω³ s t = ap-binary x-concat-Ω³ s t

ap-y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} {α α' β β' : type-Ω³ a}
  (s : Id α α') (t : Id β β') → Id (y-concat-Ω³ α β) (y-concat-Ω³ α' β')
ap-y-concat-Ω³ s t = j-concat-Id⁴ s t

ap-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} {α α' β β' : type-Ω³ a}
  (s : Id α α') (t : Id β β') → Id (z-concat-Ω³ α β) (z-concat-Ω³ α' β')
ap-z-concat-Ω³ s t = k-concat-Id⁴ s t

-- The unit laws for the three concatenations on Ω³

left-unit-law-x-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α : type-Ω³ a) →
  Id (x-concat-Ω³ refl-Ω³ α) α
left-unit-law-x-concat-Ω³ α = left-unit

right-unit-law-x-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α : type-Ω³ a) →
  Id (x-concat-Ω³ α refl-Ω³) α
right-unit-law-x-concat-Ω³ α = right-unit

left-unit-law-y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α : type-Ω³ a) →
  Id (y-concat-Ω³ refl-Ω³ α) α
left-unit-law-y-concat-Ω³ α = left-unit-law-horizontal-concat-Ω²

right-unit-law-y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α : type-Ω³ a) →
  Id (y-concat-Ω³ α refl-Ω³) α
right-unit-law-y-concat-Ω³ α = right-unit-law-horizontal-concat-Ω²

left-unit-law-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α : type-Ω³ a) →
  Id (z-concat-Ω³ refl-Ω³ α) α
left-unit-law-z-concat-Ω³ α =
  ( left-unit-law-z-concat-Id³ α) ∙
  ( ( inv right-unit) ∙
    ( ( inv (htpy-nat (λ ω → left-unit-law-horizontal-concat-Id² ω) α)) ∙
      ( ( inv right-unit) ∙
        ( ( inv (htpy-nat ap-id α)) ∙
          ( ap-id α)))))

{-
super-naturality-right-unit :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {α β : Id p q} (γ : Id α β)
  (u : Id y z) →
  Id (ap (λ ω → horizontal-concat-Id² ω (refl {x = u})) γ) {!!}
super-naturality-right-unit α = {!!}
-}

right-unit-law-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α : type-Ω³ a) →
  Id (z-concat-Ω³ α refl-Ω³) α
right-unit-law-z-concat-Ω³ α =
  ( right-unit-law-z-concat-Id³ α) ∙
  {!!}
{-
  ( ( inv right-unit) ∙
    ( ( inv (htpy-nat (λ ω → right-unit-law-horizontal-concat-Id² ω) α)) ∙
      ( left-unit ∙
        ( ( inv right-unit) ∙
          ( ( inv
              ( htpy-nat
                ( λ z →
                  ( inv right-unit) ∙
                  ( ( inv (htpy-nat (λ ω → right-unit) z)) ∙ ( ap-id z))) α)) ∙
            ( ap-id α))))))
-}

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

-- The Eckmann-Hilton connections in Ω³

outer-eckmann-hilton-connection-x-y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α δ : type-Ω³ a) →
  Id (y-concat-Ω³ α δ) (x-concat-Ω³ α δ)
outer-eckmann-hilton-connection-x-y-concat-Ω³ α δ =
  ( j-concat-Id⁴
    ( inv (right-unit-law-x-concat-Ω³ α))
    ( inv (left-unit-law-x-concat-Ω³ δ))) ∙
  ( ( interchange-x-y-concat-Ω³ α refl refl δ) ∙
    ( i-concat-Id⁴
      ( right-unit-law-y-concat-Ω³ α)
      ( left-unit-law-y-concat-Ω³ δ)))

inner-eckmann-hilton-connection-x-y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (β γ : type-Ω³ a) →
  Id (y-concat-Ω³ β γ) (x-concat-Ω³ γ β)
inner-eckmann-hilton-connection-x-y-concat-Ω³ β γ =
  ( j-concat-Id⁴
    ( inv (left-unit-law-x-concat-Ω³ β))
    ( inv (right-unit-law-x-concat-Ω³ γ))) ∙
  ( ( interchange-x-y-concat-Ω³ refl β γ refl) ∙
    ( i-concat-Id⁴
      ( left-unit-law-y-concat-Ω³ γ)
      ( right-unit-law-y-concat-Ω³ β)))

outer-eckmann-hilton-connection-x-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α δ : type-Ω³ a) →
  Id (z-concat-Ω³ α δ) (x-concat-Ω³ α δ)
outer-eckmann-hilton-connection-x-z-concat-Ω³ α δ =
  ( k-concat-Id⁴
    ( inv (right-unit-law-x-concat-Ω³ α))
    ( inv (left-unit-law-x-concat-Ω³ δ))) ∙
  ( ( interchange-x-z-concat-Ω³ α refl refl δ) ∙
    ( i-concat-Id⁴
      ( right-unit-law-z-concat-Ω³ α)
      ( left-unit-law-z-concat-Ω³ δ)))

inner-eckmann-hilton-connection-x-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (β γ : type-Ω³ a) →
  Id (z-concat-Ω³ β γ) (x-concat-Ω³ γ β)
inner-eckmann-hilton-connection-x-z-concat-Ω³ β γ =
  ( k-concat-Id⁴
    ( inv (left-unit-law-x-concat-Ω³ β))
    ( inv (right-unit-law-x-concat-Ω³ γ))) ∙
  ( ( interchange-x-z-concat-Ω³ refl β γ refl) ∙
    ( i-concat-Id⁴
      ( left-unit-law-z-concat-Ω³ γ)
      ( right-unit-law-z-concat-Ω³ β)))

outer-eckmann-hilton-connection-y-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α δ : type-Ω³ a) →
  Id (z-concat-Ω³ α δ) (y-concat-Ω³ α δ)
outer-eckmann-hilton-connection-y-z-concat-Ω³ α δ = 
  ( k-concat-Id⁴
    ( inv (right-unit-law-y-concat-Ω³ α))
    ( inv (left-unit-law-y-concat-Ω³ δ))) ∙
  ( ( interchange-y-z-concat-Ω³ α refl refl δ) ∙
    ( j-concat-Id⁴
      ( right-unit-law-z-concat-Ω³ α)
      ( left-unit-law-z-concat-Ω³ δ)))

inner-eckmann-hilton-connection-y-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (β γ : type-Ω³ a) →
  Id (z-concat-Ω³ β γ) (y-concat-Ω³ γ β)
inner-eckmann-hilton-connection-y-z-concat-Ω³ β γ =
  ( k-concat-Id⁴
    ( inv (left-unit-law-y-concat-Ω³ β))
    ( inv (right-unit-law-y-concat-Ω³ γ))) ∙
  ( ( interchange-y-z-concat-Ω³ refl β γ refl) ∙
    ( j-concat-Id⁴
      ( left-unit-law-z-concat-Ω³ γ)
      ( right-unit-law-z-concat-Ω³ β)))

--------------------------------------------------------------------------------
