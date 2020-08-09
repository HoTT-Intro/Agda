{-# OPTIONS --without-K --exact-split #-}

module W-types where

import 17-number-theory
open 17-number-theory public

module Container {l1 l2 : Level} (A : UU l1) (B : A → UU l2) where

  data 𝕎 : UU (l1 ⊔ l2) where
    sup-𝕎 : (x : A) (α : B x → 𝕎) → 𝕎

  Eq-𝕎 :
    𝕎 → 𝕎 → UU (l1 ⊔ l2)
  Eq-𝕎 (sup-𝕎 x α) (sup-𝕎 y β) =
    Σ (Id x y) (λ p → (z : B x) → Eq-𝕎 (α z) (β (tr B p z))) 

  refl-Eq-𝕎 :
    (w : 𝕎) → Eq-𝕎 w w
  refl-Eq-𝕎 (sup-𝕎 x α) = pair refl (λ z → refl-Eq-𝕎 (α z))

  center-total-Eq-𝕎 :
    (w : 𝕎) → Σ 𝕎 (Eq-𝕎 w)
  center-total-Eq-𝕎 w = pair w (refl-Eq-𝕎 w)

  aux-total-Eq-𝕎 :
    (x : A) (α : B x → 𝕎) →
    Σ (B x → 𝕎) (λ β → (y : B x) → Eq-𝕎 (α y) (β y)) →
    Σ 𝕎 (Eq-𝕎 (sup-𝕎 x α))
  aux-total-Eq-𝕎 x α (pair β e) = pair (sup-𝕎 x β) (pair refl e)

  contraction-total-Eq-𝕎 :
    (w : 𝕎) (t : Σ 𝕎 (Eq-𝕎 w)) → Id (center-total-Eq-𝕎 w) t
  contraction-total-Eq-𝕎
    ( sup-𝕎 x α) (pair (sup-𝕎 .x β) (pair refl e)) =
    ap ( ( aux-total-Eq-𝕎 x α) ∘
         ( choice-∞ {A = B x} {B = λ y → 𝕎} {C = λ y → Eq-𝕎 (α y)}))
       { x = λ y → pair (α y) (refl-Eq-𝕎 (α y))}
       { y = λ y → pair (β y) (e y)}
       ( eq-htpy (λ y → contraction-total-Eq-𝕎 (α y) (pair (β y) (e y))))

  is-contr-total-Eq-𝕎 :
    (w : 𝕎) → is-contr (Σ 𝕎 (Eq-𝕎 w))
  is-contr-total-Eq-𝕎 w =
    pair
      ( center-total-Eq-𝕎 w)
      ( contraction-total-Eq-𝕎 w)

  Eq-𝕎-eq :
    (v w : 𝕎) → Id v w → Eq-𝕎 v w
  Eq-𝕎-eq v .v refl = refl-Eq-𝕎 v

  is-equiv-Eq-𝕎-eq :
    (v w : 𝕎) → is-equiv (Eq-𝕎-eq v w)
  is-equiv-Eq-𝕎-eq v =
    fundamental-theorem-id v
      ( refl-Eq-𝕎 v)
      ( is-contr-total-Eq-𝕎 v)
      ( Eq-𝕎-eq v)
  
  is-trunc-𝕎 :
    (k : 𝕋) → is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) 𝕎
  is-trunc-𝕎 k is-trunc-A (sup-𝕎 x α) (sup-𝕎 y β) =
    is-trunc-is-equiv k
      ( Eq-𝕎 (sup-𝕎 x α) (sup-𝕎 y β))
      ( Eq-𝕎-eq (sup-𝕎 x α) (sup-𝕎 y β))
      ( is-equiv-Eq-𝕎-eq (sup-𝕎 x α) (sup-𝕎 y β))
      ( is-trunc-Σ k
        ( is-trunc-A x y)
        ( λ p → is-trunc-Π k
          ( λ z →
            is-trunc-is-equiv' k
            ( Id (α z) (β (tr B p z)))
            ( Eq-𝕎-eq (α z) (β (tr B p z)))
            ( is-equiv-Eq-𝕎-eq (α z) (β (tr B p z)))
            ( is-trunc-𝕎 k is-trunc-A (α z) (β (tr B p z))))))
  
  ------------------------------------------------------------------------------
  
  -- W-types as initial algebras

  type-polynomial-endofunctor :
    {l : Level} → UU l → UU (l ⊔ l1 ⊔ l2)
  type-polynomial-endofunctor X = Σ A (λ x → B x → X)

  -- We characterize the identity type of type-polynomial-endofunctor

  Eq-type-polynomial-endofunctor :
    {l : Level} (X : UU l) →
    (x y : type-polynomial-endofunctor X) → UU (l ⊔ l1 ⊔ l2)
  Eq-type-polynomial-endofunctor X x y =
    Σ (Id (pr1 x) (pr1 y)) (λ p → (pr2 x) ~ ((pr2 y) ∘ (tr B p)))

  refl-Eq-type-polynomial-endofunctor :
    {l : Level} (X : UU l) (x : type-polynomial-endofunctor X) →
    Eq-type-polynomial-endofunctor X x x
  refl-Eq-type-polynomial-endofunctor X (pair x α) = pair refl refl-htpy

  is-contr-total-Eq-type-polynomial-endofunctor :
    {l : Level} (X : UU l) (x : type-polynomial-endofunctor X) →
    is-contr
      ( Σ ( type-polynomial-endofunctor X)
          ( Eq-type-polynomial-endofunctor X x))
  is-contr-total-Eq-type-polynomial-endofunctor X (pair x α) =
    is-contr-total-Eq-structure
      ( ( λ (y : A) (β : B y → X) (p : Id x y) → α ~ (β ∘ tr B p)))
      ( is-contr-total-path x)
      ( pair x refl)
      ( is-contr-total-htpy α)

  Eq-type-polynomial-endofunctor-eq :
    {l : Level} (X : UU l) (x y : type-polynomial-endofunctor X) →
    Id x y → Eq-type-polynomial-endofunctor X x y
  Eq-type-polynomial-endofunctor-eq X x .x refl =
    refl-Eq-type-polynomial-endofunctor X x

  is-equiv-Eq-type-polynomial-endofunctor-eq :
    {l : Level} (X : UU l) (x y : type-polynomial-endofunctor X) →
    is-equiv (Eq-type-polynomial-endofunctor-eq X x y)
  is-equiv-Eq-type-polynomial-endofunctor-eq X x =
    fundamental-theorem-id x
      ( refl-Eq-type-polynomial-endofunctor X x)
      ( is-contr-total-Eq-type-polynomial-endofunctor X x)
      ( Eq-type-polynomial-endofunctor-eq X x)

  eq-Eq-type-polynomial-endofunctor :
    {l : Level} (X : UU l) (x y : type-polynomial-endofunctor X) →
    Eq-type-polynomial-endofunctor X x y → Id x y
  eq-Eq-type-polynomial-endofunctor X x y =
    inv-is-equiv (is-equiv-Eq-type-polynomial-endofunctor-eq X x y)

  isretr-eq-Eq-type-polynomial-endofunctor :
    {l : Level} (X : UU l) (x y : type-polynomial-endofunctor X) →
    ( ( eq-Eq-type-polynomial-endofunctor X x y) ∘
      ( Eq-type-polynomial-endofunctor-eq X x y)) ~ id
  isretr-eq-Eq-type-polynomial-endofunctor X x y =
    isretr-inv-is-equiv (is-equiv-Eq-type-polynomial-endofunctor-eq X x y)

  coh-refl-eq-Eq-type-polynomial-endofunctor :
    {l : Level} (X : UU l) (x : type-polynomial-endofunctor X) →
    Id ( eq-Eq-type-polynomial-endofunctor X x x
         ( refl-Eq-type-polynomial-endofunctor X x)) refl
  coh-refl-eq-Eq-type-polynomial-endofunctor X x =
    isretr-eq-Eq-type-polynomial-endofunctor X x x refl

  -- The action on morphisms of the polynomial endofunctor
  
  map-polynomial-endofunctor :
    {l3 l4 : Level} {X : UU l3} {Y : UU l4} (f : X → Y) →
    type-polynomial-endofunctor X → type-polynomial-endofunctor Y
  map-polynomial-endofunctor f (pair x α) = pair x (f ∘ α)

  -- The action on homotopies of the polynomial endofunctor
  
  htpy-polynomial-endofunctor :
    {l3 l4 : Level} {X : UU l3} {Y : UU l4} {f g : X → Y} →
    f ~ g → map-polynomial-endofunctor f ~ map-polynomial-endofunctor g
  htpy-polynomial-endofunctor {X = X} {Y} {f} {g} H (pair x α) =
    eq-Eq-type-polynomial-endofunctor Y
      ( map-polynomial-endofunctor f (pair x α))
      ( map-polynomial-endofunctor g (pair x α))
      ( pair refl (H ·r α))
  
  coh-refl-htpy-polynomial-endofunctor :
    {l3 l4 : Level} {X : UU l3} {Y : UU l4} (f : X → Y) →
    htpy-polynomial-endofunctor (refl-htpy {f = f}) ~ refl-htpy
  coh-refl-htpy-polynomial-endofunctor {X = X} {Y} f (pair x α) =
    coh-refl-eq-Eq-type-polynomial-endofunctor Y
      ( map-polynomial-endofunctor f (pair x α)) 

  -- algebras for the polynomial endofunctors
  
  algebra-polynomial-endofunctor :
    (l : Level) → UU (lsuc l ⊔ l1 ⊔ l2)
  algebra-polynomial-endofunctor l =
    Σ (UU l) (λ X → type-polynomial-endofunctor X → X)

  type-algebra-polynomial-endofunctor :
    {l : Level} → algebra-polynomial-endofunctor l → UU l
  type-algebra-polynomial-endofunctor X = pr1 X

  structure-algebra-polynomial-endofunctor :
    {l : Level} (X : algebra-polynomial-endofunctor l) →
    type-polynomial-endofunctor (type-algebra-polynomial-endofunctor X) →
    type-algebra-polynomial-endofunctor X
  structure-algebra-polynomial-endofunctor X = pr2 X

  -- W-types are algebras for polynomial endofunctors
  
  structure-𝕎-Alg : type-polynomial-endofunctor 𝕎 → 𝕎
  structure-𝕎-Alg (pair x α) = sup-𝕎 x α

  𝕎-Alg : algebra-polynomial-endofunctor (l1 ⊔ l2)
  𝕎-Alg = pair 𝕎 structure-𝕎-Alg

  -- Morphisms of algebras for polynomial endofunctors
  
  hom-algebra-polynomial-endofunctor :
    {l3 l4 : Level} (X : algebra-polynomial-endofunctor l3) →
    (Y : algebra-polynomial-endofunctor l4) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-algebra-polynomial-endofunctor X Y =
    Σ ( type-algebra-polynomial-endofunctor X →
        type-algebra-polynomial-endofunctor Y)
      ( λ f →
        ( f ∘ (structure-algebra-polynomial-endofunctor X)) ~
        ( ( structure-algebra-polynomial-endofunctor Y) ∘
          ( map-polynomial-endofunctor f)))

  map-hom-algebra-polynomial-endofunctor :
    {l3 l4 : Level} (X : algebra-polynomial-endofunctor l3) →
    (Y : algebra-polynomial-endofunctor l4) →
    hom-algebra-polynomial-endofunctor X Y →
    type-algebra-polynomial-endofunctor X →
    type-algebra-polynomial-endofunctor Y
  map-hom-algebra-polynomial-endofunctor X Y f = pr1 f

  structure-hom-algebra-polynomial-endofunctor :
    {l3 l4 : Level} (X : algebra-polynomial-endofunctor l3) →
    (Y : algebra-polynomial-endofunctor l4) →
    (f : hom-algebra-polynomial-endofunctor X Y) →
    ( ( map-hom-algebra-polynomial-endofunctor X Y f) ∘
      ( structure-algebra-polynomial-endofunctor X)) ~
    ( ( structure-algebra-polynomial-endofunctor Y) ∘
      ( map-polynomial-endofunctor
        ( map-hom-algebra-polynomial-endofunctor X Y f)))
  structure-hom-algebra-polynomial-endofunctor X Y f = pr2 f

  -- We characterize the identity type of the type of morphisms of algebras

  htpy-hom-algebra-polynomial-endofunctor :
    {l3 l4 : Level} (X : algebra-polynomial-endofunctor l3) →
    (Y : algebra-polynomial-endofunctor l4) →
    (f g : hom-algebra-polynomial-endofunctor X Y) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-algebra-polynomial-endofunctor X Y f g =
    Σ ( map-hom-algebra-polynomial-endofunctor X Y f ~
        map-hom-algebra-polynomial-endofunctor X Y g)
      ( λ H →
        ( ( structure-hom-algebra-polynomial-endofunctor X Y f) ∙h
          ( ( structure-algebra-polynomial-endofunctor Y) ·l
            ( htpy-polynomial-endofunctor H))) ~
        ( ( H ·r structure-algebra-polynomial-endofunctor X) ∙h
          ( structure-hom-algebra-polynomial-endofunctor X Y g)))

  refl-htpy-hom-algebra-polynomial-endofunctor :
    {l3 l4 : Level} (X : algebra-polynomial-endofunctor l3) →
    (Y : algebra-polynomial-endofunctor l4) →
    (f : hom-algebra-polynomial-endofunctor X Y) →
    htpy-hom-algebra-polynomial-endofunctor X Y f f
  refl-htpy-hom-algebra-polynomial-endofunctor X Y f =
    pair refl-htpy
      ( λ z →
        ( ap ( λ t →
               concat
                 ( structure-hom-algebra-polynomial-endofunctor X Y f z)
                 ( structure-algebra-polynomial-endofunctor Y
                   ( map-polynomial-endofunctor
                     ( map-hom-algebra-polynomial-endofunctor X Y f) z) )
                 ( ap (structure-algebra-polynomial-endofunctor Y ) t))
             ( coh-refl-htpy-polynomial-endofunctor
               ( map-hom-algebra-polynomial-endofunctor X Y f) z)) ∙
        ( right-unit))
  
  htpy-hom-algebra-polynomial-endofunctor-eq :
    {l3 l4 : Level} (X : algebra-polynomial-endofunctor l3) →
    (Y : algebra-polynomial-endofunctor l4) →
    (f g : hom-algebra-polynomial-endofunctor X Y) →
    Id f g → htpy-hom-algebra-polynomial-endofunctor X Y f g
  htpy-hom-algebra-polynomial-endofunctor-eq X Y f .f refl =
    refl-htpy-hom-algebra-polynomial-endofunctor X Y f

  is-contr-total-htpy-hom-algebra-polynomial-endofunctor :
    {l3 l4 : Level} (X : algebra-polynomial-endofunctor l3) →
    (Y : algebra-polynomial-endofunctor l4) →
    (f : hom-algebra-polynomial-endofunctor X Y) →
    is-contr
      ( Σ ( hom-algebra-polynomial-endofunctor X Y)
          ( htpy-hom-algebra-polynomial-endofunctor X Y f))
  is-contr-total-htpy-hom-algebra-polynomial-endofunctor X Y f =
    is-contr-total-Eq-structure
      ( λ ( g : pr1 X → pr1 Y)
          ( G : (g ∘ pr2 X) ~ ((pr2 Y) ∘ (map-polynomial-endofunctor g)))
          ( H : map-hom-algebra-polynomial-endofunctor X Y f ~ g) →
          ( ( structure-hom-algebra-polynomial-endofunctor X Y f) ∙h
            ( ( structure-algebra-polynomial-endofunctor Y) ·l
              ( htpy-polynomial-endofunctor H))) ~
          ( ( H ·r structure-algebra-polynomial-endofunctor X) ∙h G))
      ( is-contr-total-htpy (map-hom-algebra-polynomial-endofunctor X Y f))
      ( pair (map-hom-algebra-polynomial-endofunctor X Y f) refl-htpy)
      ( is-contr-equiv'
        ( Σ ( ( (pr1 f) ∘ pr2 X) ~
              ( pr2 Y ∘ map-polynomial-endofunctor (pr1 f)))
            ( λ H → (pr2 f) ~ H))
        ( equiv-tot
          ( λ H →
            ( equiv-htpy-concat
              ( λ x →
                ap ( concat
                     ( pr2 f x)
                     ( structure-algebra-polynomial-endofunctor Y
                       ( map-polynomial-endofunctor (pr1 f) x)))
                   ( ap ( ap (pr2 Y))
                        ( coh-refl-htpy-polynomial-endofunctor (pr1 f) x)))
              ( H)) ∘e
            ( equiv-htpy-concat htpy-right-unit H)))
        ( is-contr-total-htpy (pr2 f)))

  is-equiv-htpy-hom-algebra-polynomial-endofunctor-eq :
    {l3 l4 : Level} (X : algebra-polynomial-endofunctor l3) →
    (Y : algebra-polynomial-endofunctor l4) →
    (f g : hom-algebra-polynomial-endofunctor X Y) →
    is-equiv (htpy-hom-algebra-polynomial-endofunctor-eq X Y f g)
  is-equiv-htpy-hom-algebra-polynomial-endofunctor-eq X Y f =
    fundamental-theorem-id f
      ( refl-htpy-hom-algebra-polynomial-endofunctor X Y f)
      ( is-contr-total-htpy-hom-algebra-polynomial-endofunctor X Y f)
      ( htpy-hom-algebra-polynomial-endofunctor-eq X Y f)

  eq-htpy-hom-algebra-polynomial-endofunctor :
    {l3 l4 : Level} (X : algebra-polynomial-endofunctor l3) →
    (Y : algebra-polynomial-endofunctor l4) →
    (f g : hom-algebra-polynomial-endofunctor X Y) →
    htpy-hom-algebra-polynomial-endofunctor X Y f g → Id f g
  eq-htpy-hom-algebra-polynomial-endofunctor X Y f g =
    inv-is-equiv (is-equiv-htpy-hom-algebra-polynomial-endofunctor-eq X Y f g)

  -- We show that 𝕎 A B is the initial algebra
  
  map-hom-𝕎-Alg :
    {l : Level} (X : algebra-polynomial-endofunctor l) →
    𝕎 → type-algebra-polynomial-endofunctor X
  map-hom-𝕎-Alg X (sup-𝕎 x α) =
    structure-algebra-polynomial-endofunctor X
      ( pair x (map-hom-𝕎-Alg X ∘ α))

  structure-hom-𝕎-Alg :
    {l : Level} (X : algebra-polynomial-endofunctor l) →
    ( (map-hom-𝕎-Alg X) ∘ structure-𝕎-Alg) ~
    ( ( structure-algebra-polynomial-endofunctor X) ∘
      ( map-polynomial-endofunctor (map-hom-𝕎-Alg X)))
  structure-hom-𝕎-Alg X (pair x α) = refl

  hom-𝕎-Alg :
    {l : Level} (X : algebra-polynomial-endofunctor l) →
    hom-algebra-polynomial-endofunctor 𝕎-Alg X
  hom-𝕎-Alg X =
    pair (map-hom-𝕎-Alg X) (structure-hom-𝕎-Alg X)

  htpy-htpy-hom-𝕎-Alg :
    {l : Level} (X : algebra-polynomial-endofunctor l) →
    (f : hom-algebra-polynomial-endofunctor 𝕎-Alg X) →
    map-hom-𝕎-Alg X ~
    map-hom-algebra-polynomial-endofunctor 𝕎-Alg X f
  htpy-htpy-hom-𝕎-Alg X f (sup-𝕎 x α) =
    ( ap ( λ t → structure-algebra-polynomial-endofunctor X (pair x t))
         ( eq-htpy (λ z → htpy-htpy-hom-𝕎-Alg X f (α z)))) ∙
    ( inv
      ( structure-hom-algebra-polynomial-endofunctor 𝕎-Alg X f
        ( pair x α)))

  compute-structure-htpy-hom-𝕎-Alg :
    {l : Level} (X : algebra-polynomial-endofunctor l) (x : A)
    (α : B x → 𝕎) {f : 𝕎 → type-algebra-polynomial-endofunctor X} →
    (H : map-hom-𝕎-Alg X ~ f) →
    Id ( ap ( structure-algebra-polynomial-endofunctor X)
            ( htpy-polynomial-endofunctor H (pair x α)))
       ( ap ( λ t → structure-algebra-polynomial-endofunctor X (pair x t))
            ( eq-htpy (H ·r α)))
  compute-structure-htpy-hom-𝕎-Alg X x α =
    ind-htpy
      ( map-hom-𝕎-Alg X)
      ( λ f H →
        Id ( ap ( structure-algebra-polynomial-endofunctor X)
                ( htpy-polynomial-endofunctor H (pair x α)))
           ( ap ( λ t → structure-algebra-polynomial-endofunctor X (pair x t))
                ( eq-htpy (H ·r α))))
      ( ap ( ap (pr2 X))
           ( coh-refl-htpy-polynomial-endofunctor
             ( map-hom-𝕎-Alg X)
             ( pair x α)) ∙
      ( inv
        ( ap ( ap (λ t → pr2 X (pair x t)))
             ( eq-htpy-refl-htpy (map-hom-𝕎-Alg X ∘ α))))) 
  
  structure-htpy-hom-𝕎-Alg :
    {l : Level} (X : algebra-polynomial-endofunctor l) →
    (f : hom-algebra-polynomial-endofunctor 𝕎-Alg X) →
    ( ( structure-hom-𝕎-Alg X) ∙h
      ( ( structure-algebra-polynomial-endofunctor X) ·l
        ( htpy-polynomial-endofunctor (htpy-htpy-hom-𝕎-Alg X f)))) ~
    ( ( (htpy-htpy-hom-𝕎-Alg X f) ·r structure-𝕎-Alg) ∙h
      ( structure-hom-algebra-polynomial-endofunctor 𝕎-Alg X f))
  structure-htpy-hom-𝕎-Alg (pair X μ) (pair f μ-f) (pair x α) =
    ( ( ( compute-structure-htpy-hom-𝕎-Alg (pair X μ) x α
          ( htpy-htpy-hom-𝕎-Alg (pair X μ) (pair f μ-f)))  ∙
        ( inv right-unit)) ∙
      ( ap ( concat
             ( ap
               ( λ t → μ (pair x t))
               ( eq-htpy (htpy-htpy-hom-𝕎-Alg (pair X μ) (pair f μ-f) ·r α)))
           ( μ (map-polynomial-endofunctor f (pair x α))))
           ( inv (left-inv ( μ-f (pair x α)))))) ∙
    ( inv
      ( assoc
        ( ap ( λ t → μ (pair x t))
             ( eq-htpy (htpy-htpy-hom-𝕎-Alg (pair X μ) (pair f μ-f) ·r α)))
        ( inv (μ-f (pair x α)))
        ( μ-f (pair x α))))

  htpy-hom-𝕎-Alg :
    {l : Level} (X : algebra-polynomial-endofunctor l) →
    (f : hom-algebra-polynomial-endofunctor 𝕎-Alg X) →
    htpy-hom-algebra-polynomial-endofunctor 𝕎-Alg X (hom-𝕎-Alg X) f
  htpy-hom-𝕎-Alg X f =
    pair (htpy-htpy-hom-𝕎-Alg X f) (structure-htpy-hom-𝕎-Alg X f)

  is-initial-𝕎-Alg :
    {l : Level} (X : algebra-polynomial-endofunctor l) →
    is-contr (hom-algebra-polynomial-endofunctor 𝕎-Alg X)
  is-initial-𝕎-Alg X =
    pair
      ( hom-𝕎-Alg X)
      ( λ f →
        eq-htpy-hom-algebra-polynomial-endofunctor 𝕎-Alg X
          (hom-𝕎-Alg X) f (htpy-hom-𝕎-Alg X f))

open Container public

--------------------------------------------------------------------------------

-- Indexed W-types

data i𝕎 {l1 l2 l3 : Level} (I : UU l1) (A : I → UU l2) (B : (i : I) → A i → UU l3) (f : (i : I) (x : A i) → B i x → I) (i : I) : UU (l2 ⊔ l3) where
  sup-i𝕎 : (x : A i) (α : (y : B i x) → i𝕎 I A B f (f i x y)) → i𝕎 I A B f i
