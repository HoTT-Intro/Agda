{-# OPTIONS --without-K --exact-split #-}

module extra.wild-monoids where

open import extra.wild-unital-magma public

unital-associator :
  {l : Level} (M : Wild-Unital-Magma l) → UU l
unital-associator M =
  Σ ( (x y z : type-Wild-Unital-Magma M) →
      Id ( mul-Wild-Unital-Magma M (mul-Wild-Unital-Magma M x y) z)
         ( mul-Wild-Unital-Magma M x (mul-Wild-Unital-Magma M y z)))
    ( λ α111 →
      Σ ( (y z : type-Wild-Unital-Magma M) →
          Id ( ( α111 (unit-Wild-Unital-Magma M) y z) ∙
               ( left-unit-law-mul-Wild-Unital-Magma M
                 ( mul-Wild-Unital-Magma M y z)))
             ( ap
               ( mul-Wild-Unital-Magma' M z)
               ( left-unit-law-mul-Wild-Unital-Magma M y)))
        ( λ α011 →
          Σ ( (x z : type-Wild-Unital-Magma M) →
              Id ( ( α111 x (unit-Wild-Unital-Magma M) z) ∙
                   ( ap
                     ( mul-Wild-Unital-Magma M x)
                     ( left-unit-law-mul-Wild-Unital-Magma M z)))
                 ( ap
                   ( mul-Wild-Unital-Magma' M z)
                   ( right-unit-law-mul-Wild-Unital-Magma M x)))
            ( λ α101 →
              Σ ( (x y : type-Wild-Unital-Magma M) →
                  Id ( ( α111 x y (unit-Wild-Unital-Magma M)) ∙
                       ( ap
                         ( mul-Wild-Unital-Magma M x)
                         ( right-unit-law-mul-Wild-Unital-Magma M y)))
                     ( right-unit-law-mul-Wild-Unital-Magma M
                       ( mul-Wild-Unital-Magma M x y)))
                ( λ α110 → unit))))

Wild-Monoid : (l : Level) → UU (lsuc l)
Wild-Monoid l =
  Σ (Wild-Unital-Magma l) unital-associator

wild-unital-magma-Wild-Monoid :
  {l : Level} → Wild-Monoid l → Wild-Unital-Magma l
wild-unital-magma-Wild-Monoid M = pr1 M
      
type-Wild-Monoid :
  {l : Level} → Wild-Monoid l → UU l
type-Wild-Monoid M = type-Wild-Unital-Magma (wild-unital-magma-Wild-Monoid M)

unit-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) → type-Wild-Monoid M
unit-Wild-Monoid M = unit-Wild-Unital-Magma (wild-unital-magma-Wild-Monoid M)

pointed-type-Wild-Monoid :
  {l : Level} → Wild-Monoid l → UU-pt l
pointed-type-Wild-Monoid M =
  pointed-type-Wild-Unital-Magma (wild-unital-magma-Wild-Monoid M)

unital-mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) → unital-mul (pointed-type-Wild-Monoid M)
unital-mul-Wild-Monoid M =
  unital-mul-Wild-Unital-Magma (wild-unital-magma-Wild-Monoid M)

mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) →
  type-Wild-Monoid M → type-Wild-Monoid M → type-Wild-Monoid M
mul-Wild-Monoid M = mul-Wild-Unital-Magma (wild-unital-magma-Wild-Monoid M)

mul-Wild-Monoid' :
  {l : Level} (M : Wild-Monoid l) →
  type-Wild-Monoid M → type-Wild-Monoid M → type-Wild-Monoid M
mul-Wild-Monoid' M = mul-Wild-Unital-Magma' (wild-unital-magma-Wild-Monoid M)

ap-mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) {a b c d : type-Wild-Monoid M} →
  Id a b → Id c d → Id (mul-Wild-Monoid M a c) (mul-Wild-Monoid M b d)
ap-mul-Wild-Monoid M =
  ap-mul-Wild-Unital-Magma (wild-unital-magma-Wild-Monoid M)

left-unit-law-mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) (x : type-Wild-Monoid M) →
  Id (mul-Wild-Monoid M (unit-Wild-Monoid M) x) x
left-unit-law-mul-Wild-Monoid M =
  left-unit-law-mul-Wild-Unital-Magma (wild-unital-magma-Wild-Monoid M)

right-unit-law-mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) (x : type-Wild-Monoid M) →
  Id (mul-Wild-Monoid M x (unit-Wild-Monoid M)) x
right-unit-law-mul-Wild-Monoid M =
  right-unit-law-mul-Wild-Unital-Magma (wild-unital-magma-Wild-Monoid M)

coh-unit-laws-mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) →
  Id (left-unit-law-mul-Wild-Monoid M (unit-Wild-Monoid M))
     (right-unit-law-mul-Wild-Monoid M (unit-Wild-Monoid M))
coh-unit-laws-mul-Wild-Monoid M =
  coh-unit-laws-mul-Wild-Unital-Magma (wild-unital-magma-Wild-Monoid M)

unital-associator-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) →
  unital-associator (wild-unital-magma-Wild-Monoid M)
unital-associator-Wild-Monoid M = pr2 M

associative-mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) (x y z : type-Wild-Monoid M) →
  Id ( mul-Wild-Monoid M (mul-Wild-Monoid M x y) z)
     ( mul-Wild-Monoid M x (mul-Wild-Monoid M y z))
associative-mul-Wild-Monoid M = pr1 (unital-associator-Wild-Monoid M)

-- In the definition of morphisms of wild monoids we only require the unit and
-- multiplication to be preserved. This is because we would need further
-- coherence in wild monoids if we want morphisms list X → M to preserve the
-- associator and unitors.

-- hom-Wild-Monoid :
--   {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2) → UU (l1 ⊔ l2)
-- hom-Wild-Monoid M N =
--   Σ ( Σ ( type-Wild-Monoid M → type-Wild-Monoid N)
--         ( λ f →
--           ( x y : type-Wild-Monoid M) →
--           Id (f (mul-Wild-Monoid M x y)) (mul-Wild-Monoid N (f x) (f y))))
--     -- ( λ fμ → Id (pr1 fμ (unit-Wild-Monoid M)) (unit-Wild-Monoid N))
--     ( λ fμ →
--       Σ ( Id (pr1 fμ (unit-Wild-Monoid M)) (unit-Wild-Monoid N))
--         ( λ p →
--           ( (x : type-Wild-Monoid M) →
--             Id ( ( ( pr2 fμ (unit-Wild-Monoid M) x) ∙
--                    ( ap (mul-Wild-Monoid' N (pr1 fμ x)) p)) ∙
--                  ( left-unit-law-mul-Wild-Monoid N (pr1 fμ x)))
--                ( ap (pr1 fμ) (left-unit-law-mul-Wild-Monoid M x))) ×
--           ( (x : type-Wild-Monoid M) →
--             Id ( ( ( pr2 fμ x (unit-Wild-Monoid M)) ∙
--                    ( ap (mul-Wild-Monoid N (pr1 fμ x)) p)) ∙
--                  ( right-unit-law-mul-Wild-Monoid N (pr1 fμ x)))
--                ( ap (pr1 fμ) (right-unit-law-mul-Wild-Monoid M x)))))

-- -- map-hom-Wild-Monoid :
-- --   {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2) →
-- --   hom-Wild-Monoid M N → type-Wild-Monoid M → type-Wild-Monoid N
-- -- map-hom-Wild-Monoid M N f = pr1 (pr1 f)

-- -- preserves-mul-map-hom-Wild-Monoid :
-- --   {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2)
-- --   (f : hom-Wild-Monoid M N) (x y : type-Wild-Monoid M) →
-- --   Id ( map-hom-Wild-Monoid M N f (mul-Wild-Monoid M x y))
-- --      ( mul-Wild-Monoid N
-- --        ( map-hom-Wild-Monoid M N f x)
-- --        ( map-hom-Wild-Monoid M N f y))
-- -- preserves-mul-map-hom-Wild-Monoid M N f = pr2 (pr1 f)

-- -- preserves-unit-map-hom-Wild-Monoid :
-- --   {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2)
-- --   (f : hom-Wild-Monoid M N) →
-- --   Id (map-hom-Wild-Monoid M N f (unit-Wild-Monoid M))
-- --      (unit-Wild-Monoid N)
-- -- preserves-unit-map-hom-Wild-Monoid M N f = pr2 f

-- -- htpy-hom-Wild-Monoid :
-- --   {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2)
-- --   (f g : hom-Wild-Monoid M N) → UU (l1 ⊔ l2)
-- -- htpy-hom-Wild-Monoid M N f g =
-- --   Σ ( Σ ( map-hom-Wild-Monoid M N f ~ map-hom-Wild-Monoid M N g)
-- --         ( λ H →
-- --           ( x y : type-Wild-Monoid M) →
-- --           Id ( ( preserves-mul-map-hom-Wild-Monoid M N f x y) ∙
-- --                ( ap-mul-Wild-Monoid N (H x) (H y)))
-- --              ( ( H (mul-Wild-Monoid M x y)) ∙
-- --                ( preserves-mul-map-hom-Wild-Monoid M N g x y))))
-- --     ( λ Hμ →
-- --       Id ( preserves-unit-map-hom-Wild-Monoid M N f)
-- --          ( pr1 Hμ (unit-Wild-Monoid M) ∙ preserves-unit-map-hom-Wild-Monoid M N g))

-- -- refl-htpy-hom-Wild-Monoid :
-- --   {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2)
-- --   (f : hom-Wild-Monoid M N) → htpy-hom-Wild-Monoid M N f f
-- -- refl-htpy-hom-Wild-Monoid M N f =
-- --   pair (pair refl-htpy (λ x y → right-unit)) refl

-- -- {-
-- -- is-contr-total-htpy-hom-Wild-Monoid :
-- --   {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2)
-- --   (f : hom-Wild-Monoid M N) →
-- --   is-contr (Σ (hom-Wild-Monoid M N) (htpy-hom-Wild-Monoid M N f))
-- -- is-contr-total-htpy-hom-Wild-Monoid M N f =
-- --   is-contr-total-Eq-structure
-- --     {! λ fμ p!}
-- --     {!!}
-- --     {!!}
-- --     {!!}
-- -- -}

-- -- -- We introduce the wild monoid of lists of elements of X.

-- -- list-Wild-Monoid : {l : Level} → UU l → Wild-Monoid l
-- -- list-Wild-Monoid X =
-- --   pair
-- --     ( pair (list X) (pair concat-list assoc-concat-list))
-- --     ( pair nil (pair left-unit-law-concat-list right-unit-law-concat-list))

-- -- module _
-- --   {l1 l2 : Level} {X : UU l1} (M : Wild-Monoid l2) (f : X → type-Wild-Monoid M)
-- --   where

-- --   map-elim-list-Wild-Monoid :
-- --     list X → type-Wild-Monoid M
-- --   map-elim-list-Wild-Monoid nil = unit-Wild-Monoid M
-- --   map-elim-list-Wild-Monoid (cons u x) =
-- --     mul-Wild-Monoid M (f u) (map-elim-list-Wild-Monoid x)

-- --   preserves-unit-map-elim-list-Wild-Monoid :
-- --     Id (map-elim-list-Wild-Monoid nil) (unit-Wild-Monoid M)
-- --   preserves-unit-map-elim-list-Wild-Monoid = refl

-- --   preserves-mul-map-elim-list-Wild-Monoid :
-- --     (x y : list X) →
-- --     Id ( map-elim-list-Wild-Monoid (concat-list x y))
-- --        ( mul-Wild-Monoid M
-- --          ( map-elim-list-Wild-Monoid x)
-- --          ( map-elim-list-Wild-Monoid y))
-- --   preserves-mul-map-elim-list-Wild-Monoid nil y =
-- --     inv (left-unit-law-mul-Wild-Monoid M (map-elim-list-Wild-Monoid y))
-- --   preserves-mul-map-elim-list-Wild-Monoid (cons u x) y =
-- --     ( ap (mul-Wild-Monoid M (f u))
-- --       ( preserves-mul-map-elim-list-Wild-Monoid x y)) ∙
-- --     ( inv
-- --       ( associative-mul-Wild-Monoid M
-- --         ( f u)
-- --         ( map-elim-list-Wild-Monoid x)
-- --         ( map-elim-list-Wild-Monoid y)))

-- --   elim-list-Wild-Monoid :
-- --     hom-Wild-Monoid (list-Wild-Monoid X) M
-- --   elim-list-Wild-Monoid =
-- --     pair
-- --       ( pair
-- --         ( map-elim-list-Wild-Monoid)
-- --         ( preserves-mul-map-elim-list-Wild-Monoid))
-- --       ( preserves-unit-map-elim-list-Wild-Monoid)

-- -- htpy-elim-list-Wild-Monoid :
-- --   {l1 l2 : Level} {X : UU l1} (M : Wild-Monoid l2)
-- --   (g h : hom-Wild-Monoid (list-Wild-Monoid X) M)
-- --   ( H : ( map-hom-Wild-Monoid (list-Wild-Monoid X) M g ∘ unit-list) ~
-- --         ( map-hom-Wild-Monoid (list-Wild-Monoid X) M h ∘ unit-list)) →
-- --   htpy-hom-Wild-Monoid (list-Wild-Monoid X) M g h
-- -- htpy-elim-list-Wild-Monoid {X = X} M g h H =
-- --   pair (pair α β) γ
-- --   where
-- --   α : pr1 (pr1 g) ~ pr1 (pr1 h)
-- --   α nil =
-- --     ( preserves-unit-map-hom-Wild-Monoid (list-Wild-Monoid X) M g) ∙
-- --     ( inv (preserves-unit-map-hom-Wild-Monoid (list-Wild-Monoid X) M h))
-- --   α (cons x l) =
-- --     ( preserves-mul-map-hom-Wild-Monoid
-- --       ( list-Wild-Monoid X)
-- --       ( M)
-- --       ( g)
-- --       ( unit-list x)
-- --       ( l)) ∙
-- --     ( ( ap-mul-Wild-Monoid M (H x) (α l)) ∙
-- --       ( inv
-- --         ( preserves-mul-map-hom-Wild-Monoid
-- --           ( list-Wild-Monoid X)
-- --           ( M)
-- --           ( h)
-- --           ( unit-list x)
-- --           ( l))))
-- --   β : (x y : pr1 (pr1 (list-Wild-Monoid X))) →
-- --       Id ( pr2 (pr1 g) x y ∙ ap-mul-Wild-Monoid M (α x) (α y))
-- --          ( α (concat-list x y) ∙ pr2 (pr1 h) x y)
-- --   β nil y = {!!}
-- --   β (cons x x₁) y = {!!}
-- --   γ : Id (pr2 g) (α nil ∙ pr2 h)
-- --   γ =
-- --     ( inv right-unit) ∙
-- --     ( ( ap (concat (pr2 g) (pr1 (pr2 M))) (inv (left-inv (pr2 h)))) ∙
-- --       ( inv (assoc (pr2 g) (inv (pr2 h)) (pr2 h))))
