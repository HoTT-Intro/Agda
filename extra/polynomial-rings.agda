{-# OPTIONS --without-K --exact-split #-}

module extra.polynomial-rings where

open import extra.rings public

{- We state the universal property of the polynomial ring R[x]. -}

precomp-universal-property-polynomial-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3)
  (f : hom-Ring R S) (s : type-Ring S) →
  hom-Ring S T → (hom-Ring R T) × (type-Ring T)
precomp-universal-property-polynomial-Ring R S T f s g =
  pair (comp-hom-Ring R S T g f) (map-hom-Ring S T g s)

universal-property-polynomial-Ring :
  (l : Level) {l1 l2 : Level} (R : Ring l1) (S : Ring l2)
  (f : hom-Ring R S) (s : type-Ring S) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-polynomial-Ring l R S f s =
  (T : Ring l) →
  is-equiv (precomp-universal-property-polynomial-Ring R S T f s)

{- We define the polynomial ring R[x] -}

pretype-polynomial-Ring :
  {l1 : Level} (R : Ring l1) → UU l1
pretype-polynomial-Ring R =
  list (type-Ring R)

preconstant-polynomial-Ring :
  {l1 : Level} (R : Ring l1) → type-Ring R → pretype-polynomial-Ring R
preconstant-polynomial-Ring R r = cons r nil

prezero-polynomial-Ring :
  {l1 : Level} (R : Ring l1) → pretype-polynomial-Ring R
prezero-polynomial-Ring R = preconstant-polynomial-Ring R (zero-Ring R)

-- We define an equivalence relation on the pretype of a polynomial ring

rel-pretype-polynomial-Ring :
  {l1 : Level} (R : Ring l1) →
  (x y : pretype-polynomial-Ring R) → UU l1
rel-pretype-polynomial-Ring {l1} R nil nil =
  raise l1 unit
rel-pretype-polynomial-Ring R nil (cons s y) =
  (Id s (zero-Ring R)) × (rel-pretype-polynomial-Ring R nil y)
rel-pretype-polynomial-Ring R (cons r x) nil =
  (Id r (zero-Ring R)) × (rel-pretype-polynomial-Ring R x nil)
rel-pretype-polynomial-Ring R (cons r x) (cons s y) =
  (Id r s) × (rel-pretype-polynomial-Ring R x y)

is-prop-rel-pretype-polynomial-Ring :
  {l1 : Level} (R : Ring l1) (x y : pretype-polynomial-Ring R) →
  is-prop (rel-pretype-polynomial-Ring R x y)
is-prop-rel-pretype-polynomial-Ring {l1} R nil nil =
  is-prop-equiv' unit (equiv-raise l1 unit) is-prop-unit
is-prop-rel-pretype-polynomial-Ring R nil (cons s y) =
  is-prop-prod
    ( is-set-type-Ring R s (zero-Ring R))
    ( is-prop-rel-pretype-polynomial-Ring R nil y)
is-prop-rel-pretype-polynomial-Ring R (cons r x) nil =
  is-prop-prod
    ( is-set-type-Ring R r (zero-Ring R))
    ( is-prop-rel-pretype-polynomial-Ring R x nil)
is-prop-rel-pretype-polynomial-Ring R (cons r x) (cons s y) =
  is-prop-prod
    ( is-set-type-Ring R r s)
    ( is-prop-rel-pretype-polynomial-Ring R x y)

refl-rel-pretype-polynomial-Ring :
  {l1 : Level} (R : Ring l1) →
  (x : pretype-polynomial-Ring R) → rel-pretype-polynomial-Ring R x x
refl-rel-pretype-polynomial-Ring R nil =
  map-raise star
refl-rel-pretype-polynomial-Ring R (cons r x) =
  pair refl (refl-rel-pretype-polynomial-Ring R x)

symmetric-rel-pretype-polynomial-Ring :
  {l1 : Level} (R : Ring l1) →
  (x y : pretype-polynomial-Ring R) →
  rel-pretype-polynomial-Ring R x y → rel-pretype-polynomial-Ring R y x
symmetric-rel-pretype-polynomial-Ring R nil nil H = H
symmetric-rel-pretype-polynomial-Ring R nil (cons s y) (pair p H) =
  pair p (symmetric-rel-pretype-polynomial-Ring R nil y H)
symmetric-rel-pretype-polynomial-Ring R (cons r x) nil (pair p H) =
  pair p (symmetric-rel-pretype-polynomial-Ring R x nil H)
symmetric-rel-pretype-polynomial-Ring R (cons r x) (cons s y) (pair p H) =
  pair (inv p) (symmetric-rel-pretype-polynomial-Ring R x y H)

transitive-rel-pretype-polynomial-Ring :
  {l1 : Level} (R : Ring l1) →
  (x y z : pretype-polynomial-Ring R) →
  rel-pretype-polynomial-Ring R x y → rel-pretype-polynomial-Ring R y z →
  rel-pretype-polynomial-Ring R x z
transitive-rel-pretype-polynomial-Ring R nil nil nil H1 H2 =
  map-raise star
transitive-rel-pretype-polynomial-Ring R nil nil (cons x z) H1 H2 = H2
transitive-rel-pretype-polynomial-Ring R nil (cons x y) nil H1 H2 =
  map-raise star
transitive-rel-pretype-polynomial-Ring R
  nil (cons s y) (cons t z) (pair p1 H1) (pair p2 H2) =
  pair (inv p2 ∙ p1) (transitive-rel-pretype-polynomial-Ring R nil y z H1 H2)
transitive-rel-pretype-polynomial-Ring R (cons r x) nil nil H1 H2 = H1
transitive-rel-pretype-polynomial-Ring R
  (cons r x) nil (cons t z) (pair p1 H1) (pair p2 H2) =
  pair (p1 ∙ inv p2) (transitive-rel-pretype-polynomial-Ring R x nil z H1 H2)
transitive-rel-pretype-polynomial-Ring R
  (cons r x) (cons s y) nil (pair p1 H1) (pair p2 H2) =
  pair (p1 ∙ p2) (transitive-rel-pretype-polynomial-Ring R x y nil H1 H2)
transitive-rel-pretype-polynomial-Ring R
  (cons r x) (cons s y) (cons t z) (pair p1 H1) (pair p2 H2) =
  pair (p1 ∙ p2) (transitive-rel-pretype-polynomial-Ring R x y z H1 H2)
