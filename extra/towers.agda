{-# OPTIONS --without-K --exact-split #-}

module extra.towers where

import book
open book public

record tower (l : Level) : UU (lsuc l)
  where
  coinductive
  field
    base  : UU l
    slice : (X : base) → tower l

record hom-tower {l1 l2 : Level} (A : tower l1) (B : tower l2) : UU (l1 ⊔ l2)
  where
  coinductive
  field
    base  : tower.base A → tower.base B
    slice : (X : tower.base A) →
            hom-tower (tower.slice A X) (tower.slice B (base X))

id-hom-tower :
  {l : Level} (A : tower l) → hom-tower A A
hom-tower.base (id-hom-tower A) = id
hom-tower.slice (id-hom-tower A) X = id-hom-tower (tower.slice A X)

comp-hom-tower :
  {l1 l2 l3 : Level} {A : tower l1} {B : tower l2} {C : tower l3} →
  (g : hom-tower B C) (f : hom-tower A B) → hom-tower A C
hom-tower.base (comp-hom-tower g f) = hom-tower.base g ∘ hom-tower.base f
hom-tower.slice (comp-hom-tower g f) X =
  comp-hom-tower (hom-tower.slice g (hom-tower.base f X)) (hom-tower.slice f X)

tr-hom-tower :
  {l1 l2 : Level} {A : tower l1} {B B' : tower l2} (f : hom-tower A B)
  (p : Id B B') (X : tower.base A) →
  Id ( tower.slice B (hom-tower.base f X))
     ( tower.slice B' (hom-tower.base (tr (hom-tower A) p f) X))
tr-hom-tower f refl X = refl

record htpy-hom-tower'
  {l1 l2 : Level} {A : tower l1} {B B' : tower l2} (p : Id B B')
  (f : hom-tower A B) (g : hom-tower A B') : UU (l1 ⊔ l2)
  where
  coinductive
  field
    base  : hom-tower.base (tr (hom-tower A) p f) ~ hom-tower.base g
    slice : (X : tower.base A) →
            htpy-hom-tower'
              ( (tr-hom-tower f p X) ∙ (ap (tower.slice B') (base X)))
              ( hom-tower.slice f X)
              ( hom-tower.slice g X)

refl-htpy-hom-tower' :
  {l1 l2 : Level} {A : tower l1} {B : tower l2} (f : hom-tower A B) →
  htpy-hom-tower' refl f f
htpy-hom-tower'.base (refl-htpy-hom-tower' f) =
  refl-htpy
htpy-hom-tower'.slice (refl-htpy-hom-tower' f) X =
  refl-htpy-hom-tower' (hom-tower.slice f X)

htpy-hom-tower :
  {l1 l2 : Level} {A : tower l1} {B : tower l2} (f g : hom-tower A B) →
  UU (l1 ⊔ l2)
htpy-hom-tower f g = htpy-hom-tower' refl f g

refl-htpy-hom-tower :
  {l1 l2 : Level} {A : tower l1} {B : tower l2} (f : hom-tower A B) →
  htpy-hom-tower f f
refl-htpy-hom-tower f = refl-htpy-hom-tower' f
