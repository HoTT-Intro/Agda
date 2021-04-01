{-# OPTIONS --without-K --exact-split #-}

module extra.globular where

import book
open book public

record Glob (l : Level) : UU (lsuc l) where
  coinductive
  field
    type : UU l
    rel  : (x y : type) → Glob l

record hom-Glob {l1 l2 : Level} (A : Glob l1) (B : Glob l2) : UU (l1 ⊔ l2) where
  coinductive
  field
    map    : Glob.type A → Glob.type B
    is-hom : (x y : Glob.type A) →
             hom-Glob (Glob.rel A x y) (Glob.rel B (map x) (map y))

Glob-Type : {l : Level} → UU l → Glob l
Glob.type (Glob-Type A) = A
Glob.rel (Glob-Type A) x y = Glob-Type (Id x y)

hom-Glob-Map : {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  hom-Glob (Glob-Type A) (Glob-Type B)
hom-Glob.map (hom-Glob-Map {l1} {l2} {A} {B} f) = f
hom-Glob.is-hom (hom-Glob-Map {l1} {l2} {A} {B} f) x y = hom-Glob-Map (ap f)

record bihom-Glob
  {l1 l2 l3 : Level} (A : Glob l1) (B : Glob l2) (C : Glob l3) :
  UU (l1 ⊔ l2 ⊔ l3) where
  coinductive
  field
    binary-op : Glob.type A → Glob.type B → Glob.type C
    is-hom : (x x' : Glob.type A) (y y' : Glob.type B) →
             bihom-Glob
               ( Glob.rel A x x')
               ( Glob.rel B y y')
               ( Glob.rel C (binary-op x y) (binary-op x' y'))

bihom-Glob-binary-op :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  bihom-Glob (Glob-Type A) (Glob-Type B) (Glob-Type C)
bihom-Glob.binary-op (bihom-Glob-binary-op f) = f
bihom-Glob.is-hom (bihom-Glob-binary-op f) x x' y y' =
  bihom-Glob-binary-op (λ p q → ap-binary f p q)
