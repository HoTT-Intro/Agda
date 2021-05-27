{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.fibered-dependent-type-theories where

open import extra.dependent-type-theories public
open dependent

module fibered where

  ------------------------------------------------------------------------------

  -- Bifibered systems

  record bifibered-system
    {l1 l2 l3 l4 l5 l6 : Level} (l7 l8 : Level) {A : system l1 l2}
    (B : fibered-system l3 l4 A) (C : fibered-system l5 l6 A) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ lsuc l7 ⊔ lsuc l8)
    where
    coinductive
    field
      type    : {X : system.type A} (Y : fibered-system.type B X)
                (Z : fibered-system.type C X) → UU l7
      element : {X : system.type A} {Y : fibered-system.type B X}
                {Z : fibered-system.type C X} {x : system.element A X}
                (W : type Y Z) (y : fibered-system.element B Y x)
                (z : fibered-system.element C Z x) → UU l8
      slice   : {X : system.type A} {Y : fibered-system.type B X}
                {Z : fibered-system.type C X} → type Y Z →
                bifibered-system l7 l8
                  ( fibered-system.slice B Y)
                  ( fibered-system.slice C Z)

  record section-fibered-system
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
    {B : fibered-system l3 l4 A} {C : fibered-system l5 l6 A}
    (f : section-system A C) (D : bifibered-system l7 l8 B C) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l7 ⊔ l8)
    where
    coinductive
    field
      type    : {X : system.type A} (Y : fibered-system.type B X) →
                bifibered-system.type D Y (section-system.type f X)
      element : {X : system.type A} {Y : fibered-system.type B X} →
                {x : system.element A X} (y : fibered-system.element B Y x) →
                bifibered-system.element D 
                  ( type Y)
                  ( y)
                  ( section-system.element f x)
      slice   : {X : system.type A} (Y : fibered-system.type B X) →
                section-fibered-system
                  ( section-system.slice f X)
                  ( bifibered-system.slice D (type Y))

  ------------------------------------------------------------------------------

  -- Homotopies of sections of fibered systems

  double-tr :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
    (D : (x : A) → B x → C x → UU l4) {x y : A} (p : Id x y) {u : B x}
    {v : C x} → D x u v → D y (tr B p u) (tr C p v)
  double-tr D refl z = z

  tr-bifibered-system-slice :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
    {B : fibered-system l3 l4 A} {C : fibered-system l5 l6 A}
    (D : bifibered-system l7 l8 B C) {X : system.type A}
    (Y : fibered-system.type B X) {Z Z' : fibered-system.type C X}
    {d : bifibered-system.type D Y Z} {d' : bifibered-system.type D Y Z'}
    (p : Id Z Z') (q : Id (tr (bifibered-system.type D Y) p d) d') →
    Id ( tr ( bifibered-system l7 l8 (fibered-system.slice B Y))
            ( ap (fibered-system.slice C) p)
            ( bifibered-system.slice D d))
       ( bifibered-system.slice D (tr (bifibered-system.type D Y) p d))
  tr-bifibered-system-slice D Y refl refl = refl
   
  Eq-bifibered-system' :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
    {B : fibered-system l3 l4 A} {C C' : fibered-system l5 l6 A}
    (D : bifibered-system l7 l8 B C) (D' : bifibered-system l7 l8 B C')
    (α : Id C C') (β : Id (tr (bifibered-system l7 l8 B) α D) D')
    (f : section-system A C) (f' : section-system A C')
    (g : section-fibered-system f D) (g' : section-fibered-system f' D') →
    bifibered-system l7 l8 B (Eq-fibered-system' α f f')
  bifibered-system.type
    ( Eq-bifibered-system' D .D refl refl f f' g g') {X} Y p =
    Id ( tr (bifibered-system.type D Y) p (section-fibered-system.type g Y))
       ( section-fibered-system.type g' Y)
  bifibered-system.element
    ( Eq-bifibered-system' {A = A} {C = C} D .D refl refl f f' g g')
    {X} {Y} {p} {x} α y q =
    Id ( tr
         ( bifibered-system.element D (section-fibered-system.type g' Y) y)
         ( q)
         ( tr
           ( λ t →
             bifibered-system.element D t y
               ( tr (λ t → fibered-system.element C t x)
               ( p)
               ( section-system.element f x)))
           ( α)
           ( double-tr
             ( λ Z u v → bifibered-system.element D {Z = Z} u y v)
             ( p)
             ( section-fibered-system.element g y))))
       ( section-fibered-system.element g' y)
  bifibered-system.slice
    ( Eq-bifibered-system' {C = C} D .D refl refl f f' g g') {X} {Y} {α} β =
    Eq-bifibered-system'
      ( bifibered-system.slice D (section-fibered-system.type g Y))
      ( bifibered-system.slice D (section-fibered-system.type g' Y))
      ( ap (fibered-system.slice C) α)
      ( tr-bifibered-system-slice D Y α β ∙ ap (bifibered-system.slice D) β)
      ( section-system.slice f X)
      ( section-system.slice f' X)
      ( section-fibered-system.slice g Y)
      ( section-fibered-system.slice g' Y)

  htpy-section-fibered-system' :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
    {B : fibered-system l3 l4 A} {C C' : fibered-system l5 l6 A}
    {D : bifibered-system l7 l8 B C} {D' : bifibered-system l7 l8 B C'}
    {f : section-system A C} {f' : section-system A C'}
    {α : Id C C'} (β : Id (tr (bifibered-system l7 l8 B) α D) D')
    (H : htpy-section-system' α f f')
    (g : section-fibered-system f D) (h : section-fibered-system f' D') →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l7 ⊔ l8)
  htpy-section-fibered-system' {D = D} {D'} {f} {f'} {α} β H g h =
    section-fibered-system H (Eq-bifibered-system' D D' α β f f' g h)

  htpy-section-fibered-system :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
    {B : fibered-system l3 l4 A} {C : fibered-system l5 l6 A}
    {D : bifibered-system l7 l8 B C} {f f' : section-system A C} 
    (H : htpy-section-system f f')
    (g : section-fibered-system f D) (h : section-fibered-system f' D) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l7 ⊔ l8)
  htpy-section-fibered-system H g h =
    htpy-section-fibered-system' {α = refl} refl H g h

  ------------------------------------------------------------------------------

  -- Morphisms of fibered systems

  constant-bifibered-system :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
    (B : fibered-system l3 l4 A) {C : system l5 l6}
    (D : fibered-system l7 l8 C) →
    bifibered-system l7 l8 B (constant-fibered-system A C)
  bifibered-system.type (constant-bifibered-system B D) Y Z =
    fibered-system.type D Z
  bifibered-system.element (constant-bifibered-system B D) {Z = Z} W y z =
    fibered-system.element D W z
  bifibered-system.slice (constant-bifibered-system B D) {X = X} {Y} {Z} W =
    constant-bifibered-system
      ( fibered-system.slice B Y)
      ( fibered-system.slice D W)

  hom-fibered-system :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2} {A' : system l3 l4}
    (f : hom-system A A') (B : fibered-system l5 l6 A)
    (B' : fibered-system l7 l8 A') → UU (l1 ⊔ l2 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8)
  hom-fibered-system f B B' = 
    section-fibered-system f (constant-bifibered-system B B')

  id-hom-fibered-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} (B : fibered-system l3 l4 A) →
    hom-fibered-system (id-hom-system A) B B
  section-fibered-system.type (id-hom-fibered-system B) = id
  section-fibered-system.element (id-hom-fibered-system B) = id
  section-fibered-system.slice (id-hom-fibered-system B) Y =
    id-hom-fibered-system (fibered-system.slice B Y)

  comp-hom-fibered-system :
    {l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 : Level}
    {A : system l1 l2} {B : system l3 l4} {C : system l5 l6}
    {g : hom-system B C} {f : hom-system A B}
    {D : fibered-system l7 l8 A} {E : fibered-system l9 l10 B}
    {F : fibered-system l11 l12 C}
    (k : hom-fibered-system g E F) (h : hom-fibered-system f D E) →
    hom-fibered-system (comp-hom-system g f) D F
  section-fibered-system.type (comp-hom-fibered-system k h) Y =
    section-fibered-system.type k
      ( section-fibered-system.type h Y)
  section-fibered-system.element (comp-hom-fibered-system k h) y =
    section-fibered-system.element k
      ( section-fibered-system.element h y)
  section-fibered-system.slice (comp-hom-fibered-system k h) Y =
    comp-hom-fibered-system
      ( section-fibered-system.slice k (section-fibered-system.type h Y))
      ( section-fibered-system.slice h Y)

  htpy-hom-fibered-system :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
    {B : fibered-system l3 l4 A} {C : system l5 l6} {D : fibered-system l7 l8 C}
    {f f' : hom-system A C} (H : htpy-hom-system f f')
    (g : hom-fibered-system f B D) (g' : hom-fibered-system f' B D) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l7 ⊔ l8)
  htpy-hom-fibered-system H g g' = htpy-section-fibered-system H g g'

  ------------------------------------------------------------------------------

  {- We define what it means for a fibered system over a system equipped with
     weakening structure to be equipped with weakening structure. -}

  record fibered-weakening
    {l1 l2 l3 l4 : Level} {A : system l1 l2} (B : fibered-system l3 l4 A)
    (W : weakening A) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type  : {X : system.type A} (Y : fibered-system.type B X) →
              hom-fibered-system
                ( weakening.type W X)
                ( B)
                ( fibered-system.slice B Y)
      slice : {X : system.type A} (Y : fibered-system.type B X) →
              fibered-weakening
                ( fibered-system.slice B Y)
                ( weakening.slice W X)

  record preserves-fibered-weakening
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
    {B : fibered-system l3 l4 A} {C : system l5 l6}
    (D : fibered-system l7 l8 C) {WA : weakening A} {WC : weakening C}
    (WB : fibered-weakening B WA) (WD : fibered-weakening D WC)
    {f : hom-system A C} (Wf : preserves-weakening WA WC f)
    (g : hom-fibered-system f B D) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l7 ⊔ l8)
    where
    coinductive
    field
      type  : {X : system.type A} (Y : fibered-system.type B X) →
              htpy-hom-fibered-system
                ( preserves-weakening.type Wf X)
                ( comp-hom-fibered-system
                  ( section-fibered-system.slice g Y)
                  ( fibered-weakening.type WB Y))
                ( comp-hom-fibered-system
                  ( fibered-weakening.type WD
                    ( section-fibered-system.type g Y))
                  ( g))
      slice : {X : system.type A} (Y : fibered-system.type B X) →
              preserves-fibered-weakening
                ( fibered-system.slice D (section-fibered-system.type g Y))
                ( fibered-weakening.slice WB Y)
                ( fibered-weakening.slice WD (section-fibered-system.type g Y))
                ( preserves-weakening.slice Wf X)
                ( section-fibered-system.slice g Y)

  ------------------------------------------------------------------------------

  {- We define what it means for a fibered system over a system equipped with
     substitution structure to be equipped with substitution structure. -}

  record fibered-substitution
    {l1 l2 l3 l4 : Level} {A : system l1 l2} (B : fibered-system l3 l4 A)
    (S : substitution A) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type  : {X : system.type A} {Y : fibered-system.type B X}
              {x : system.element A X} (y : fibered-system.element B Y x) →
              hom-fibered-system
                ( substitution.type S X x)
                ( fibered-system.slice B Y)
                ( B)
      slice : {X : system.type A} (Y : fibered-system.type B X) →
              fibered-substitution
                ( fibered-system.slice B Y)
                ( substitution.slice S X)

  record fibered-generic-element
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
    {WA : weakening A} (W : fibered-weakening B WA) (δ : generic-element WA) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type  : {X : system.type A} (Y : fibered-system.type B X) →
              fibered-system.element
                ( fibered-system.slice B Y)
                ( section-fibered-system.type (fibered-weakening.type W Y) Y)
                ( generic-element.type δ X)
      slice : {X : system.type A} (Y : fibered-system.type B X) →
              fibered-generic-element
                ( fibered-weakening.slice W Y)
                ( generic-element.slice δ X)

