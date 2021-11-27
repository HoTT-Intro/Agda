{-# OPTIONS --without-K --allow-unsolved-metas --exact-split #-}

module book.24-pushouts where

open import book.23-pullbacks public

-- Section 14.1

{- We define the type of cocones with vertex X on a span. Since we will use it
   later on, we will also characterize the identity type of the type of cocones
   with a given vertex X. -}

cocone :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) → UU l4 → UU _
cocone {A = A} {B = B} f g X =
  Σ (A → X) (λ i → Σ (B → X) (λ j → (i ∘ f) ~ (j ∘ g)))

{- We characterize the identity type of the type of cocones with vertex C. -}

coherence-htpy-cocone :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c c' : cocone f g X) →
  (K : (pr1 c) ~ (pr1 c')) (L : (pr1 (pr2 c)) ~ (pr1 (pr2 c'))) → UU (l1 ⊔ l4)
coherence-htpy-cocone f g c c' K L =
  ((pr2 (pr2 c)) ∙h (L ·r g)) ~ ((K ·r f) ∙h (pr2 (pr2 c')))

htpy-cocone :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} →
  cocone f g X → cocone f g X → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
htpy-cocone f g c c' =
  Σ ((pr1 c) ~ (pr1 c'))
    ( λ K → Σ ((pr1 (pr2 c)) ~ (pr1 (pr2 c')))
      ( coherence-htpy-cocone f g c c' K))

reflexive-htpy-cocone :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  htpy-cocone f g c c
reflexive-htpy-cocone f g (pair i (pair j H)) =
  pair refl-htpy (pair refl-htpy right-unit-htpy)

htpy-cocone-eq :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c c' : cocone f g X) →
  Id c c' → htpy-cocone f g c c'
htpy-cocone-eq f g c .c refl = reflexive-htpy-cocone f g c

is-contr-total-htpy-cocone :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  is-contr (Σ (cocone f g X) (htpy-cocone f g c))
is-contr-total-htpy-cocone f g c =
  is-contr-total-Eq-structure
    ( λ i' jH' K → Σ ((pr1 (pr2 c)) ~ (pr1 jH'))
      ( coherence-htpy-cocone f g c (pair i' jH') K))
    ( is-contr-total-htpy (pr1 c))
    ( pair (pr1 c) refl-htpy)
    ( is-contr-total-Eq-structure
      ( λ j' H' → coherence-htpy-cocone f g c
        ( pair (pr1 c) (pair j' H'))
        ( refl-htpy))
      ( is-contr-total-htpy (pr1 (pr2 c)))
      ( pair (pr1 (pr2 c)) refl-htpy)
      ( is-contr-is-equiv'
        ( Σ (((pr1 c) ∘ f) ~ ((pr1 (pr2 c)) ∘ g)) (λ H' → (pr2 (pr2 c)) ~ H'))
        ( tot (λ H' M → right-unit-htpy ∙h M))
        ( is-equiv-tot-is-fiberwise-equiv (λ H' → is-equiv-concat-htpy _ _))
        ( is-contr-total-htpy (pr2 (pr2 c)))))

is-equiv-htpy-cocone-eq :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c c' : cocone f g X) →
  is-equiv (htpy-cocone-eq f g c c')
is-equiv-htpy-cocone-eq f g c =
  fundamental-theorem-id c
    ( reflexive-htpy-cocone f g c)
    ( is-contr-total-htpy-cocone f g c)
    ( htpy-cocone-eq f g c)

eq-htpy-cocone :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c c' : cocone f g X) →
  htpy-cocone f g c c' → Id c c'
eq-htpy-cocone f g c c' = map-inv-is-equiv (is-equiv-htpy-cocone-eq f g c c')

{- Given a cocone c on a span S with vertex X, and a type Y, the function 
   cocone-map sends a function X → Y to a new cocone with vertex Y. -}

cocone-map :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} {Y : UU l5} →
  cocone f g X → (X → Y) → cocone f g Y
cocone-map f g (pair i (pair j H)) h =
  pair (h ∘ i) (pair (h ∘ j) (h ·l H))

cocone-map-id :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  Id (cocone-map f g c id) c
cocone-map-id f g (pair i (pair j H)) =
  eq-pair-Σ refl (eq-pair-Σ refl (eq-htpy (λ s → ap-id (H s))))

cocone-map-comp :
  {l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  {Y : UU l5} (h : X → Y) {Z : UU l6} (k : Y → Z) →
  Id (cocone-map f g c (k ∘ h)) (cocone-map f g (cocone-map f g c h) k)
cocone-map-comp f g (pair i (pair j H)) h k =
  eq-pair-Σ refl (eq-pair-Σ refl (eq-htpy (λ s → ap-comp k h (H s))))

{- A cocone c on a span S is said to satisfy the universal property of the
   pushout of S if the function cocone-map is an equivalence for every type Y.
   -}

universal-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} →
  cocone f g X → UU _
universal-property-pushout l f g c =
  (Y : UU l) → is-equiv (cocone-map f g {Y = Y} c)

map-universal-property-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ( up-c : {l : Level} → universal-property-pushout l f g c)
  {Y : UU l5} → cocone f g Y → (X → Y)
map-universal-property-pushout f g c up-c {Y} = map-inv-is-equiv (up-c Y)

htpy-cocone-map-universal-property-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ( up-c : {l : Level} → universal-property-pushout l f g c)
  { Y : UU l5} (d : cocone f g Y) →
  htpy-cocone f g
    ( cocone-map f g c
      ( map-universal-property-pushout f g c up-c d))
    ( d)
htpy-cocone-map-universal-property-pushout f g c up-c {Y} d =
  htpy-cocone-eq f g
    ( cocone-map f g c (map-universal-property-pushout f g c up-c d))
    ( d)
    ( issec-map-inv-is-equiv (up-c Y) d)

uniqueness-map-universal-property-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ( up-c : {l : Level} → universal-property-pushout l f g c) →
  { Y : UU l5} (d : cocone f g Y) →
  is-contr ( Σ (X → Y) (λ h → htpy-cocone f g (cocone-map f g c h) d))
uniqueness-map-universal-property-pushout f g c up-c {Y} d =
  is-contr-is-equiv'
    ( fib (cocone-map f g c) d)
    ( tot (λ h → htpy-cocone-eq f g (cocone-map f g c h) d))
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ h → is-equiv-htpy-cocone-eq f g (cocone-map f g c h) d))
    ( is-contr-map-is-equiv (up-c Y) d)

{- We derive a 3-for-2 property of pushouts, analogous to the 3-for-2 property
   of pullbacks. -}

triangle-cocone-cocone :
  { l1 l2 l3 l4 l5 l6 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {Y : UU l5}
  { f : S → A} {g : S → B} (c : cocone f g X) (d : cocone f g Y)
  ( h : X → Y) (KLM : htpy-cocone f g (cocone-map f g c h) d)
  ( Z : UU l6) →
  ( cocone-map f g d) ~ ((cocone-map f g c) ∘ (λ (k : Y → Z) → k ∘ h))
triangle-cocone-cocone {Y = Y} {f = f} {g = g} c d h KLM Z k =
  inv
    ( ( cocone-map-comp f g c h k) ∙
      ( ap
        ( λ t → cocone-map f g t k)
        ( eq-htpy-cocone f g (cocone-map f g c h) d KLM)))

is-equiv-up-pushout-up-pushout :
  { l1 l2 l3 l4 l5 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {Y : UU l5}
  ( f : S → A) (g : S → B) (c : cocone f g X) (d : cocone f g Y) →
  ( h : X → Y) (KLM : htpy-cocone f g (cocone-map f g c h) d) →
  ( up-c : {l : Level} → universal-property-pushout l f g c) →
  ( up-d : {l : Level} → universal-property-pushout l f g d) →
  is-equiv h
is-equiv-up-pushout-up-pushout f g c d h KLM up-c up-d =
  is-equiv-is-equiv-precomp h
    ( λ l Z →
      is-equiv-right-factor
        ( cocone-map f g d)
        ( cocone-map f g c)
        ( precomp h Z)
        ( triangle-cocone-cocone c d h KLM Z)
        ( up-c Z)
        ( up-d Z))

up-pushout-up-pushout-is-equiv :
  { l1 l2 l3 l4 l5 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {Y : UU l5}
  ( f : S → A) (g : S → B) (c : cocone f g X) (d : cocone f g Y) →
  ( h : X → Y) (KLM : htpy-cocone f g (cocone-map f g c h) d) →
  is-equiv h →
  ( up-c : {l : Level} → universal-property-pushout l f g c) →
  {l : Level} → universal-property-pushout l f g d
up-pushout-up-pushout-is-equiv f g c d h KLM is-equiv-h up-c Z =
  is-equiv-comp
    ( cocone-map f g d)
    ( cocone-map f g c)
    ( precomp h Z)
    ( triangle-cocone-cocone c d h KLM Z)
    ( is-equiv-precomp-is-equiv h is-equiv-h Z)
    ( up-c Z)

up-pushout-is-equiv-up-pushout :
  { l1 l2 l3 l4 l5 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {Y : UU l5}
  ( f : S → A) (g : S → B) (c : cocone f g X) (d : cocone f g Y) →
  ( h : X → Y) (KLM : htpy-cocone f g (cocone-map f g c h) d) →
  ( up-d : {l : Level} → universal-property-pushout l f g d) →
  is-equiv h →
  {l : Level} → universal-property-pushout l f g c
up-pushout-is-equiv-up-pushout f g c d h KLM up-d is-equiv-h Z =
  is-equiv-left-factor
    ( cocone-map f g d)
    ( cocone-map f g c)
    ( precomp h Z)
    ( triangle-cocone-cocone c d h KLM Z)
    ( up-d Z)
    ( is-equiv-precomp-is-equiv h is-equiv-h Z)

uniquely-unique-pushout :
  { l1 l2 l3 l4 l5 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {Y : UU l5}
  ( f : S → A) (g : S → B) (c : cocone f g X) (d : cocone f g Y) →
  ( up-c : {l : Level} → universal-property-pushout l f g c) →
  ( up-d : {l : Level} → universal-property-pushout l f g d) →
  is-contr
    ( Σ (X ≃ Y) (λ e → htpy-cocone f g (cocone-map f g c (map-equiv e)) d))
uniquely-unique-pushout f g c d up-c up-d =
  is-contr-total-Eq-substructure
    ( uniqueness-map-universal-property-pushout f g c up-c d)
    ( is-subtype-is-equiv)
    ( map-universal-property-pushout f g c up-c d)
    ( htpy-cocone-map-universal-property-pushout f g c up-c d)
    ( is-equiv-up-pushout-up-pushout f g c d
      ( map-universal-property-pushout f g c up-c d)
      ( htpy-cocone-map-universal-property-pushout f g c up-c d)
      ( up-c)
      ( up-d))
  
{- We will assume that every span has a pushout. Moreover, we will introduce
   some further terminology to facilitate working with these pushouts. -}

postulate pushout : {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3} (f : S → A) (g : S → B) → UU (l1 ⊔ l2 ⊔ l3)

postulate inl-pushout : {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3} (f : S → A) (g : S → B) → A → pushout f g

postulate inr-pushout : {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3} (f : S → A) (g : S → B) → B → pushout f g

postulate glue-pushout : {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3} (f : S → A) (g : S → B) → ((inl-pushout f g) ∘ f) ~ ((inr-pushout f g) ∘ g)

cocone-pushout :
  {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) → cocone f g (pushout f g)
cocone-pushout f g =
  pair
    ( inl-pushout f g)
    ( pair
      ( inr-pushout f g)
      ( glue-pushout f g))

postulate up-pushout : {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} (f : S → A) (g : S → B) → universal-property-pushout l4 f g (cocone-pushout f g)

cogap :
  { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) →
  { X : UU l4} (c : cocone f g X) → pushout f g → X
cogap f g =
  map-universal-property-pushout f g
    ( cocone-pushout f g)
    ( up-pushout f g)

is-pushout :
  { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
is-pushout f g c = is-equiv (cogap f g c)

-- Section 14.2 Suspensions

suspension-structure :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
suspension-structure X Y = Σ Y (λ N → Σ Y (λ S → (x : X) → Id N S))

suspension-cocone' :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
suspension-cocone' X Y = cocone (const X unit star) (const X unit star) Y

cocone-suspension-structure :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) →
  suspension-structure X Y → suspension-cocone' X Y
cocone-suspension-structure X Y (pair N (pair S merid)) =
  pair
    ( const unit Y N)
    ( pair
      ( const unit Y S)
      ( merid))

universal-property-suspension' :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2)
  (susp-str : suspension-structure X Y) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-suspension' l X Y susp-str-Y =
  universal-property-pushout l
    ( const X unit star)
    ( const X unit star)
    ( cocone-suspension-structure X Y susp-str-Y)

is-suspension :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (lsuc l ⊔ l1 ⊔ l2)
is-suspension l X Y =
  Σ (suspension-structure X Y) (universal-property-suspension' l X Y)

suspension :
  {l : Level} → UU l → UU l
suspension X = pushout (const X unit star) (const X unit star)

N-susp :
  {l : Level} {X : UU l} → suspension X
N-susp {X = X} = inl-pushout (const X unit star) (const X unit star) star

S-susp :
  {l : Level} {X : UU l} → suspension X
S-susp {X = X} = inr-pushout (const X unit star) (const X unit star) star

merid-susp :
  {l : Level} {X : UU l} → X → Id (N-susp {X = X}) (S-susp {X = X})
merid-susp {X = X} = glue-pushout (const X unit star) (const X unit star)

sphere : ℕ → UU lzero
sphere zero-ℕ = bool
sphere (succ-ℕ n) = suspension (sphere n)

N-sphere : (n : ℕ) → sphere n
N-sphere zero-ℕ = true
N-sphere (succ-ℕ n) = N-susp

S-sphere : (n : ℕ) → sphere n
S-sphere zero-ℕ = false
S-sphere (succ-ℕ n) = S-susp

{- We now work towards Lemma 17.2.2. -}

suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) → UU _
suspension-cocone X Z = Σ Z (λ z1 → Σ Z (λ z2 → (x : X) → Id z1 z2))

ev-suspension :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (susp-str-Y : suspension-structure X Y) →
  (Z : UU l3) → (Y → Z) → suspension-cocone X Z
ev-suspension (pair N (pair S merid)) Z h =
  pair (h N) (pair (h S) (h ·l merid))

universal-property-suspension :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2) →
  suspension-structure X Y → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-suspension l X Y susp-str-Y =
  (Z : UU l) → is-equiv (ev-suspension susp-str-Y Z)

comparison-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  suspension-cocone' X Z ≃ suspension-cocone X Z
comparison-suspension-cocone X Z =
  equiv-Σ
    ( λ z1 → Σ Z (λ z2 → (x : X) → Id z1 z2))
    ( equiv-ev-star' Z)
    ( λ z1 →
      equiv-Σ
        ( λ z2 → (x : X) → Id (z1 star) z2)
        ( equiv-ev-star' Z)
        ( λ z2 → equiv-id))

map-comparison-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  suspension-cocone' X Z → suspension-cocone X Z
map-comparison-suspension-cocone X Z =
  map-equiv (comparison-suspension-cocone X Z)

is-equiv-map-comparison-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  is-equiv (map-comparison-suspension-cocone X Z)
is-equiv-map-comparison-suspension-cocone X Z =
  is-equiv-map-equiv (comparison-suspension-cocone X Z)

triangle-ev-suspension :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (susp-str-Y : suspension-structure X Y) →
  (Z : UU l3) →
  ( ( map-comparison-suspension-cocone X Z) ∘
    ( cocone-map
      ( const X unit star)
      ( const X unit star)
      ( cocone-suspension-structure X Y susp-str-Y))) ~
  ( ev-suspension susp-str-Y Z)
triangle-ev-suspension (pair N (pair S merid)) Z h = refl

is-equiv-ev-suspension :
  { l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  ( susp-str-Y : suspension-structure X Y) →
  ( up-Y : universal-property-suspension' l3 X Y susp-str-Y) → 
  ( Z : UU l3) → is-equiv (ev-suspension susp-str-Y Z)
is-equiv-ev-suspension {X = X} susp-str-Y up-Y Z =
  is-equiv-comp
    ( ev-suspension susp-str-Y Z)
    ( map-comparison-suspension-cocone X Z)
    ( cocone-map
      ( const X unit star)
      ( const X unit star)
      ( cocone-suspension-structure X _ susp-str-Y))
    ( inv-htpy (triangle-ev-suspension susp-str-Y Z))
    ( up-Y Z)
    ( is-equiv-map-comparison-suspension-cocone X Z)

--------------------------------------------------------------------------------

-- Section 14.3 Duality of pushouts and pullbacks
  
{- The universal property of the pushout of a span S can also be stated as a
   pullback-property: a cocone c = (pair i (pair j H)) with vertex X
   satisfies the universal property of the pushout of S if and only if the
   square

     Y^X -----> Y^B
      |          |
      |          |
      V          V
     Y^A -----> Y^S

   is a pullback square for every type Y. Below, we first define the cone of
   this commuting square, and then we introduce the type 
   pullback-property-pushout, which states that the above square is a pullback.
   -}

htpy-precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {f g : A → B} (H : f ~ g) (C : UU l3) →
  (precomp f C) ~ (precomp g C)
htpy-precomp H C h = eq-htpy (h ·l H)

compute-htpy-precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : UU l3) →
  (htpy-precomp (refl-htpy' f) C) ~ refl-htpy
compute-htpy-precomp f C h = eq-htpy-refl-htpy (h ∘ f)

cone-pullback-property-pushout :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (Y : UU l) →
  cone (λ (h : A → Y) → h ∘ f) (λ (h : B → Y) → h ∘ g) (X → Y)
cone-pullback-property-pushout f g {X} c Y =
  pair
    ( precomp (pr1 c) Y)
    ( pair
      ( precomp (pr1 (pr2 c)) Y)
      ( htpy-precomp (pr2 (pr2 c)) Y))

pullback-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  UU (l1 ⊔ (l2 ⊔ (l3 ⊔ (l4 ⊔ lsuc l))))
pullback-property-pushout l {S} {A} {B} f g {X} c =
  (Y : UU l) → is-pullback
    ( precomp f Y)
    ( precomp g Y)
    ( cone-pullback-property-pushout f g c Y)

{- In order to show that the universal property of pushouts is equivalent to 
   the pullback property, we show that the maps cocone-map and the gap map fit 
   in a commuting triangle, where the third map is an equivalence. The claim 
   then follows from the 3-for-2 property of equivalences. -}
   
triangle-pullback-property-pushout-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  {l : Level} (Y : UU l) →
  ( cocone-map f g c) ~
  ( ( tot (λ i' → tot (λ j' p → htpy-eq p))) ∘
    ( gap (λ h → h ∘ f) (λ h → h ∘ g) (cone-pullback-property-pushout f g c Y)))
triangle-pullback-property-pushout-universal-property-pushout
  {S = S} {A = A} {B = B} f g (pair i (pair j H)) Y h =
    eq-pair-Σ refl (eq-pair-Σ refl (inv (issec-eq-htpy (h ·l H))))

pullback-property-pushout-universal-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  universal-property-pushout l f g c → pullback-property-pushout l f g c
pullback-property-pushout-universal-property-pushout
  l f g (pair i (pair j H)) up-c Y =
  let c = (pair i (pair j H)) in
  is-equiv-right-factor
    ( cocone-map f g c)
    ( tot (λ i' → tot (λ j' p → htpy-eq p)))
    ( gap (λ h → h ∘ f) (λ h → h ∘ g) (cone-pullback-property-pushout f g c Y))
    ( triangle-pullback-property-pushout-universal-property-pushout f g c Y)
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ i' → is-equiv-tot-is-fiberwise-equiv
        ( λ j' → funext (i' ∘ f) (j' ∘ g))))
    ( up-c Y)

universal-property-pushout-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  pullback-property-pushout l f g c → universal-property-pushout l f g c
universal-property-pushout-pullback-property-pushout
  l f g (pair i (pair j H)) pb-c Y =
  let c = (pair i (pair j H)) in
  is-equiv-comp
    ( cocone-map f g c)
    ( tot (λ i' → tot (λ j' p → htpy-eq p)))
    ( gap (λ h → h ∘ f) (λ h → h ∘ g) (cone-pullback-property-pushout f g c Y))
    ( triangle-pullback-property-pushout-universal-property-pushout f g c Y)
    ( pb-c Y)
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ i' → is-equiv-tot-is-fiberwise-equiv
        ( λ j' → funext (i' ∘ f) (j' ∘ g))))

cocone-compose-horizontal :
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( f : A → X) (i : A → B) (k : B → C) →
  ( c : cocone f i Y) (d : cocone (pr1 (pr2 c)) k Z) →
  cocone f (k ∘ i) Z
cocone-compose-horizontal f i k (pair j (pair g H)) (pair l (pair h K)) =
  pair
    ( l ∘ j)
    ( pair
      ( h)
      ( (l ·l H) ∙h (K ·r i)))

{-
is-pushout-rectangle-is-pushout-right-square :
  ( l : Level) { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( f : A → X) (i : A → B) (k : B → C) →
  ( c : cocone f i Y) (d : cocone (pr1 (pr2 c)) k Z) →
  universal-property-pushout l f i c →
  universal-property-pushout l (pr1 (pr2 c)) k d →
  universal-property-pushout l f (k ∘ i) (cocone-compose-horizontal f i k c d)
is-pushout-rectangle-is-pushout-right-square l f i k c d up-Y up-Z =
  universal-property-pushout-pullback-property-pushout l f (k ∘ i)
    ( cocone-compose-horizontal f i k c d)
    ( λ T → is-pullback-htpy {!!} {!!} {!!} {!!} {!!} {!!} {!!})
-}

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 13.1

-- Exercise 13.2

is-equiv-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv f →
  ({l : Level} → universal-property-pushout l f g c) → is-equiv (pr1 (pr2 c))
is-equiv-universal-property-pushout
  {A = A} {B} f g (pair i (pair j H)) is-equiv-f up-c =
  is-equiv-is-equiv-precomp j
    ( λ l T →
      is-equiv-is-pullback'
        ( λ (h : A → T) → h ∘ f)
        ( λ (h : B → T) → h ∘ g)
        ( cone-pullback-property-pushout f g (pair i (pair j H)) T)
        ( is-equiv-precomp-is-equiv f is-equiv-f T)
        ( pullback-property-pushout-universal-property-pushout
          l f g (pair i (pair j H)) up-c T))

equiv-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (e : S ≃ A) (g : S → B) (c : cocone (map-equiv e) g C) →
  ({l : Level} → universal-property-pushout l (map-equiv e) g c) →
  B ≃ C
equiv-universal-property-pushout e g c up-c =
  pair
    ( pr1 (pr2 c))
    ( is-equiv-universal-property-pushout
      ( map-equiv e)
      ( g)
      ( c)
      ( is-equiv-map-equiv e)
      ( up-c))

is-equiv-universal-property-pushout' :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv g →
  ({l : Level} → universal-property-pushout l f g c) →
  is-equiv (pr1 c)
is-equiv-universal-property-pushout' f g (pair i (pair j H)) is-equiv-g up-c =
  is-equiv-is-equiv-precomp i
    ( λ l T →
      is-equiv-is-pullback
        ( precomp f T)
        ( precomp g T)
        ( cone-pullback-property-pushout f g (pair i (pair j H)) T)
        ( is-equiv-precomp-is-equiv g is-equiv-g T)
        ( pullback-property-pushout-universal-property-pushout
          l f g (pair i (pair j H)) up-c T))

equiv-universal-property-pushout' :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (e : S ≃ B) (c : cocone f (map-equiv e) C) →
  ({l : Level} → universal-property-pushout l f (map-equiv e) c) →
  A ≃ C
equiv-universal-property-pushout' f e c up-c =
  pair
    ( pr1 c)
    ( is-equiv-universal-property-pushout'
      ( f)
      ( map-equiv e)
      ( c)
      ( is-equiv-map-equiv e)
      ( up-c))

universal-property-pushout-is-equiv :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv f → is-equiv (pr1 (pr2 c)) →
  ({l : Level} → universal-property-pushout l f g c)
universal-property-pushout-is-equiv f g (pair i (pair j H)) is-equiv-f is-equiv-j {l} =
  let c = (pair i (pair j H)) in
  universal-property-pushout-pullback-property-pushout l f g c
    ( λ T → is-pullback-is-equiv'
      ( λ h → h ∘ f)
      ( λ h → h ∘ g)
      ( cone-pullback-property-pushout f g c T)
      ( is-equiv-precomp-is-equiv f is-equiv-f T)
      ( is-equiv-precomp-is-equiv j is-equiv-j T))

universal-property-pushout-is-equiv' :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv g → is-equiv (pr1 c) →
  ({l : Level} → universal-property-pushout l f g c)
universal-property-pushout-is-equiv'
  f g (pair i (pair j H)) is-equiv-g is-equiv-i {l} =
  let c = (pair i (pair j H)) in
  universal-property-pushout-pullback-property-pushout l f g c
    ( λ T → is-pullback-is-equiv
      ( precomp f T)
      ( precomp g T)
      ( cone-pullback-property-pushout f g c T)
      ( is-equiv-precomp-is-equiv g is-equiv-g T)
      ( is-equiv-precomp-is-equiv i is-equiv-i T))

is-contr-suspension-is-contr :
  {l : Level} {X : UU l} → is-contr X → is-contr (suspension X)
is-contr-suspension-is-contr {l} {X} is-contr-X =
  is-contr-is-equiv'
    ( unit)
    ( pr1 (pr2 (cocone-pushout (const X unit star) (const X unit star))))
    ( is-equiv-universal-property-pushout
      ( const X unit star)
      ( const X unit star)
      ( cocone-pushout
        ( const X unit star)
        ( const X unit star))
      ( is-equiv-is-contr (const X unit star) is-contr-X is-contr-unit)
      ( up-pushout (const X unit star) (const X unit star)))
    ( is-contr-unit)

is-equiv-cofiber-point :
  {l : Level} {B : UU l} (b : B) →
  is-equiv (pr1 (cocone-pushout (const unit B b) (const unit unit star)))
is-equiv-cofiber-point {l} {B} b =
  is-equiv-universal-property-pushout'
    ( const unit B b)
    ( const unit unit star)
    ( cocone-pushout (const unit B b) (const unit unit star))
    ( is-equiv-is-contr (const unit unit star) is-contr-unit is-contr-unit)
    ( up-pushout (const unit B b) (const unit unit star))

-- Exercise 16.2

-- ev-disjunction :
--   {l1 l2 l3 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) (R : UU-Prop l3) →
--   ((type-Prop P) * (type-Prop Q) → (type-Prop R)) →
--   (type-Prop P → type-Prop R) × (type-Prop Q → type-Prop R)
-- ev-disjunction P Q R f =
--   pair
--     ( f ∘ (inl-join (type-Prop P) (type-Prop Q)))
--     ( f ∘ (inr-join (type-Prop P) (type-Prop Q)))

-- comparison-ev-disjunction :
--   {l1 l2 l3 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) (R : UU-Prop l3) →
--   cocone-join (type-Prop P) (type-Prop Q) (type-Prop R)

-- universal-property-disjunction-join-prop :
--   {l1 l2 l3 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) (R : UU-Prop l3) →
--   is-equiv (ev-disjunction P Q R)
