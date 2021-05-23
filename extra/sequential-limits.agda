{-# OPTIONS --without-K --exact-split #-}

module extra.sequential-limits where

open import book public
open import extra.interchange public

--------------------------------------------------------------------------------

{- We introduce cosequences (i.e. sequences going in the other way) -}

Coseq-UU : (l : Level) → UU (lsuc l)
Coseq-UU l = Σ (ℕ → UU l) (λ A → (n : ℕ) → A (succ-ℕ n) → A n)

type-Coseq : {l : Level} (A : Coseq-UU l) → (n : ℕ) → UU l
type-Coseq A = pr1 A

map-Coseq :
  {l : Level} (A : Coseq-UU l) →
  (n : ℕ) → (type-Coseq A (succ-ℕ n)) → (type-Coseq A n)
map-Coseq A = pr2 A

{- We characterize the identity type of Coseq-UU l. -}

equiv-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) → UU (l1 ⊔ l2)
equiv-Coseq A B =
  Σ ( (n : ℕ) → (type-Coseq A n) ≃ (type-Coseq B n)) (λ e →
    ( n : ℕ) →
      ( (map-Coseq B n) ∘ (map-equiv (e (succ-ℕ n)))) ~
      ( (map-equiv (e n)) ∘ (map-Coseq A n)))

reflexive-equiv-Coseq :
  { l1 : Level} (A : Coseq-UU l1) → equiv-Coseq A A
reflexive-equiv-Coseq A =
  pair
    ( λ n → equiv-id)
    ( λ n → refl-htpy)

equiv-eq-Coseq :
  { l1 : Level} (A B : Coseq-UU l1) → Id A B → equiv-Coseq A B
equiv-eq-Coseq A .A refl = reflexive-equiv-Coseq A

is-contr-total-equiv-Coseq :
  { l1 : Level} (A : Coseq-UU l1) →
  is-contr (Σ (Coseq-UU l1) (equiv-Coseq A))
is-contr-total-equiv-Coseq A =
  is-contr-total-Eq-structure
    ( λ B g (e : (n : ℕ) → (type-Coseq A n) ≃ (B n)) → (n : ℕ) →
      ( (g n) ∘ (map-equiv (e (succ-ℕ n)))) ~
      ( (map-equiv (e n)) ∘ (map-Coseq A n)))
    ( is-contr-total-Eq-Π
      ( λ n B → (type-Coseq A n) ≃ B)
      ( λ n → is-contr-total-equiv (type-Coseq A n)))
    ( pair (type-Coseq A) (λ n → equiv-id))
    ( is-contr-total-Eq-Π
      ( λ n g → g ~ (map-Coseq A n))
      ( λ n → is-contr-total-htpy' (map-Coseq A n)))

is-equiv-equiv-eq-Coseq :
  { l1 : Level} (A B : Coseq-UU l1) → is-equiv (equiv-eq-Coseq A B)
is-equiv-equiv-eq-Coseq A =
  fundamental-theorem-id A
    ( reflexive-equiv-Coseq A)
    ( is-contr-total-equiv-Coseq A)
    ( equiv-eq-Coseq A)

eq-equiv-Coseq :
  { l1 : Level} (A B : Coseq-UU l1) → equiv-Coseq A B → Id A B
eq-equiv-Coseq A B = map-inv-is-equiv (is-equiv-equiv-eq-Coseq A B)

--------------------------------------------------------------------------------

{- We introduce dependent sequences -}

dependent-Coseq-UU :
  (l : Level) {l1 : Level} (A : Coseq-UU l1) → UU (lsuc l ⊔ l1)
dependent-Coseq-UU l A =
  Σ ( (n : ℕ) → type-Coseq A n → UU l)
    ( λ B →
      (n : ℕ) (a : type-Coseq A (succ-ℕ n)) →
      B (succ-ℕ n) a → B n (map-Coseq A n a))

type-dependent-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A) →
  (n : ℕ) → type-Coseq A n → UU l2
type-dependent-Coseq A = pr1

map-dependent-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A) →
  (n : ℕ) (a : type-Coseq A (succ-ℕ n)) →
  type-dependent-Coseq A B (succ-ℕ n) a →
  type-dependent-Coseq A B n (map-Coseq A n a)
map-dependent-Coseq A = pr2

{- We introduce sections of dependent cosequences -}

section-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A) → UU (l1 ⊔ l2)
section-Coseq A B =
  Σ ( (n : ℕ) (x : type-Coseq A n) → type-dependent-Coseq A B n x)
    ( λ f →
      (n : ℕ) (x : type-Coseq A (succ-ℕ n)) →
      Id (map-dependent-Coseq A B n x (f (succ-ℕ n) x)) (f n (map-Coseq A n x)))

value-section-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (f : section-Coseq A B) (n : ℕ) (x : type-Coseq A n) →
  type-dependent-Coseq A B n x
value-section-Coseq A B f = pr1 f

naturality-section-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (f : section-Coseq A B) (n : ℕ) (x : type-Coseq A (succ-ℕ n)) →
  Id ( map-dependent-Coseq A B n x
       ( value-section-Coseq A B f (succ-ℕ n) x))
     ( value-section-Coseq A B f n (map-Coseq A n x))
naturality-section-Coseq A B f = pr2 f

{- We introduce homotopies of sections of dependent cosequences. The advantage 
   of the following definition of homotopies of section is that we can iterate 
   the definition to consider homotopies of homotopies. -}

type-Eq-section-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (f g : section-Coseq A B) (n : ℕ) (x : type-Coseq A n) → UU l2
type-Eq-section-Coseq A B f g n x =
  Id (value-section-Coseq A B f n x) (value-section-Coseq A B g n x)

map-Eq-section-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (f g : section-Coseq A B) (n : ℕ) (x : type-Coseq A (succ-ℕ n)) →
  type-Eq-section-Coseq A B f g (succ-ℕ n) x →
  type-Eq-section-Coseq A B f g n (map-Coseq A n x)
map-Eq-section-Coseq A B f g n x p =
  ( inv (naturality-section-Coseq A B f n x)) ∙
  ( ( ap (map-dependent-Coseq A B n x) p) ∙
    ( naturality-section-Coseq A B g n x))

Eq-section-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (f g : section-Coseq A B) → dependent-Coseq-UU l2 A
Eq-section-Coseq A B f g =
  pair (type-Eq-section-Coseq A B f g) (map-Eq-section-Coseq A B f g)

htpy-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (f g : section-Coseq A B) → UU (l1 ⊔ l2)
htpy-Coseq A B f g = section-Coseq A (Eq-section-Coseq A B f g)

value-htpy-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (f g : section-Coseq A B) → htpy-Coseq A B f g →
  (n : ℕ) → (x : type-Coseq A n) →
  type-Eq-section-Coseq A B f g n x
value-htpy-Coseq A B f g = value-section-Coseq A (Eq-section-Coseq A B f g)

naturality-htpy-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (f g : section-Coseq A B) (H : htpy-Coseq A B f g)
  (n : ℕ) (x : type-Coseq A (succ-ℕ n)) →
  Id ( map-Eq-section-Coseq A B f g n x
       ( value-htpy-Coseq A B f g H (succ-ℕ n) x))
     ( value-htpy-Coseq A B f g H n (map-Coseq A n x))
naturality-htpy-Coseq A B f g =
  naturality-section-Coseq A (Eq-section-Coseq A B f g)

{- We show that htpy-Coseq characterizes the identity type of section-Coseq -}

refl-htpy-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (f : section-Coseq A B) → htpy-Coseq A B f f
refl-htpy-Coseq A B f =
  pair (λ n → refl-htpy) (λ n x → left-inv (pr2 f n x))

htpy-eq-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (f g : section-Coseq A B) → Id f g → htpy-Coseq A B f g
htpy-eq-Coseq A B f .f refl = refl-htpy-Coseq A B f

is-contr-total-htpy-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (f : section-Coseq A B) → is-contr (Σ (section-Coseq A B) (htpy-Coseq A B f))
is-contr-total-htpy-Coseq A B f =
  is-contr-total-Eq-structure
    ( λ g H G →
      (n : ℕ) (x : type-Coseq A (succ-ℕ n)) →
      Id ( pr2 (Eq-section-Coseq A B f (pair g H)) n x (G (succ-ℕ n) x))
         ( G n (pr2 A n x)))
    ( is-contr-total-Eq-Π
      ( λ n g → value-section-Coseq A B f n ~ g)
      ( λ n → is-contr-total-htpy (value-section-Coseq A B f n)))
    ( pair (value-section-Coseq A B f) (λ n → refl-htpy))
    ( is-contr-total-Eq-Π
      ( λ n G →
        (x : type-Coseq A (succ-ℕ n)) → Id ((inv (pr2 f n x)) ∙ (G x)) refl)
      ( λ n →
        is-contr-total-Eq-Π
          ( λ x p → Id ((inv (pr2 f n x)) ∙ p) refl)
          ( λ x →
            is-contr-map-is-equiv
              ( is-equiv-concat (inv (pr2 f n x)) (pr1 f n (pr2 A n x)))
              ( refl))))

is-equiv-htpy-eq-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A) →
  (f g : section-Coseq A B) → is-equiv (htpy-eq-Coseq A B f g)
is-equiv-htpy-eq-Coseq A B f =
  fundamental-theorem-id f
    ( refl-htpy-Coseq A B f)
    ( is-contr-total-htpy-Coseq A B f)
    ( htpy-eq-Coseq A B f)

eq-htpy-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A) →
  (f g : section-Coseq A B) → htpy-Coseq A B f g → Id f g
eq-htpy-Coseq A B f g = map-inv-is-equiv (is-equiv-htpy-eq-Coseq A B f g)

--------------------------------------------------------------------------------
  
{- We introduce morphisms of cosequences -}

weaken-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) →
  dependent-Coseq-UU l2 A
weaken-Coseq A B = pair (λ n x → type-Coseq B n) (λ n x → map-Coseq B n)

hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) → UU (l1 ⊔ l2)
hom-Coseq A B = section-Coseq A (weaken-Coseq A B)

map-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) →
  hom-Coseq A B → (n : ℕ) → type-Coseq A n → type-Coseq B n
map-hom-Coseq A B h = pr1 h

Naturality-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) →
  (h : (n : ℕ) → type-Coseq A n → type-Coseq B n) → UU (l1 ⊔ l2)
Naturality-hom-Coseq A B h =
  (n : ℕ) → ((map-Coseq B n) ∘ (h (succ-ℕ n))) ~ ((h n) ∘ (map-Coseq A n))

naturality-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (h : hom-Coseq A B) →
  Naturality-hom-Coseq A B (map-hom-Coseq A B h)
naturality-hom-Coseq A B h = pr2 h

{- We define homotopies of morphisms of cosequences -}

htpy-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2)
  (f g : hom-Coseq A B) → UU (l1 ⊔ l2)
htpy-hom-Coseq A B f g = htpy-Coseq A (weaken-Coseq A B) f g

refl-htpy-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  htpy-hom-Coseq A B f f
refl-htpy-hom-Coseq A B f =
  refl-htpy-Coseq A (weaken-Coseq A B) f

htpy-eq-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2)
  (f g : hom-Coseq A B) → Id f g → htpy-hom-Coseq A B f g
htpy-eq-hom-Coseq A B f .f refl = refl-htpy-hom-Coseq A B f

is-contr-total-htpy-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  is-contr (Σ (hom-Coseq A B) (htpy-hom-Coseq A B f))
is-contr-total-htpy-hom-Coseq A B f =
  is-contr-total-htpy-Coseq A (weaken-Coseq A B) f

is-equiv-htpy-eq-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) →
  (f g : hom-Coseq A B) → is-equiv (htpy-eq-hom-Coseq A B f g)
is-equiv-htpy-eq-hom-Coseq A B f =
  fundamental-theorem-id f
    ( refl-htpy-hom-Coseq A B f)
    ( is-contr-total-htpy-hom-Coseq A B f)
    ( htpy-eq-hom-Coseq A B f)

eq-htpy-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) →
  (f g : hom-Coseq A B) → htpy-hom-Coseq A B f g → Id f g
eq-htpy-hom-Coseq A B f g =
  map-inv-is-equiv (is-equiv-htpy-eq-hom-Coseq A B f g)

{- We define composition of morphisms of cosequences -}

value-comp-hom-Coseq :
  {l1 l2 l3 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (C : Coseq-UU l3) →
  (g : hom-Coseq B C) (f : hom-Coseq A B) →
  (n : ℕ) → (type-Coseq A n) → (type-Coseq C n)
value-comp-hom-Coseq A B C g f n =
  ( map-hom-Coseq B C g n) ∘ ( map-hom-Coseq A B f n)

naturality-comp-hom-Coseq :
  {l1 l2 l3 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (C : Coseq-UU l3) →
  (g : hom-Coseq B C) (f : hom-Coseq A B) (n : ℕ) → 
  ( ( map-Coseq C n) ∘ (value-comp-hom-Coseq A B C g f (succ-ℕ n))) ~
  ( ( value-comp-hom-Coseq A B C g f n) ∘ (map-Coseq A n))
naturality-comp-hom-Coseq A B C g f n =
  ( ( naturality-hom-Coseq B C g n) ·r (map-hom-Coseq A B f (succ-ℕ n))) ∙h
  ( ( map-hom-Coseq B C g n) ·l (naturality-hom-Coseq A B f n))

comp-hom-Coseq :
  {l1 l2 l3 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (C : Coseq-UU l3) →
  (g : hom-Coseq B C) (f : hom-Coseq A B) → hom-Coseq A C
comp-hom-Coseq A B C g f =
  pair ( value-comp-hom-Coseq A B C g f)
       ( naturality-comp-hom-Coseq A B C g f)

associative-comp-hom-Coseq' :
  {l1 l2 l3 l4 : Level}
  (A : Coseq-UU l1) (B : Coseq-UU l2) (C : Coseq-UU l3) (D : Coseq-UU l4)
  (h : hom-Coseq C D) (g : hom-Coseq B C) (f : hom-Coseq A B) →
  htpy-hom-Coseq A D
    ( comp-hom-Coseq A B D (comp-hom-Coseq B C D h g) f)
    ( comp-hom-Coseq A C D h (comp-hom-Coseq A B C g f))
associative-comp-hom-Coseq' A B C D h g f =
  pair
    ( λ n → refl-htpy)
    ( λ n x →
      inv
        ( inv-con
          ( ( ( pr2 h n (pr1 g (succ-ℕ n) (pr1 f (succ-ℕ n) x))) ∙
              ( ap (pr1 h n) (pr2 g n (pr1 f (succ-ℕ n) x)))) ∙ 
            ( ap (λ a → pr1 h n (pr1 g n a)) (pr2 f n x)))
          ( refl)
          ( ( pr2 h n (pr1 g (succ-ℕ n) (pr1 f (succ-ℕ n) x))) ∙
            ( ap 
              ( pr1 h n)
              ( ( pr2 g n (pr1 f (succ-ℕ n) x)) ∙ 
                ( ap (pr1 g n) (pr2 f n x)))))
          ( ( right-unit) ∙
            ( ( assoc
                ( pr2 h n (pr1 g (succ-ℕ n) (pr1 f (succ-ℕ n) x)))
                ( ap (pr1 h n) (pr2 g n (pr1 f (succ-ℕ n) x)))
                ( ap (pr1 h n ∘ pr1 g n) (pr2 f n x))) ∙
              ( ap
                ( concat
                  ( pr2 h n (pr1 g (succ-ℕ n) (pr1 f (succ-ℕ n) x)))
                  ( pr1 h n (pr1 g n (pr1 f n (pr2 A n x)))))
                ( ( ap
                    ( concat
                      ( ap (pr1 h n) (pr2 g n (pr1 f (succ-ℕ n) x)))
                      ( pr1 h n (pr1 g n (pr1 f n (pr2 A n x)))))
                    ( ap-comp (pr1 h n) (pr1 g n) (pr2 f n x))) ∙
                  ( inv
                    ( ap-concat
                      ( pr1 h n)
                      ( pr2 g n (pr1 f (succ-ℕ n) x))
                      ( ap (pr1 g n) (pr2 f n x))))))))))

associative-comp-hom-Coseq :
  {l1 l2 l3 l4 : Level}
  (A : Coseq-UU l1) (B : Coseq-UU l2) (C : Coseq-UU l3) (D : Coseq-UU l4)
  (h : hom-Coseq C D) (g : hom-Coseq B C) (f : hom-Coseq A B) →
  Id ( comp-hom-Coseq A B D (comp-hom-Coseq B C D h g) f)
     ( comp-hom-Coseq A C D h (comp-hom-Coseq A B C g f))
associative-comp-hom-Coseq A B C D h g f =
  eq-htpy-hom-Coseq A D
    ( comp-hom-Coseq A B D (comp-hom-Coseq B C D h g) f)
    ( comp-hom-Coseq A C D h (comp-hom-Coseq A B C g f))
    ( associative-comp-hom-Coseq' A B C D h g f)

--------------------------------------------------------------------------------

{- We introduce simpler homotopies of morphisms between cosequences -}

Naturality-simple-htpy-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f g : hom-Coseq A B)
  (H : (n : ℕ) → (map-hom-Coseq A B f n) ~ (map-hom-Coseq A B g n))
  → UU (l1 ⊔ l2)
Naturality-simple-htpy-hom-Coseq A B f g H =
  (n : ℕ) →
  ( ( (map-Coseq B n) ·l (H (succ-ℕ n))) ∙h
    ( naturality-hom-Coseq A B g n)) ~
  ( ( naturality-hom-Coseq A B f n) ∙h
    ( (H n) ·r (map-Coseq A n)))

simple-htpy-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) →
  hom-Coseq A B → hom-Coseq A B → UU (l1 ⊔ l2)
simple-htpy-hom-Coseq A B f g =
  Σ ( (n : ℕ) → (map-hom-Coseq A B f n) ~ (map-hom-Coseq A B g n))
    ( Naturality-simple-htpy-hom-Coseq A B f g)

value-simple-htpy-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2)
  (f g : hom-Coseq A B) → simple-htpy-hom-Coseq A B f g → (n : ℕ) →
  (map-hom-Coseq A B f n) ~ (map-hom-Coseq A B g n)
value-simple-htpy-hom-Coseq A B f g H = pr1 H

naturality-simple-htpy-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2)
  (f g : hom-Coseq A B) (H : simple-htpy-hom-Coseq A B f g) →
  Naturality-simple-htpy-hom-Coseq A B f g (value-simple-htpy-hom-Coseq A B f g H)
naturality-simple-htpy-hom-Coseq A B f g H = pr2 H

{- We show that simple-htpy-hom-Coseq also characterizes the identity type of 
   hom-Coseq. -}

refl-simple-htpy-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  simple-htpy-hom-Coseq A B f f
refl-simple-htpy-hom-Coseq A B f =
  pair ((λ n → refl-htpy)) (λ n → inv-htpy right-unit-htpy)

simple-htpy-eq-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2)
  (f g : hom-Coseq A B) → Id f g → simple-htpy-hom-Coseq A B f g
simple-htpy-eq-hom-Coseq A B f .f refl = refl-simple-htpy-hom-Coseq A B f

is-contr-total-simple-htpy-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  is-contr (Σ (hom-Coseq A B) (simple-htpy-hom-Coseq A B f))
is-contr-total-simple-htpy-hom-Coseq A B f =
  is-contr-total-Eq-structure
    ( λ g G → Naturality-simple-htpy-hom-Coseq A B f (pair g G))
    ( is-contr-total-Eq-Π
      ( λ n gn → map-hom-Coseq A B f n ~ gn)
      ( λ n → is-contr-total-htpy (map-hom-Coseq A B f n)))
    ( pair (map-hom-Coseq A B f) (λ n → refl-htpy))
    ( is-contr-total-Eq-Π
      ( λ n Gn →
        ( ((map-Coseq B n) ·l refl-htpy) ∙h Gn) ~
        ( ((naturality-hom-Coseq A B f n) ∙h refl-htpy)))
      ( λ n →
        is-contr-equiv
          ( Σ ( ( (map-Coseq B n) ∘ (map-hom-Coseq A B f (succ-ℕ n))) ~
                ( (map-hom-Coseq A B f n) ∘ (map-Coseq A n)))
              ( (λ Gn → Gn ~ (naturality-hom-Coseq A B f n))))
          ( equiv-tot ((λ Gn → equiv-concat-htpy' Gn right-unit-htpy)))
          ( is-contr-total-htpy' (naturality-hom-Coseq A B f n))))

is-equiv-simple-htpy-eq-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2)
  (f g : hom-Coseq A B) → is-equiv (simple-htpy-eq-hom-Coseq A B f g)
is-equiv-simple-htpy-eq-hom-Coseq A B f =
  fundamental-theorem-id f
    ( refl-simple-htpy-hom-Coseq A B f)
    ( is-contr-total-simple-htpy-hom-Coseq A B f)
    ( simple-htpy-eq-hom-Coseq A B f)

equiv-simple-htpy-eq-hom-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f g : hom-Coseq A B) →
  Id f g ≃ (simple-htpy-hom-Coseq A B f g)
equiv-simple-htpy-eq-hom-Coseq A B f g =
  pair
    ( simple-htpy-eq-hom-Coseq A B f g)
    ( is-equiv-simple-htpy-eq-hom-Coseq A B f g)

eq-simple-htpy-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2)
  (f g : hom-Coseq A B) → simple-htpy-hom-Coseq A B f g → Id f g
eq-simple-htpy-hom-Coseq A B f g =
  map-inv-is-equiv (is-equiv-simple-htpy-eq-hom-Coseq A B f g)

--------------------------------------------------------------------------------

{- We introduce cones on a type sequence. -}

constant-Coseq : {l : Level} (X : UU l) → Coseq-UU l
constant-Coseq X = pair (λ n → X) (λ n → id)

cone-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) (X : UU l2) → UU (l1 ⊔ l2)
cone-Coseq A X = hom-Coseq (constant-Coseq X) A

map-cone-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( n : ℕ) → X → type-Coseq A n
map-cone-Coseq A c = pr1 c

triangle-cone-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( n : ℕ) →
  ( (map-Coseq A n) ∘ (map-cone-Coseq A c (succ-ℕ n))) ~
  ( map-cone-Coseq A c n)
triangle-cone-Coseq A c = pr2 c

--------------------------------------------------------------------------------

{- We characterize the identity type of cone-Coseq. -}

naturality-htpy-cone-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c c' : cone-Coseq A X) →
  ( H : (n : ℕ) → (map-cone-Coseq A c n) ~ (map-cone-Coseq A c' n)) →
  UU (l1 ⊔ l2)
naturality-htpy-cone-Coseq A {X} =
  Naturality-simple-htpy-hom-Coseq (constant-Coseq X) A

htpy-cone-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} →
  ( c c' : cone-Coseq A X) → UU (l1 ⊔ l2)
htpy-cone-Coseq A {X} = simple-htpy-hom-Coseq (constant-Coseq X) A

refl-htpy-cone-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  htpy-cone-Coseq A c c
refl-htpy-cone-Coseq A {X} = refl-simple-htpy-hom-Coseq (constant-Coseq X) A

htpy-cone-Coseq-eq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c c' : cone-Coseq A X) →
  Id c c' → htpy-cone-Coseq A c c'
htpy-cone-Coseq-eq A {X} = simple-htpy-eq-hom-Coseq (constant-Coseq X) A

is-contr-total-htpy-cone-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  is-contr (Σ (cone-Coseq A X) (htpy-cone-Coseq A c))
is-contr-total-htpy-cone-Coseq A {X} =
  is-contr-total-simple-htpy-hom-Coseq (constant-Coseq X) A

is-equiv-htpy-cone-Coseq-eq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c c' : cone-Coseq A X) →
  is-equiv (htpy-cone-Coseq-eq A c c')
is-equiv-htpy-cone-Coseq-eq A {X} =
  is-equiv-simple-htpy-eq-hom-Coseq (constant-Coseq X) A

eq-htpy-cone-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c c' : cone-Coseq A X) →
  htpy-cone-Coseq A c c' → Id c c'
eq-htpy-cone-Coseq A {X} = eq-simple-htpy-hom-Coseq (constant-Coseq X) A

equiv-htpy-cone-Coseq-eq :
  { l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c c' : cone-Coseq A X) →
  Id c c' ≃ (htpy-cone-Coseq A c c')
equiv-htpy-cone-Coseq-eq A {X} =
  equiv-simple-htpy-eq-hom-Coseq (constant-Coseq X) A

--------------------------------------------------------------------------------

{- We introduce sequential limits. -}

hom-constant-Coseq :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  (X → Y) → hom-Coseq (constant-Coseq X) (constant-Coseq Y)
hom-constant-Coseq f =
  pair (λ n → f) (λ n → refl-htpy)

cone-map-Coseq' :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( Y : UU l3) → (Y → X) → cone-Coseq A Y
cone-map-Coseq' A c Y h = 
  pair
    ( λ n → (map-cone-Coseq A c n) ∘ h)
    ( λ n → (triangle-cone-Coseq A c n) ·r h)

cone-map-Coseq :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  (Y : UU l3) → (Y → X) → cone-Coseq A Y
cone-map-Coseq A {X} c Y h =
  comp-hom-Coseq (constant-Coseq Y) (constant-Coseq X) A c
    ( hom-constant-Coseq h)

compute-cone-map-Coseq' :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  {Y : UU l3} (h : Y → X) →
  htpy-cone-Coseq A (cone-map-Coseq' A c Y h) (cone-map-Coseq A c Y h)
compute-cone-map-Coseq' A {X} c {Y} h =
  pair (λ n → refl-htpy) (λ n → refl-htpy)

compute-cone-map-Coseq :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  {Y : UU l3} (h : Y → X) →
  Id (cone-map-Coseq' A c Y h) (cone-map-Coseq A c Y h)
compute-cone-map-Coseq A c h =
  eq-htpy-cone-Coseq A
    ( cone-map-Coseq' A c _ h)
    ( cone-map-Coseq A c _ h)
    ( compute-cone-map-Coseq' A c h)

universal-property-limit-Coseq :
  ( l : Level) {l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2}
  ( c : cone-Coseq A X) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-limit-Coseq l A c =
  (Y : UU l) → is-equiv (cone-map-Coseq A c Y)

--------------------------------------------------------------------------------

{- We introduce the canonical sequential limit. -}

limit-Coseq :
  {l : Level} (A : Coseq-UU l) → UU l
limit-Coseq A =
  Σ ( (n : ℕ) → type-Coseq A n)
    ( λ a → (n : ℕ) → Id (map-Coseq A n (a (succ-ℕ n))) (a n))

map-cone-limit-Coseq :
  {l : Level} (A : Coseq-UU l) (x : limit-Coseq A) (n : ℕ) →
  type-Coseq A n
map-cone-limit-Coseq A x = pr1 x

triangle-cone-limit-Coseq :
  {l : Level} (A : Coseq-UU l) (x : limit-Coseq A) (n : ℕ) →
  Id ( map-Coseq A n (map-cone-limit-Coseq A x (succ-ℕ n)))
     ( map-cone-limit-Coseq A x n)
triangle-cone-limit-Coseq A x = pr2 x

{- We introduce a second canonical sequential limit. -}

limit-Coseq' : {l : Level} (A : Coseq-UU l) → UU l
limit-Coseq' A = cone-Coseq A unit

equiv-limit-Coseq :
  {l : Level} (A : Coseq-UU l) →
  limit-Coseq' A ≃ limit-Coseq A
equiv-limit-Coseq A =
  equiv-Σ
    ( λ a → (n : ℕ) → Id (map-Coseq A n (a (succ-ℕ n))) (a n))
    ( equiv-map-Π (λ n → equiv-ev-star' (type-Coseq A n)))
    ( λ a →
      equiv-map-Π
        ( λ n →
          equiv-ev-star (λ x → Id (map-Coseq A n (a (succ-ℕ n) x)) (a n x))))

--------------------------------------------------------------------------------

{- We characterize the identity type of the canonical sequential limit. -}

Eq-limit-Coseq :
  { l1 : Level} (A : Coseq-UU l1) (x y : limit-Coseq A) → UU l1
Eq-limit-Coseq A x y =
  Σ ( ( map-cone-limit-Coseq A x) ~
      ( map-cone-limit-Coseq A y))
    ( λ H → (n : ℕ) →
      Id ( ( ap (map-Coseq A n) (H (succ-ℕ n))) ∙
           ( triangle-cone-limit-Coseq A y n))
         ( ( triangle-cone-limit-Coseq A x n) ∙
           ( H n)))

refl-Eq-limit-Coseq :
  { l1 : Level} (A : Coseq-UU l1) (x : limit-Coseq A) →
  Eq-limit-Coseq A x x
refl-Eq-limit-Coseq A x =
  pair refl-htpy (inv-htpy right-unit-htpy)

Eq-limit-Coseq-eq :
  { l1 : Level} (A : Coseq-UU l1) (x y : limit-Coseq A) →
  Id x y → Eq-limit-Coseq A x y
Eq-limit-Coseq-eq A x .x refl =
  refl-Eq-limit-Coseq A x

is-contr-total-Eq-limit-Coseq :
  { l1 : Level} (A : Coseq-UU l1) (x : limit-Coseq A) →
  is-contr
    ( Σ (limit-Coseq A) (Eq-limit-Coseq A x))
is-contr-total-Eq-limit-Coseq A x =
  is-contr-total-Eq-structure
    ( λ y q (H : (n : ℕ) → Id (pr1 x n) (y n)) →
      (n : ℕ) →
        Id ((ap (map-Coseq A n) (H (succ-ℕ n))) ∙ (q n)) ((pr2 x n) ∙ (H n)))
    ( is-contr-total-Eq-Π
      ( λ n yn → Id (pr1 x n) yn)
      ( λ n → is-contr-total-path (pr1 x n)))
    ( pair (pr1 x) refl-htpy)
    ( is-contr-total-Eq-Π
      ( λ n q → Id q ((pr2 x n) ∙ refl))
      ( λ n → is-contr-total-path' ((pr2 x n) ∙ refl)))

is-equiv-Eq-limit-Coseq :
  { l1 : Level} (A : Coseq-UU l1) (x y : limit-Coseq A) →
  is-equiv (Eq-limit-Coseq-eq A x y)
is-equiv-Eq-limit-Coseq A x =
  fundamental-theorem-id x
    ( refl-Eq-limit-Coseq A x)
    ( is-contr-total-Eq-limit-Coseq A x)
    ( Eq-limit-Coseq-eq A x)

eq-Eq-limit-Coseq :
  { l1 : Level} (A : Coseq-UU l1) {x y : limit-Coseq A} →
  Eq-limit-Coseq A x y → Id x y
eq-Eq-limit-Coseq A {x} {y} =
  map-inv-is-equiv (is-equiv-Eq-limit-Coseq A x y)

--------------------------------------------------------------------------------

{- We give a second characterization of the identity type of the canonical
   sequential colimit, expressed as a canonical sequential colimit. -}

type-coseq-Eq-limit-Coseq' :
  {l : Level} (A : Coseq-UU l) (x y : limit-Coseq A) →
  (n : ℕ) → UU l
type-coseq-Eq-limit-Coseq' A x y n =
  Id ( map-cone-limit-Coseq A x n)
     ( map-cone-limit-Coseq A y n)

map-coseq-Eq-limit-Coseq' :
  {l : Level} (A : Coseq-UU l) (x y : limit-Coseq A) (n : ℕ) →
  type-coseq-Eq-limit-Coseq' A x y (succ-ℕ n) →
  type-coseq-Eq-limit-Coseq' A x y n
map-coseq-Eq-limit-Coseq' A x y n p =
  ( inv (triangle-cone-limit-Coseq A x n)) ∙
  ( ( ap (map-Coseq A n) p) ∙
    ( triangle-cone-limit-Coseq A y n))

coseq-Eq-limit-Coseq' :
  {l : Level} (A : Coseq-UU l) (x y : limit-Coseq A) → Coseq-UU l
coseq-Eq-limit-Coseq' A x y =
  pair ( type-coseq-Eq-limit-Coseq' A x y)
       ( map-coseq-Eq-limit-Coseq' A x y)

Eq-limit-Coseq' :
  {l : Level} (A : Coseq-UU l) (x y : limit-Coseq A) → UU l
Eq-limit-Coseq' A x y =
  limit-Coseq (coseq-Eq-limit-Coseq' A x y)

refl-Eq-limit-Coseq' :
  {l : Level} (A : Coseq-UU l) (x : limit-Coseq A) →
  Eq-limit-Coseq' A x x
refl-Eq-limit-Coseq' A x =
  pair (λ n → refl) (λ n → left-inv (triangle-cone-limit-Coseq A x n))

Eq-limit-Coseq-eq' :
  {l : Level} (A : Coseq-UU l) (x y : limit-Coseq A) →
  Id x y → Eq-limit-Coseq' A x y
Eq-limit-Coseq-eq' A x .x refl =
  refl-Eq-limit-Coseq' A x

is-contr-total-Eq-limit-Coseq' :
  {l : Level} (A : Coseq-UU l) (x : limit-Coseq A) →
  is-contr
    ( Σ (limit-Coseq A) (Eq-limit-Coseq' A x))
is-contr-total-Eq-limit-Coseq' A x =
  is-contr-total-Eq-structure
    ( λ a H (p : (n : ℕ) → Id (map-cone-limit-Coseq A x n) (a n)) →
      (n : ℕ) →
      Id ( inv
           ( triangle-cone-limit-Coseq A x n) ∙
           ( ( ap (map-Coseq A n) (p (succ-ℕ n))) ∙ (H n)))
         ( p n))
    ( is-contr-total-htpy (map-cone-limit-Coseq A x))
    ( pair (map-cone-limit-Coseq A x) refl-htpy)
    ( is-contr-equiv'
      ( Σ ( (n : ℕ) →
            Id ( map-Coseq A n
                 ( map-cone-limit-Coseq A x (succ-ℕ n)))
               ( map-cone-limit-Coseq A x n))
          ( λ p →
            (n : ℕ) → Id (triangle-cone-limit-Coseq A x n) (p n)))
      ( equiv-tot
        ( λ p →
          equiv-map-Π
            ( λ n →
              ( equiv-inv refl (inv (pr2 x n) ∙ p n)) ∘e
              ( ( equiv-inv-con (pr2 x n) refl (p n)) ∘e
                ( equiv-concat right-unit (p n))))))
      ( is-contr-total-htpy (triangle-cone-limit-Coseq A x)))

is-equiv-Eq-limit-Coseq-eq' :
  {l : Level} (A : Coseq-UU l) (x y : limit-Coseq A) →
  is-equiv (Eq-limit-Coseq-eq' A x y)
is-equiv-Eq-limit-Coseq-eq' A x =
  fundamental-theorem-id x
    ( refl-Eq-limit-Coseq' A x)
    ( is-contr-total-Eq-limit-Coseq' A x)
    ( Eq-limit-Coseq-eq' A x)

--------------------------------------------------------------------------------

{- We equip the canonical sequential limit with the structure of a cone. -}

cone-limit-Coseq :
  {l1 : Level} (A : Coseq-UU l1) → cone-Coseq A (limit-Coseq A)
cone-limit-Coseq A =
  pair ( λ n a → map-cone-limit-Coseq A a n)
       ( λ n a → triangle-cone-limit-Coseq A a n)

--------------------------------------------------------------------------------

{- We show that the canonical sequential limit satisfies the universal property
   of sequential limits. -}

gap-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) {Y : UU l2} → cone-Coseq A Y →
  Y → limit-Coseq A
gap-Coseq A c y =
  pair ( λ n → map-cone-Coseq A c n y)
       ( λ n → triangle-cone-Coseq A c n y)

issec-gap-Coseq' :
  { l1 l2 : Level} (A : Coseq-UU l1) {Y : UU l2} (c : cone-Coseq A Y) →
  htpy-cone-Coseq A
    ( cone-map-Coseq A (cone-limit-Coseq A) Y (gap-Coseq A c))
    ( c)
issec-gap-Coseq' A {Y} c =
  pair (λ n → refl-htpy) (λ n x → inv right-unit ∙ inv right-unit)

issec-gap-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) (Y : UU l2) →
  ((cone-map-Coseq A (cone-limit-Coseq A) Y) ∘ (gap-Coseq A {Y})) ~ id
issec-gap-Coseq A Y c =
  eq-htpy-cone-Coseq A
    ( cone-map-Coseq A
      ( cone-limit-Coseq A)
      ( Y)
      ( gap-Coseq A c))
    ( c)
    ( issec-gap-Coseq' A c)

isretr-gap-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) (Y : UU l2) →
  ((gap-Coseq A {Y}) ∘ (cone-map-Coseq A (cone-limit-Coseq A) Y)) ~ id
isretr-gap-Coseq A Y h =
  eq-htpy (λ y →
    eq-Eq-limit-Coseq A
      (pair (λ n → refl) (λ n → inv right-unit ∙ inv right-unit)))

is-equiv-cone-map-cone-limit-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) (Y : UU l2) →
  is-equiv (cone-map-Coseq A (cone-limit-Coseq A) Y)
is-equiv-cone-map-cone-limit-Coseq A Y =
  is-equiv-has-inverse
    ( gap-Coseq A)
    ( issec-gap-Coseq A Y)
    ( isretr-gap-Coseq A Y)

universal-property-limit-limit-Coseq :
  ( l : Level) {l1 : Level} (A : Coseq-UU l1) →
  universal-property-limit-Coseq l A (cone-limit-Coseq A)
universal-property-limit-limit-Coseq l A Y =
  is-equiv-cone-map-cone-limit-Coseq A Y

--------------------------------------------------------------------------------

{- Unique mapping property for sequential limits. -}

unique-mapping-property-limit-Coseq' :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-limit-Coseq l A c)
  { Y : UU l3} (c' : cone-Coseq A Y) →
  is-contr (fib (cone-map-Coseq A c Y) c')
unique-mapping-property-limit-Coseq' A c up-X {Y} =
  is-contr-map-is-equiv (up-X Y)

map-universal-property-limit-Coseq :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-limit-Coseq l A c) →
  { Y : UU l3} (c' : cone-Coseq A Y) → Y → X
map-universal-property-limit-Coseq A c up-X c' =
  pr1 (center (unique-mapping-property-limit-Coseq' A c up-X c'))

path-universal-property-limit-Coseq :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-limit-Coseq l A c) →
  { Y : UU l3} (c' : cone-Coseq A Y) →
  Id ( cone-map-Coseq A c Y
       ( map-universal-property-limit-Coseq A c up-X c'))
     ( c')
path-universal-property-limit-Coseq A c up-X c' =
  pr2 (center (unique-mapping-property-limit-Coseq' A c up-X c'))

unique-mapping-property-limit-Coseq :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-limit-Coseq l A c) →
  { Y : UU l3} (c' : cone-Coseq A Y) →
  is-contr
    ( Σ ( Y → X)
        ( λ h → htpy-cone-Coseq A (cone-map-Coseq A c Y h) c'))
unique-mapping-property-limit-Coseq {l3 = l3} A c up-X {Y} c' =
  is-contr-equiv'
    ( fib (cone-map-Coseq A c Y) c')
    ( equiv-tot
      ( λ h → equiv-htpy-cone-Coseq-eq A (cone-map-Coseq A c Y h) c'))
    ( unique-mapping-property-limit-Coseq' A c up-X c')

htpy-universal-property-limit-Coseq :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-limit-Coseq l A c) →
  { Y : UU l3} (c' : cone-Coseq A Y) →
  htpy-cone-Coseq A
    ( cone-map-Coseq A c Y
      ( map-universal-property-limit-Coseq A c up-X c'))
    ( c')
htpy-universal-property-limit-Coseq A c up-X {Y} c' =
  htpy-cone-Coseq-eq A
    ( cone-map-Coseq A c Y
      ( map-universal-property-limit-Coseq A c up-X c'))
    ( c')
    ( path-universal-property-limit-Coseq A c up-X c')

uniqueness-map-limit-Coseq' :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-limit-Coseq l A c)
  { Y : UU l3} (c' : cone-Coseq A Y) →
  ( h : Y → X) (H : Id (cone-map-Coseq A c Y h) c')
  ( h' : Y → X) (H' : Id (cone-map-Coseq A c Y h') c') →
  h ~ h'
uniqueness-map-limit-Coseq' A c up-X c' h H h' H' =
  htpy-eq
    ( ap pr1
      ( eq-is-contr'
        ( unique-mapping-property-limit-Coseq' A c up-X c')
        ( pair h H)
        ( pair h' H')))

uniqueness-map-limit-Coseq :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-limit-Coseq l A c) →
  { Y : UU l3} (c' : cone-Coseq A Y)
  ( h : Y → X) (H : htpy-cone-Coseq A (cone-map-Coseq A c Y h) c')
  ( h' : Y → X) (H' : htpy-cone-Coseq A (cone-map-Coseq A c Y h') c') →
  h ~ h'
uniqueness-map-limit-Coseq A c up-X c' h H h' H' =
  htpy-eq
    ( ap pr1
      ( eq-is-contr'
        ( unique-mapping-property-limit-Coseq A c up-X c')
        ( pair h H)
        ( pair h' H')))

--------------------------------------------------------------------------------
    
{- We show a 3-for-2 property of sequential limits. -}

compose-cone-map-Coseq :
  { l1 l2 l3 l4 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X)
  { Y : UU l3} {Z : UU l4} (h : Y → X) (k : Z → Y) →
  Id ( cone-map-Coseq A (cone-map-Coseq A c Y h) Z k)
     ( cone-map-Coseq A c Z (h ∘ k))
compose-cone-map-Coseq A {X} c {Y} {Z} h k =
  associative-comp-hom-Coseq
    ( constant-Coseq Z)
    ( constant-Coseq Y)
    ( constant-Coseq X)
    ( A)
    ( c)
    ( hom-constant-Coseq h)
    ( hom-constant-Coseq k)
    
module 3-for-2-limit-Coseq
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} {Y : UU l3}
  ( c : cone-Coseq A X) (c' : cone-Coseq A Y) (h : Y → X)
  ( e : htpy-cone-Coseq A (cone-map-Coseq A c Y h) c')
  where

  triangle-cone-cone-Coseq :
    {l4 : Level} (Z : UU  l4) →
      ( cone-map-Coseq A c' Z) ~
      ( ( cone-map-Coseq A c Z) ∘ (λ (k : Z → Y) → h ∘ k))
  triangle-cone-cone-Coseq Z k =
    ( ap
      ( λ t → cone-map-Coseq A t Z k)
      ( inv (eq-htpy-cone-Coseq A (cone-map-Coseq A c Y h) c' e))) ∙
    ( compose-cone-map-Coseq A c h k)
    
  is-equiv-universal-property-limit-Coseq :
    ({l : Level} → universal-property-limit-Coseq l A c) →
    ({l : Level} → universal-property-limit-Coseq l A c') →
    is-equiv h
  is-equiv-universal-property-limit-Coseq up-X up-Y =
    is-equiv-is-equiv-postcomp h (λ {l} Z →
      is-equiv-right-factor
        ( cone-map-Coseq A c' Z)
        ( cone-map-Coseq A c Z)
        ( λ k → h ∘ k)
        ( triangle-cone-cone-Coseq Z)
        ( up-X Z)
        ( up-Y Z))

  universal-property-limit-is-equiv-Coseq' :
    ({l : Level} → universal-property-limit-Coseq l A c) →
    is-equiv h →
    ({l : Level} → universal-property-limit-Coseq l A c')
  universal-property-limit-is-equiv-Coseq' up-X is-equiv-h Z =
    is-equiv-comp
      ( cone-map-Coseq A c' Z)
      ( cone-map-Coseq A c Z)
      ( λ k → h ∘ k)
      ( triangle-cone-cone-Coseq Z)
      ( is-equiv-postcomp-is-equiv h is-equiv-h Z)
      ( up-X Z)

  universal-property-limit-is-equiv-Coseq :
    ({l : Level} → universal-property-limit-Coseq l A c') →
    is-equiv h →
    ({l : Level} → universal-property-limit-Coseq l A c)
  universal-property-limit-is-equiv-Coseq up-Y is-equiv-h Z =
    is-equiv-left-factor
      ( cone-map-Coseq A c' Z)
      ( cone-map-Coseq A c Z)
      ( λ k → h ∘ k)
      ( triangle-cone-cone-Coseq Z)
      ( up-Y Z)
      ( is-equiv-postcomp-is-equiv h is-equiv-h Z)

open 3-for-2-limit-Coseq public

--------------------------------------------------------------------------------

{- We prove the uniquely uniqueness of sequential limits. -}

uniquely-uniqueness-limit-Coseq :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} {Y : UU l3} →
  ( c : cone-Coseq A X) (c' : cone-Coseq A Y) →
  ( {l : Level} → universal-property-limit-Coseq l A c) →
  ( {l : Level} → universal-property-limit-Coseq l A c') →
  is-contr (Σ (Y ≃ X)
    (λ e → htpy-cone-Coseq A (cone-map-Coseq A c Y (map-equiv e)) c'))
uniquely-uniqueness-limit-Coseq A {X} {Y} c c' up-X up-Y =
  is-contr-total-Eq-substructure
    ( unique-mapping-property-limit-Coseq A c up-X c')
    ( is-subtype-is-equiv)
    ( map-universal-property-limit-Coseq A c up-X c')
    ( htpy-universal-property-limit-Coseq A c up-X c')
    ( is-equiv-universal-property-limit-Coseq A c c'
      ( map-universal-property-limit-Coseq A c up-X c')
      ( htpy-universal-property-limit-Coseq A c up-X c')
      ( up-X)
      ( up-Y))

--------------------------------------------------------------------------------

{- We simplify the proof that something is a limit of a cosequence. -}

is-limit-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  UU (l1 ⊔ l2)
is-limit-Coseq A {X} c = is-equiv (gap-Coseq A c)

universal-property-limit-is-limit-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  is-limit-Coseq A c → {l : Level} → universal-property-limit-Coseq l A c
universal-property-limit-is-limit-Coseq A {X} c H =
  universal-property-limit-is-equiv-Coseq' A
    ( cone-limit-Coseq A)
    ( c)
    ( gap-Coseq A c)
    ( issec-gap-Coseq' A c)
    ( λ {l'} → universal-property-limit-limit-Coseq l' A)
    ( H)

is-limit-universal-property-limit-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ({l : Level} → universal-property-limit-Coseq l A c) → is-limit-Coseq A c
is-limit-universal-property-limit-Coseq A {X} c up-c =
  is-equiv-universal-property-limit-Coseq A
    ( cone-limit-Coseq A)
    ( c)
    ( gap-Coseq A c)
    ( issec-gap-Coseq' A c)
    ( λ {l'} → universal-property-limit-limit-Coseq l' A)
    ( up-c)

--------------------------------------------------------------------------------

{- We define the functorial action of limits -}

limit-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  limit-Coseq A → limit-Coseq B
limit-hom-Coseq A B f =
  gap-Coseq B
    ( comp-hom-Coseq (constant-Coseq (limit-Coseq A))
    ( A)
    ( B)
    ( f)
    ( cone-limit-Coseq A))

eq-limit-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) → 
  Id ( comp-hom-Coseq
       ( constant-Coseq (limit-Coseq A))
       ( constant-Coseq (limit-Coseq B))
       ( B)
       ( cone-limit-Coseq B)
       ( hom-constant-Coseq (limit-hom-Coseq A B f)))
     ( comp-hom-Coseq (constant-Coseq (limit-Coseq A)) A B f
       ( cone-limit-Coseq A))
eq-limit-hom-Coseq A B f =
  issec-gap-Coseq B
    ( limit-Coseq A)
    ( comp-hom-Coseq (constant-Coseq (limit-Coseq A)) A B f
      ( cone-limit-Coseq A))

--------------------------------------------------------------------------------

{- We prove uniqueness of limit-hom-Coseq -}

uniqueness-limit-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  ( h : limit-Coseq A → limit-Coseq B)
  ( p : Id ( cone-map-Coseq B (cone-limit-Coseq B) (limit-Coseq A) h)
           ( comp-hom-Coseq (constant-Coseq (limit-Coseq A)) A B f
             ( cone-limit-Coseq A))) →
  Id (pair (limit-hom-Coseq A B f) (eq-limit-hom-Coseq A B f))
     (pair h p)
uniqueness-limit-hom-Coseq A B f h p =
  eq-is-contr'
    ( unique-mapping-property-limit-Coseq' B
      ( cone-limit-Coseq B)
      ( λ {l} → universal-property-limit-limit-Coseq l B)
      ( comp-hom-Coseq (constant-Coseq (limit-Coseq A)) A B f
        ( cone-limit-Coseq A)))
    ( pair (limit-hom-Coseq A B f) (eq-limit-hom-Coseq A B f))
    ( pair h p)

eq-uniqueness-limit-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  ( h : limit-Coseq A → limit-Coseq B)
  ( p : Id ( cone-map-Coseq B (cone-limit-Coseq B) (limit-Coseq A) h)
           ( comp-hom-Coseq (constant-Coseq (limit-Coseq A)) A B f
             ( cone-limit-Coseq A))) →
  Id (limit-hom-Coseq A B f) h
eq-uniqueness-limit-hom-Coseq A B f h p =
  ap pr1 (uniqueness-limit-hom-Coseq A B f h p)
  
--------------------------------------------------------------------------------

{- We prove compositionality of limit-hom-Coseq -}

comp-hom-constant-Coseq :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {Z : UU l3} (g : Y → Z)
  (f : X  → Y) →
  Id ( hom-constant-Coseq (g ∘ f))
     ( comp-hom-Coseq
       ( constant-Coseq X)
       ( constant-Coseq Y)
       ( constant-Coseq Z)
       ( hom-constant-Coseq g)
       ( hom-constant-Coseq f))
comp-hom-constant-Coseq {X = X} {Y} {Z} g f =
   eq-htpy-hom-Coseq
    ( constant-Coseq X)
    ( constant-Coseq Z)
    ( hom-constant-Coseq (g ∘ f))
    ( comp-hom-Coseq
      ( constant-Coseq X)
      ( constant-Coseq Y)
      ( constant-Coseq Z)
      ( hom-constant-Coseq g)
      ( hom-constant-Coseq f))
    ( pair (λ n → refl-htpy) (λ n → refl-htpy))

comp-limit-hom-Coseq' :
  {l1 l2 l3 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (C : Coseq-UU l3)
  (g : hom-Coseq B C) (f : hom-Coseq A B) →
  Id ( limit-hom-Coseq A C (comp-hom-Coseq A B C g f))
     ( limit-hom-Coseq B C g ∘ limit-hom-Coseq A B f)
comp-limit-hom-Coseq' A B C g f =
  eq-uniqueness-limit-hom-Coseq A C
    ( comp-hom-Coseq A B C g f)
    ( limit-hom-Coseq B C g ∘ limit-hom-Coseq A B f)
    ( ( ap
        ( comp-hom-Coseq
          ( constant-Coseq (limit-Coseq A))
          ( constant-Coseq (limit-Coseq C))
          ( C)
          ( cone-limit-Coseq C))
        ( comp-hom-constant-Coseq
          ( limit-hom-Coseq B C g)
          ( limit-hom-Coseq A B f))) ∙
      ( ( inv
          ( associative-comp-hom-Coseq
            ( constant-Coseq (limit-Coseq A))
            ( constant-Coseq (limit-Coseq B))
            ( constant-Coseq (limit-Coseq C))
            ( C)
            ( cone-limit-Coseq C)
            ( hom-constant-Coseq (limit-hom-Coseq B C g))
            ( hom-constant-Coseq (limit-hom-Coseq A B f)))) ∙
        ( ( ap
            ( λ x →
              comp-hom-Coseq
                ( constant-Coseq (limit-Coseq A))
                ( constant-Coseq (limit-Coseq B))
                ( C)
                ( x)
                ( hom-constant-Coseq (limit-hom-Coseq A B f)))
            ( eq-limit-hom-Coseq B C g)) ∙
          ( ( associative-comp-hom-Coseq
              ( constant-Coseq (limit-Coseq A))
              ( constant-Coseq (limit-Coseq B))
              ( B)
              ( C)
              ( g)
              ( cone-limit-Coseq B)
              ( hom-constant-Coseq (limit-hom-Coseq A B f))) ∙
            ( ( ap
                ( comp-hom-Coseq (constant-Coseq (limit-Coseq A)) B C g)
                ( eq-limit-hom-Coseq A B f)) ∙
              ( inv
                ( associative-comp-hom-Coseq
                  ( constant-Coseq (limit-Coseq A))
                  ( A)
                  ( B)
                  ( C)
                  ( g)
                  ( f)
                  ( cone-limit-Coseq A))))))))

comp-limit-hom-Coseq :
  {l1 l2 l3 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (C : Coseq-UU l3)
  (g : hom-Coseq B C) (f : hom-Coseq A B) →
  ( limit-hom-Coseq A C (comp-hom-Coseq A B C g f)) ~
  ( limit-hom-Coseq B C g ∘ limit-hom-Coseq A B f)
comp-limit-hom-Coseq A B C g f =
  htpy-eq (comp-limit-hom-Coseq' A B C g f)

--------------------------------------------------------------------------------

{- We introduce the notion of diagonal fillers for morphisms of cosequences -}

has-filler-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D) (H : (k ∘ g) ~ (h ∘ f)) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
has-filler-square {A = A} {B} {C} {D} f g h k H =
  Σ ( C → B)
    ( λ j →
       Σ ( (j ∘ g) ~ f)
         ( λ T →
           Σ ( k ~ (h ∘ j))
             ( λ S → ((S ·r g) ∙h ( h ·l T)) ~ H)))

map-has-filler-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D) (H : (k ∘ g) ~ (h ∘ f)) →
  has-filler-square f g h k H → C → B
map-has-filler-square f g h k H J = pr1 J

upper-triangle-has-filler-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D) (H : (k ∘ g) ~ (h ∘ f)) →
  (J : has-filler-square f g h k H) →
  ((map-has-filler-square f g h k H J) ∘ g) ~ f
upper-triangle-has-filler-square f g h k H J = pr1 (pr2 J)

lower-triangle-has-filler-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D) (H : (k ∘ g) ~ (h ∘ f)) →
  (J : has-filler-square f g h k H) →
  k ~ (h ∘ (map-has-filler-square f g h k H J))
lower-triangle-has-filler-square f g h k H J = pr1 (pr2 (pr2 J))

coherence-has-filler-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D) (H : (k ∘ g) ~ (h ∘ f)) →
  (J : has-filler-square f g  h k H) →
  ( ( (lower-triangle-has-filler-square f g h k H J) ·r g) ∙h
    ( h ·l (upper-triangle-has-filler-square f g h k H J))) ~ H
coherence-has-filler-square f g h k H J = pr2 (pr2 (pr2 J))

has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  UU (l1 ⊔ l2)
has-filler-hom-Coseq A B f =
  (n : ℕ) →
  has-filler-square
    ( map-Coseq A n)
    ( map-hom-Coseq A B f (succ-ℕ n))
    ( map-hom-Coseq A B f n)
    ( map-Coseq B n)
    ( naturality-hom-Coseq A B f n)

map-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  has-filler-hom-Coseq A B f →
  (n : ℕ) → type-Coseq B (succ-ℕ n) → type-Coseq A n
map-has-filler-hom-Coseq A B f J n = pr1 (J n)

upper-triangle-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) (n : ℕ) →
  ( ( map-has-filler-hom-Coseq A B f J n) ∘
    ( map-hom-Coseq A B f (succ-ℕ n))) ~ (map-Coseq A n)
upper-triangle-has-filler-hom-Coseq A B f J n = pr1 (pr2 (J n))

lower-triangle-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) (n : ℕ) →
  (map-Coseq B n) ~
  ((map-hom-Coseq A B f n) ∘ (map-has-filler-hom-Coseq A B f J n))
lower-triangle-has-filler-hom-Coseq A B f J n = pr1 (pr2 (pr2 (J n)))

coherence-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) (n : ℕ) →
  ( ( ( lower-triangle-has-filler-hom-Coseq A B f J n) ·r
      ( map-hom-Coseq A B f (succ-ℕ n))) ∙h
    ( ( map-hom-Coseq A B f n) ·l
      ( upper-triangle-has-filler-hom-Coseq A B f J n))) ~
  ( naturality-hom-Coseq A B f n)
coherence-has-filler-hom-Coseq A B f J n = pr2 (pr2 (pr2 (J n)))

--------------------------------------------------------------------------------

{- We show that any morphism of cosequences that has a diagonal filler induces
   an equivalence on limits -}

point-map-inv-limit-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  has-filler-hom-Coseq A B f →
  ((n : ℕ) → type-Coseq B n) → ((n : ℕ) → type-Coseq A n)
point-map-inv-limit-has-filler-hom-Coseq A B f J y n =
  map-has-filler-hom-Coseq A B f J n (y (succ-ℕ n))

path-map-inv-limit-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) (y : (n : ℕ) → type-Coseq B n)
  (z : (n : ℕ) → Id (map-Coseq B n (y (succ-ℕ n))) (y n)) → (n : ℕ) →
  Id ( map-Coseq A n
       ( point-map-inv-limit-has-filler-hom-Coseq
         A B f J y (succ-ℕ n)))
     ( point-map-inv-limit-has-filler-hom-Coseq A B f J y n)
path-map-inv-limit-has-filler-hom-Coseq A B f J y z n =
  ( inv ( H (j' (y (succ-ℕ (succ-ℕ n)))))) ∙
  ( ( ap j (inv (K (y (succ-ℕ (succ-ℕ n)))))) ∙
    ( ap j (z (succ-ℕ n))))
  where
  j = map-has-filler-hom-Coseq A B f J n
  j' = map-has-filler-hom-Coseq A B f J (succ-ℕ n)
  H = upper-triangle-has-filler-hom-Coseq A B f J n
  K = lower-triangle-has-filler-hom-Coseq A B f J (succ-ℕ n)

map-inv-limit-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  has-filler-hom-Coseq A B f → limit-Coseq B → limit-Coseq A
map-inv-limit-has-filler-hom-Coseq A B f J =
  map-Σ
    ( λ x → (n : ℕ) → Id (map-Coseq A n (x (succ-ℕ n))) (x n))
    ( point-map-inv-limit-has-filler-hom-Coseq A B f J)
    ( path-map-inv-limit-has-filler-hom-Coseq A B f J)

--------------------------------------------------------------------------------

{- We show that the shifted cosequence as an equivalent limit -}

type-shift-Coseq : {l : Level} → Coseq-UU l → ℕ → UU l
type-shift-Coseq A n = type-Coseq A (succ-ℕ n)

map-shift-Coseq :
  {l : Level} (A : Coseq-UU l) (n : ℕ) →
  type-shift-Coseq A (succ-ℕ n) → type-shift-Coseq A n
map-shift-Coseq A n = map-Coseq A (succ-ℕ n)

shift-Coseq : {l : Level} → Coseq-UU l → Coseq-UU l
shift-Coseq A = pair (type-shift-Coseq A) (map-shift-Coseq A)

limit-shift-Coseq :
  {l : Level} → Coseq-UU l → UU l
limit-shift-Coseq A = limit-Coseq (shift-Coseq A)

map-counit-shift-Coseq :
  {l : Level} (A : Coseq-UU l) (n : ℕ) →
  type-Coseq A (succ-ℕ n) → type-Coseq A n
map-counit-shift-Coseq = map-Coseq

naturality-map-counit-shift-Coseq :
  {l : Level} (A : Coseq-UU l) →
  Naturality-hom-Coseq (shift-Coseq A) A (map-counit-shift-Coseq A)
naturality-map-counit-shift-Coseq A n = refl-htpy

counit-shift-Coseq : {l : Level} (A : Coseq-UU l) → hom-Coseq (shift-Coseq A) A
counit-shift-Coseq A =
  pair (map-counit-shift-Coseq A) (naturality-map-counit-shift-Coseq A)

cone-limit-shift-Coseq :
  {l : Level} (A : Coseq-UU l) → cone-Coseq A (limit-shift-Coseq A)
cone-limit-shift-Coseq A =
  comp-hom-Coseq
    ( constant-Coseq (limit-Coseq (shift-Coseq A)))
    ( shift-Coseq A)
    ( A)
    ( counit-shift-Coseq A)
    ( cone-limit-Coseq (shift-Coseq A))

map-limit-shift-Coseq' :
  {l : Level} (A : Coseq-UU l) → limit-shift-Coseq A → limit-Coseq A
map-limit-shift-Coseq' A =
  gap-Coseq A (cone-limit-shift-Coseq A)

map-limit-shift-Coseq :
  {l : Level} (A : Coseq-UU l) →
  limit-Coseq (shift-Coseq A) → limit-Coseq A
map-limit-shift-Coseq A =
  limit-hom-Coseq (shift-Coseq A) A (counit-shift-Coseq A)

htpy-map-limit-shift-Coseq :
  {l : Level} (A : Coseq-UU l) →
  map-limit-shift-Coseq' A ~ map-limit-shift-Coseq A
htpy-map-limit-shift-Coseq A = refl-htpy

map-inv-limit-shift-Coseq :
  {l : Level} (A : Coseq-UU l) →
  limit-Coseq A → limit-Coseq (shift-Coseq A)
map-inv-limit-shift-Coseq A =
  map-Σ
    ( λ x → (n : ℕ) → Id (map-Coseq A (succ-ℕ n) (x (succ-ℕ n))) (x n))
    ( λ x n → x (succ-ℕ n))
    ( λ x p n → p (succ-ℕ n))

issec-map-inv-limit-shift-Coseq :
  {l : Level} (A : Coseq-UU l) →
  ( ( map-limit-shift-Coseq A) ∘ ( map-inv-limit-shift-Coseq A)) ~ id
issec-map-inv-limit-shift-Coseq A x =
  eq-Eq-limit-Coseq A (pair (pr2 x) (λ n → refl))

isretr-map-inv-limit-shift-Coseq :
  {l : Level} (A : Coseq-UU l) →
  ( ( map-inv-limit-shift-Coseq A) ∘ (map-limit-shift-Coseq A)) ~ id
isretr-map-inv-limit-shift-Coseq A x =
  eq-Eq-limit-Coseq (shift-Coseq A) (pair (pr2 x) (λ n → refl))

is-limit-cone-limit-shift-Coseq :
  {l : Level} (A : Coseq-UU l) →
  is-limit-Coseq A (cone-limit-shift-Coseq A)
is-limit-cone-limit-shift-Coseq A =
  is-equiv-has-inverse
    ( map-inv-limit-shift-Coseq A)
    ( issec-map-inv-limit-shift-Coseq A)
    ( isretr-map-inv-limit-shift-Coseq A)

equiv-limit-shift-Coseq :
  {l : Level} (A : Coseq-UU l) → (limit-shift-Coseq A) ≃ (limit-Coseq A)
equiv-limit-shift-Coseq A =
  pair (map-limit-shift-Coseq A) (is-limit-cone-limit-shift-Coseq A)

--------------------------------------------------------------------------------

map-hom-shift-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (n : ℕ) → type-Coseq (shift-Coseq A) n → type-Coseq (shift-Coseq B) n
map-hom-shift-Coseq A B f n = map-hom-Coseq A B f (succ-ℕ n)

naturality-map-hom-shift-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  Naturality-hom-Coseq
    ( shift-Coseq A)
    ( shift-Coseq B)
    ( map-hom-shift-Coseq A B f)
naturality-map-hom-shift-Coseq A B f n =
  naturality-hom-Coseq A B f (succ-ℕ n)

hom-shift-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) →
  hom-Coseq A B → hom-Coseq (shift-Coseq A) (shift-Coseq B)
hom-shift-Coseq A B f =
  pair ( map-hom-shift-Coseq A B f)
       ( naturality-map-hom-shift-Coseq A B f)

--------------------------------------------------------------------------------

{- We prove the 2-out-of-6 property for equivalences -}

is-equiv-left-factor-2-out-of-6 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} →
  (f : A → B) (g : B → C) (h : C → D) {i : A → C} {j : B → D} →
  (G : i ~ (g ∘ f)) (H : (h ∘ g) ~ j) →
  is-equiv i → is-equiv j → is-equiv h
is-equiv-left-factor-2-out-of-6 f g h {i} {j} G H is-equiv-i is-equiv-j =
  is-equiv-has-inverse
    ( g ∘ j⁻¹)
    ( λ d →
      ( H (map-inv-is-equiv is-equiv-j d)) ∙
      ( issec-map-inv-is-equiv is-equiv-j d))
    ( λ c →
      ( ap
        ( (g ∘ j⁻¹) ∘ h)
        ( ( inv (issec-map-inv-is-equiv is-equiv-i c)) ∙
          ( G (i⁻¹ c)))) ∙
      ( ( ap
          ( g ∘ j⁻¹)
          ( H (f (i⁻¹ c)))) ∙
        ( ( ap g (isretr-map-inv-is-equiv is-equiv-j (f (i⁻¹ c)))) ∙
          ( ( inv (G (i⁻¹ c))) ∙
            ( issec-map-inv-is-equiv is-equiv-i c)))))
  where
  i⁻¹ = map-inv-is-equiv is-equiv-i
  j⁻¹ = map-inv-is-equiv is-equiv-j

is-equiv-middle-factor-2-out-of-6 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} →
  (f : A → B) (g : B → C) (h : C → D) {i : A → C} {j : B → D} →
  (G : i ~ (g ∘ f)) (H : (h ∘ g) ~ j) →
  is-equiv i → is-equiv j → is-equiv g
is-equiv-middle-factor-2-out-of-6 f g h {i} {j} G H is-equiv-i is-equiv-j =
  is-equiv-right-factor j h g
    ( inv-htpy H)
    ( is-equiv-left-factor-2-out-of-6 f g h G H is-equiv-i is-equiv-j)
    ( is-equiv-j)

is-equiv-right-factor-2-out-of-6 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} →
  (f : A → B) (g : B → C) (h : C → D) {i : A → C} {j : B → D} →
  (G : i ~ (g ∘ f)) (H : (h ∘ g) ~ j) →
  is-equiv i → is-equiv j → is-equiv f
is-equiv-right-factor-2-out-of-6 f g h {i} {j} G H is-equiv-i is-equiv-j =
  is-equiv-right-factor i g f G
    ( is-equiv-middle-factor-2-out-of-6 f g h G H is-equiv-i is-equiv-j)
    ( is-equiv-i)

--------------------------------------------------------------------------------

{- We show that any morphism of cosequences equipped with a diagonal filler
   induces an equivalence on limits. -}

map-hom-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) (n : ℕ) →
  type-Coseq B (succ-ℕ n) → type-Coseq A n
map-hom-has-filler-hom-Coseq = map-has-filler-hom-Coseq

naturality-map-hom-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) →
  Naturality-hom-Coseq (shift-Coseq B) A (map-hom-has-filler-hom-Coseq A B f J)
naturality-map-hom-has-filler-hom-Coseq A B f J n b =
  ( inv
    ( upper-triangle-has-filler-hom-Coseq A B f J n
      ( map-hom-has-filler-hom-Coseq A B f J (succ-ℕ n) b))) ∙
  ( inv
    ( ap (map-hom-has-filler-hom-Coseq A B f J n)
      ( lower-triangle-has-filler-hom-Coseq A B f J (succ-ℕ n) b)))

hom-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) → hom-Coseq (shift-Coseq B) A
hom-has-filler-hom-Coseq A B f J =
  pair ( map-hom-has-filler-hom-Coseq A B f J)
       ( naturality-map-hom-has-filler-hom-Coseq A B f J)

htpy-right-triangle-hom-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) (n : ℕ) →
  ( map-hom-Coseq A B f n ∘ map-hom-has-filler-hom-Coseq A B f J n) ~
  ( map-counit-shift-Coseq B n)
htpy-right-triangle-hom-has-filler-hom-Coseq A B f J n =
  inv-htpy (lower-triangle-has-filler-hom-Coseq A B f J n)

interchange-whisker-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f g : A → B}
  {h k : B → C} (G : f ~ g) (H : h ~ k) →
  ((H ·r f) ∙h (k ·l G)) ~ ((h ·l G) ∙h (H ·r g))
interchange-whisker-htpy G H a = htpy-nat H (G a)

naturality-right-triangle-hom-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) →
  Naturality-simple-htpy-hom-Coseq (shift-Coseq B) B
    ( comp-hom-Coseq (shift-Coseq B) A B f
      ( hom-has-filler-hom-Coseq A B f J))
    ( counit-shift-Coseq B)
    ( htpy-right-triangle-hom-has-filler-hom-Coseq A B f J)
naturality-right-triangle-hom-has-filler-hom-Coseq A B f J n b =
  ( right-unit ∙ ( ap-inv (pr2 B n) (K (succ-ℕ n) b))) ∙
  ( inv
    ( ( ap
        ( concat'
          ( map-Coseq B n (pr1 f (succ-ℕ n) (j (succ-ℕ n) b)))
          ( inv (K n (pr2 B (succ-ℕ n) b))))
        ( ( ap
            ( concat
              ( pr2 f n (j (succ-ℕ n) b))
              ( pr1 f n (j n (pr2 B (succ-ℕ n) b))))
            ( ap-concat
              ( pr1 f n)
              ( inv (H n (j (succ-ℕ n) b)))
              ( inv (ap (j n) (K (succ-ℕ n) b))))) ∙
          ( inv
            ( assoc
              ( pr2 f n (j (succ-ℕ n) b))
              ( ap (pr1 f n) (inv (H n (j (succ-ℕ n) b))))
              ( ap (pr1 f n) (inv (ap (j n) (K (succ-ℕ n) b)))))))) ∙
      ( ( assoc
          ( ( pr2 f n (j (succ-ℕ n) b)) ∙
            ( ap (pr1 f n) (inv (H n (j (succ-ℕ n) b)))))
          ( ap (pr1 f n) (inv (ap (j n) (K (succ-ℕ n) b))))
          ( inv (K n (pr2 B (succ-ℕ n) b)))) ∙
        ( ( ap
            ( concat
              ( ( pr2 f n (j (succ-ℕ n) b)) ∙
                ( ap (pr1 f n) (inv (H n (j (succ-ℕ n) b)))))
              ( map-Coseq B n (map-Coseq B (succ-ℕ n) b)))
            ( ( ap
                ( concat'
                  ( pr1 f n (j n (pr1 f (succ-ℕ n) (j (succ-ℕ n) b))))
                  ( inv (K n (pr2 B (succ-ℕ n) b))))
                ( ( ap-inv (pr1 f n) (ap (j n) (K (succ-ℕ n) b))) ∙
                  ( ap
                    ( inv)
                    ( inv (ap-comp (pr1 f n) (j n) (K (succ-ℕ n) b)))))) ∙
              ( ( inv
                  ( distributive-inv-concat
                    ( K n (pr2 B (succ-ℕ n) b))
                    ( ap ((pr1 f n) ∘ (j n)) (K (succ-ℕ n) b)))) ∙
                ( ( ap
                    ( inv)
                    ( interchange-whisker-htpy (K (succ-ℕ n)) (K n) b)) ∙
                  ( distributive-inv-concat
                    ( ap (pr2 B n) (K (succ-ℕ n) b))
                    ( K n (pr1 f (succ-ℕ n) (j (succ-ℕ n) b)))))))) ∙
          ( ( inv
              ( assoc
                ( ( pr2 f n (j (succ-ℕ n) b)) ∙
                  ( ap (pr1 f n) (inv (H n (j (succ-ℕ n) b)))))
                ( inv (K n (pr1 f (succ-ℕ n) (j (succ-ℕ n) b))))
                ( inv (ap (pr2 B n) (K (succ-ℕ n) b))))) ∙
            ( ap
              ( concat'
                ( pr2 B n (pr1 f (succ-ℕ n) (j (succ-ℕ n) b)))
                ( inv (ap (pr2 B n) (K (succ-ℕ n) b))))
              ( inv
                ( con-inv
                  ( refl)
                  ( K n (pr1 f (succ-ℕ n) (j (succ-ℕ n) b)))
                  ( ( pr2 f n (j (succ-ℕ n) b)) ∙ 
                    ( ap (pr1 f n) (inv (H n (j (succ-ℕ n) b)))))
                  ( ( con-inv
                      ( K n (pr1 f (succ-ℕ n) (j (succ-ℕ n) b)))
                      ( ap (pr1 f n) (H n (j (succ-ℕ n) b)))
                      ( pr2 f n (j (succ-ℕ n) b))
                      ( M n (j (succ-ℕ n) b))) ∙
                    ( ap
                      ( concat
                        ( pr2 f n (j (succ-ℕ n) b))
                        ( pr1 f n (j n (pr1 f (succ-ℕ n) (j (succ-ℕ n) b)))))
                      ( inv
                        ( ap-inv (pr1 f n) (H n (j (succ-ℕ n) b))))))))))))))
  where
  j = map-has-filler-hom-Coseq A B f J
  H = upper-triangle-has-filler-hom-Coseq A B f J
  K = lower-triangle-has-filler-hom-Coseq A B f J
  M = coherence-has-filler-hom-Coseq A B f J

right-triangle-hom-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) →
  simple-htpy-hom-Coseq (shift-Coseq B) B
    ( comp-hom-Coseq (shift-Coseq B) A B f (hom-has-filler-hom-Coseq A B f J))
    ( counit-shift-Coseq B)
right-triangle-hom-has-filler-hom-Coseq A B f J =
  pair ( htpy-right-triangle-hom-has-filler-hom-Coseq A B f J)
       ( naturality-right-triangle-hom-has-filler-hom-Coseq A B f J)

htpy-left-triangle-hom-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) (n : ℕ) → 
  ( map-counit-shift-Coseq A n) ~
  ( ( map-hom-has-filler-hom-Coseq A B f J n) ∘ (map-hom-shift-Coseq A B f n))  
htpy-left-triangle-hom-has-filler-hom-Coseq A B f J n =
  inv-htpy (upper-triangle-has-filler-hom-Coseq A B f J n)

naturality-left-triangle-hom-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) →
  Naturality-simple-htpy-hom-Coseq (shift-Coseq A) A
    ( counit-shift-Coseq A)
    ( comp-hom-Coseq (shift-Coseq A) (shift-Coseq B) A
      ( hom-has-filler-hom-Coseq A B f J)
      ( hom-shift-Coseq A B f))
    ( htpy-left-triangle-hom-has-filler-hom-Coseq A B f J)
naturality-left-triangle-hom-has-filler-hom-Coseq A B f J n a =
  ( ap
    ( concat
      ( ap (pr2 A n) (inv (H (succ-ℕ n) a)))
      ( j n (pr1 f (succ-ℕ n) (pr2 A (succ-ℕ n) a))))
    ( assoc
      ( inv (H n (j (succ-ℕ n) (pr1 f (succ-ℕ (succ-ℕ n)) a))))
      ( inv (ap (j n) (K (succ-ℕ n) (pr1 f (succ-ℕ (succ-ℕ n)) a))))
      ( ap (j n) (pr2 f (succ-ℕ n) a)))) ∙
  ( ( inv
      ( assoc
        ( ap (pr2 A n) (inv (H (succ-ℕ n) a)))
        ( inv (H n (j (succ-ℕ n) (pr1 f (succ-ℕ (succ-ℕ n)) a))))
        ( ( inv (ap (j n) (K (succ-ℕ n) (pr1 f (succ-ℕ (succ-ℕ n)) a)))) ∙
          ( ap (j n) (pr2 f (succ-ℕ n) a))))) ∙
    ( ( ap
        ( concat'
          ( pr2 A n (pr2 A (succ-ℕ n) a))
          ( ( inv (ap (j n) (K (succ-ℕ n) (pr1 f (succ-ℕ (succ-ℕ n)) a)))) ∙ 
            ( ap (j n) (pr2 f (succ-ℕ n) a))))
        ( inv
          ( interchange-whisker-htpy
            ( inv-htpy (H (succ-ℕ n)))
            ( inv-htpy (H n))
            ( a)))) ∙
      ( ( assoc
          ( inv (H n (pr2 A (succ-ℕ n) a)))
          ( ap ((j n) ∘ (pr1 f (succ-ℕ n))) (inv (H (succ-ℕ n) a)))
          ( ( inv (ap (j n) (K (succ-ℕ n) (pr1 f (succ-ℕ (succ-ℕ n)) a)))) ∙ 
            ( ap (j n) (pr2 f (succ-ℕ n) a)))) ∙
        ( ( ap
            ( concat
              ( inv (H n (pr2 A (succ-ℕ n) a)))
              ( j n (pr1 f (succ-ℕ n) (pr2 A (succ-ℕ n) a))))
            ( ( ap
                ( concat'
                  ( j n (pr1 f (succ-ℕ n) (pr2 A (succ-ℕ n) a)))
                  ( ( inv
                      ( ap
                        ( j n)
                        ( K (succ-ℕ n) (pr1 f (succ-ℕ (succ-ℕ n)) a)))) ∙ 
                    ( ap (j n) (pr2 f (succ-ℕ n) a))))
                ( ap-inv ((j n) ∘ (pr1 f (succ-ℕ n))) (H (succ-ℕ n) a))) ∙
              ( inv
                ( inv-con
                  ( ap ((j n) ∘ (pr1 f (succ-ℕ n))) (H (succ-ℕ n) a))
                  ( refl)
                  ( ( inv
                      ( ap
                        ( j n)
                        ( K (succ-ℕ n) (pr1 f (succ-ℕ (succ-ℕ n)) a)))) ∙ 
                    ( ap (j n) (pr2 f (succ-ℕ n) a)))
                  ( ( ( right-unit) ∙
                      ( ap-comp (j n) (pr1 f (succ-ℕ n)) (H (succ-ℕ n) a))) ∙
                    ( inv-con
                      ( ap (j n) (K (succ-ℕ n) (pr1 f (succ-ℕ (succ-ℕ n)) a)))
                      ( ap (j n) (ap (pr1 f (succ-ℕ n)) (H (succ-ℕ n) a)))
                      ( ap (j n) (pr2 f (succ-ℕ n) a))
                      ( ( inv
                          ( ap-concat
                            ( j n)
                            ( K (succ-ℕ n) (pr1 f (succ-ℕ (succ-ℕ n)) a))
                            ( ap (pr1 f (succ-ℕ n)) (H (succ-ℕ n) a)))) ∙
                        ( ap ( ap (j n)) ( M (succ-ℕ n) a))))))))) ∙
          ( right-unit))))) 
  where
  j = map-has-filler-hom-Coseq A B f J
  H = upper-triangle-has-filler-hom-Coseq A B f J
  K = lower-triangle-has-filler-hom-Coseq A B f J
  M = coherence-has-filler-hom-Coseq A B f J

left-triangle-hom-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  (J : has-filler-hom-Coseq A B f) →
  simple-htpy-hom-Coseq (shift-Coseq A) A
    ( counit-shift-Coseq A)
    ( comp-hom-Coseq (shift-Coseq A) (shift-Coseq B) A
      ( hom-has-filler-hom-Coseq A B f J)
      ( hom-shift-Coseq A B f))
left-triangle-hom-has-filler-hom-Coseq A B f J =
  pair ( htpy-left-triangle-hom-has-filler-hom-Coseq A B f J)
       ( naturality-left-triangle-hom-has-filler-hom-Coseq A B f J)

is-equiv-map-limit-has-filler-hom-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (f : hom-Coseq A B) →
  has-filler-hom-Coseq A B f → is-equiv (limit-hom-Coseq A B f)
is-equiv-map-limit-has-filler-hom-Coseq A B f J =
  is-equiv-left-factor-2-out-of-6
    ( limit-hom-Coseq (shift-Coseq A) (shift-Coseq B) (hom-shift-Coseq A B f))
    ( limit-hom-Coseq (shift-Coseq B) A (hom-has-filler-hom-Coseq A B f J))
    ( limit-hom-Coseq A B f)
    ( ( htpy-eq
        ( ap
          ( limit-hom-Coseq (shift-Coseq A) A)
          ( eq-simple-htpy-hom-Coseq (shift-Coseq A) A
            ( counit-shift-Coseq A)
            ( comp-hom-Coseq (shift-Coseq A) (shift-Coseq B) A
              ( hom-has-filler-hom-Coseq A B f J)
              ( hom-shift-Coseq A B f))
            ( left-triangle-hom-has-filler-hom-Coseq A B f J)))) ∙h
      ( comp-limit-hom-Coseq
        ( shift-Coseq A)
        ( shift-Coseq B)
        ( A)
        ( hom-has-filler-hom-Coseq A B f J)
        ( hom-shift-Coseq A B f)))
    ( ( inv-htpy
        ( comp-limit-hom-Coseq
          ( shift-Coseq B)
          ( A)
          ( B)
          ( f)
          ( hom-has-filler-hom-Coseq A B f J))) ∙h
      ( htpy-eq
        ( ap
          ( limit-hom-Coseq (shift-Coseq B) B)
          ( eq-simple-htpy-hom-Coseq (shift-Coseq B) B
            ( comp-hom-Coseq (shift-Coseq B) A B f
              ( hom-has-filler-hom-Coseq A B f J))
            ( counit-shift-Coseq B)
            ( right-triangle-hom-has-filler-hom-Coseq A B f J)))))
    ( is-limit-cone-limit-shift-Coseq A)
    ( is-limit-cone-limit-shift-Coseq B) 

--------------------------------------------------------------------------------

{- We show that exponents preserve sequential limits -}

exponent-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) (X : UU l2) → Coseq-UU (l1 ⊔ l2)
exponent-Coseq A X =
  pair
    ( λ n → X → type-Coseq A n)
    ( λ n h → (map-Coseq A n) ∘ h)

limit-Coseq-exponent-Coseq :
  { l1 l2 : Level} (A : Coseq-UU l1) (X : UU l2) → UU (l1 ⊔ l2)
limit-Coseq-exponent-Coseq A X =
  X → limit-Coseq A

cone-limit-Coseq-exponent-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (X : UU l2) →
  cone-Coseq
    ( exponent-Coseq A X)
    ( limit-Coseq-exponent-Coseq A X)
cone-limit-Coseq-exponent-Coseq A X =
  pair
    ( λ n h →
      ( map-cone-Coseq A (cone-limit-Coseq A) n) ∘ h)
    ( λ n h →
      eq-htpy
        ( (triangle-cone-Coseq A (cone-limit-Coseq A) n) ·r h))

cone-exponent-Coseq :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( Y : UU l3) → cone-Coseq (exponent-Coseq A Y) (Y → X)
cone-exponent-Coseq A c Y =
  pair
    ( λ n h → (map-cone-Coseq A c n) ∘ h)
    ( λ n h → eq-htpy ((triangle-cone-Coseq A c n) ·r h))

{-
universal-property-limit-cone-exponent-Coseq :
  { l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  ( up-X : {l : Level} → universal-property-limit-Coseq l A c) →
  ( Y : UU l3) {l : Level} →
  universal-property-limit-Coseq l
    ( exponent-Coseq A Y)
    ( cone-exponent-Coseq A c Y)
universal-property-limit-cone-exponent-Coseq A c up-X Y Z =
  {!!}
-}

--------------------------------------------------------------------------------

{- We show that coproducts preserve sequential limits -}

type-coprod-Coseq :
  {l1 l2 : Level} → Coseq-UU l1 → Coseq-UU l2 → ℕ → UU (l1 ⊔ l2)
type-coprod-Coseq A B n = coprod (type-Coseq A n) (type-Coseq B n)

map-coprod-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : Coseq-UU l2) (n : ℕ) →
  type-coprod-Coseq A B (succ-ℕ n) → type-coprod-Coseq A B n
map-coprod-Coseq A B n =
  map-coprod (map-Coseq A n) (map-Coseq B n)

coprod-Coseq :
  {l1 l2 : Level} → Coseq-UU l1 → Coseq-UU l2 → Coseq-UU (l1 ⊔ l2)
coprod-Coseq A B =
  pair (type-coprod-Coseq A B) (map-coprod-Coseq A B)

{- We introduce dependent morphisms for dependent cosequences -}

Map-hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C)
  (f : hom-Coseq A C) → UU (l1 ⊔ l2 ⊔ l4)
Map-hom-dependent-Coseq A B C D f =
  (n : ℕ) (a : type-Coseq A n) → type-dependent-Coseq A B n a →
  type-dependent-Coseq C D n (map-hom-Coseq A C f n a)

Naturality-hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C)
  (f : hom-Coseq A C) (g : Map-hom-dependent-Coseq A B C D f) →
  UU (l1 ⊔ l2 ⊔ l4)
Naturality-hom-dependent-Coseq A B C D f g =
  (n : ℕ) (a : type-Coseq A (succ-ℕ n))
  (b : type-dependent-Coseq A B (succ-ℕ n) a) →
  Id ( tr ( type-dependent-Coseq C D n)
          ( naturality-hom-Coseq A C f n a)
          ( map-dependent-Coseq C D n
            ( map-hom-Coseq A C f (succ-ℕ n) a)
            ( g (succ-ℕ n) a b)))
     ( g n (map-Coseq A n a) (map-dependent-Coseq A B n a b))

hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C)
  (f : hom-Coseq A C) → UU (l1 ⊔ l2 ⊔ l4)
hom-dependent-Coseq A B C D f =
  Σ ( Map-hom-dependent-Coseq A B C D f)
    ( Naturality-hom-dependent-Coseq A B C D f)

map-hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C) →
  hom-dependent-Coseq A B C D f → Map-hom-dependent-Coseq A B C D f
map-hom-dependent-Coseq A B C D f g = pr1 g

naturality-hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C) →
  (g : hom-dependent-Coseq A B C D f) →
  Naturality-hom-dependent-Coseq A B C D f (map-hom-dependent-Coseq A B C D f g)
naturality-hom-dependent-Coseq A B C D f g = pr2 g

{- We characterize the identity type of hom-dependent-Coseq -}

Htpy-htpy-hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C)
  (g h : hom-dependent-Coseq A B C D f) → UU (l1 ⊔ l2 ⊔ l4)
Htpy-htpy-hom-dependent-Coseq A B C D f g h =
  (n : ℕ) (a : type-Coseq A n) →
  map-hom-dependent-Coseq A B C D f g n a ~
  map-hom-dependent-Coseq A B C D f h n a

Naturality-htpy-hom-dependent-Coseq' :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C)
  (g h : hom-dependent-Coseq A B C D f)
  (H : Htpy-htpy-hom-dependent-Coseq A B C D f g h) (n : ℕ)
  (a : type-Coseq A (succ-ℕ n)) (b : type-dependent-Coseq A B (succ-ℕ n) a) →
  UU l4
Naturality-htpy-hom-dependent-Coseq' A B C D f g h H n a b =
  Id ( ( ap ( tr ( type-dependent-Coseq C D n)
                 ( naturality-hom-Coseq A C f n a))
            ( ap ( map-dependent-Coseq C D n (map-hom-Coseq A C f (succ-ℕ n) a))
                 ( H (succ-ℕ n) a b))) ∙
       ( naturality-hom-dependent-Coseq A B C D f h n a b))
     ( ( naturality-hom-dependent-Coseq A B C D f g n a b) ∙
       ( H n (map-Coseq A n a) (map-dependent-Coseq A B n a b)))

Naturality-htpy-hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C)
  (g h : hom-dependent-Coseq A B C D f)
  (H : Htpy-htpy-hom-dependent-Coseq A B C D f g h) → UU (l1 ⊔ l2 ⊔ l4)
Naturality-htpy-hom-dependent-Coseq A B C D f g h H =
  (n : ℕ) (a : type-Coseq A (succ-ℕ n))
  (b : type-dependent-Coseq A B (succ-ℕ n) a) →
  Naturality-htpy-hom-dependent-Coseq' A B C D f g h H n a b

htpy-hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C) →
  (g h : hom-dependent-Coseq A B C D f) → UU (l1 ⊔ l2 ⊔ l4)
htpy-hom-dependent-Coseq A B C D f g h =
  Σ ( Htpy-htpy-hom-dependent-Coseq A B C D f g h)
    ( Naturality-htpy-hom-dependent-Coseq A B C D f g h)

refl-htpy-hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C) →
  (g : hom-dependent-Coseq A B C D f) →
  htpy-hom-dependent-Coseq A B C D f g g
refl-htpy-hom-dependent-Coseq A B C D f g =
  pair (λ n a → refl-htpy) (λ n a b → inv right-unit)

htpy-hom-dependent-Coseq-eq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C) →
  (g h : hom-dependent-Coseq A B C D f) → Id g h →
  htpy-hom-dependent-Coseq A B C D f g h
htpy-hom-dependent-Coseq-eq A B C D f g .g refl =
  refl-htpy-hom-dependent-Coseq A B C D f g

is-contr-total-htpy-hom-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C)
  (g : hom-dependent-Coseq A B C D f) →
  is-contr
    ( Σ ( hom-dependent-Coseq A B C D f)
        ( htpy-hom-dependent-Coseq A B C D f g))
is-contr-total-htpy-hom-dependent-Coseq A B C D f g =
  is-contr-total-Eq-structure
    ( λ h H → Naturality-htpy-hom-dependent-Coseq A B C D f g (pair h H))
    ( is-contr-total-Eq-Π
      ( λ n h →
        ( a : type-Coseq A n) → map-hom-dependent-Coseq A B C D f g n a ~ h a)
      ( λ n →
        is-contr-total-Eq-Π
          ( λ a h → map-hom-dependent-Coseq A B C D f g n a ~ h)
          ( λ a →
            is-contr-total-htpy (map-hom-dependent-Coseq A B C D f g n a))))
    ( pair (map-hom-dependent-Coseq A B C D f g) (λ n a → refl-htpy))
    ( is-contr-total-Eq-Π
      ( λ n H →
        ( a : type-Coseq A (succ-ℕ n)) →
        ( b : type-dependent-Coseq A B (succ-ℕ n) a) →
        Id ( H a b)
           ( ( naturality-hom-dependent-Coseq A B C D f g n a b) ∙ refl))
      ( λ n →
        ( is-contr-total-Eq-Π
          ( λ a H →
            ( b : type-dependent-Coseq A B (succ-ℕ n) a) →
            Id ( H b)
               ( ( naturality-hom-dependent-Coseq A B C D f g n a b) ∙ refl))
          ( λ a →
            is-contr-total-htpy'
              ( λ b →
                ( naturality-hom-dependent-Coseq A B C D f g n a b) ∙ refl)))))

is-equiv-htpy-hom-dependent-Coseq-eq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (f : hom-Coseq A C)
  (g h : hom-dependent-Coseq A B C D f) →
  is-equiv (htpy-hom-dependent-Coseq-eq A B C D f g h)
is-equiv-htpy-hom-dependent-Coseq-eq A B C D f g =
  fundamental-theorem-id g
    ( refl-htpy-hom-dependent-Coseq A B C D f g)
    ( is-contr-total-htpy-hom-dependent-Coseq A B C D f g)
    ( htpy-hom-dependent-Coseq-eq A B C D f g)

{- We define composition of morphisms of dependent cosequences -}

comp-hom-dependent-Coseq :
  {l1 l2 l3 l4 l5 l6 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  (C : Coseq-UU l3) (D : dependent-Coseq-UU l4 C) (E : Coseq-UU l5)
  (F : dependent-Coseq-UU l6 E) (f : hom-Coseq A C)
  (g : hom-dependent-Coseq A B C D f) (h : hom-Coseq C E)
  (k : hom-dependent-Coseq C D E F h) →
  hom-dependent-Coseq A B E F (comp-hom-Coseq A C E h f)
comp-hom-dependent-Coseq A B C D E F f g h k =
  pair
    ( λ n x y →
      map-hom-dependent-Coseq C D E F h k n
        ( map-hom-Coseq A C f n x)
        ( map-hom-dependent-Coseq A B C D f g n x y))
    ( λ n x y →
      ( tr-concat
        ( pr2 h n (pr1 f (succ-ℕ n) x))
        ( ap (pr1 h n) (pr2 f n x))
        ( pr2 F n
          ( pr1 h (succ-ℕ n) (pr1 f (succ-ℕ n) x))
          ( pr1 k (succ-ℕ n) (pr1 f (succ-ℕ n) x) (pr1 g (succ-ℕ n) x y)))) ∙
      ( ( ap
          ( tr (pr1 F n) (ap (pr1 h n) (pr2 f n x)))
          ( pr2 k n (pr1 f (succ-ℕ n) x) (pr1 g (succ-ℕ n) x y))) ∙
        ( ( tr-ap
            ( pr1 h n)
            ( pr1 k n)
            ( pr2 f n x)
            ( pr2 D n (pr1 f (succ-ℕ n) x) (pr1 g (succ-ℕ n) x y))) ∙
          ( ap
            ( pr1 k n (pr1 f n (pr2 A n x)))
            ( pr2 g n x y)))))

{- We introduce dependent cones for dependent cosequences -}

constant-dependent-Coseq :
  {l1 l2 : Level} (X : UU l1) (Y : X → UU l2) →
  dependent-Coseq-UU l2 (constant-Coseq X)
constant-dependent-Coseq X Y =
  pair (λ n → Y) (λ n x → id)

cone-dependent-Coseq :
  {l1 l2 l3 l4 : Level} (A : Coseq-UU l1) (X : UU l2)
  (B : dependent-Coseq-UU l3 A) (Y : X → UU l4) →
  cone-Coseq A X → UU (l2 ⊔ l3 ⊔ l4)
cone-dependent-Coseq A X B Y c =
  hom-dependent-Coseq (constant-Coseq X) (constant-dependent-Coseq X Y) A B c

{- We introduce limiting cones of dependent cosequences -}

hom-constant-dependent-Coseq :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (g : (x : A) → B x → D (f x)) → 
  hom-dependent-Coseq
    ( constant-Coseq A)
    ( constant-dependent-Coseq A B)
    ( constant-Coseq C)
    ( constant-dependent-Coseq C D)
    ( hom-constant-Coseq f)
hom-constant-dependent-Coseq D f g =
  pair
    ( λ n → g)
    ( λ n x → refl-htpy)

cone-map-dependent-Coseq :
  {l1 l2 l3 l4 l5 l6 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A)
  {X : UU l3} (cX : cone-Coseq A X) {Y : X → UU l4}
  (cY : cone-dependent-Coseq A X B Y cX) {S : UU l5} {T : S → UU l6}
  (f : S → X) (g : (x : S) → T x → Y (f x)) →
  cone-dependent-Coseq A S B T (cone-map-Coseq A cX S f)
cone-map-dependent-Coseq A B {X} cX {Y} cY {S} {T} f g =
  comp-hom-dependent-Coseq
    ( constant-Coseq S)
    ( constant-dependent-Coseq S T)
    ( constant-Coseq X)
    ( constant-dependent-Coseq X Y)
    ( A)
    ( B)
    ( hom-constant-Coseq f)
    ( hom-constant-dependent-Coseq Y f g)
    ( cX)
    ( cY)

universal-property-limit-dependent-Coseq :
  (l l' : Level) {l1 l2 l3 l4 : Level} (A : Coseq-UU l1)
  (B : dependent-Coseq-UU l2 A) {X : UU l3} {Y : X → UU l4}
  (c : cone-Coseq A X) (d : cone-dependent-Coseq A X B Y c) →
  UU (lsuc l ⊔ lsuc l' ⊔ l2 ⊔ l3 ⊔ l4)
universal-property-limit-dependent-Coseq l l' A B {X} {Y} c d =
  (Z : UU l) (W : Z → UU l') (f : Z → X) →
  is-equiv (cone-map-dependent-Coseq A B c {Y} d {Z} {W} f)

{- We define the canonical limit of a dependent cosequence -}

type-limit-dependent-Coseq :
  {l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  (B : dependent-Coseq-UU l3 A) → X → UU l3
type-limit-dependent-Coseq A c B x =
  Σ ( (n : ℕ) → type-dependent-Coseq A B n (map-cone-Coseq A c n x))
    ( λ y →
      (n : ℕ) → Id ( tr
                     ( type-dependent-Coseq A B n)
                     ( triangle-cone-Coseq A c n x)
                     ( map-dependent-Coseq A B n
                       ( map-cone-Coseq A c (succ-ℕ n) x) (y (succ-ℕ n))))
                   ( y n))

type-limit-dependent-Coseq' :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A) →
  limit-Coseq A → UU l2
type-limit-dependent-Coseq' A =
  type-limit-dependent-Coseq A (cone-limit-Coseq A)

map-cone-limit-dependent-Coseq :
  {l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  (B : dependent-Coseq-UU l3 A) (n : ℕ) (x : X) →
  type-limit-dependent-Coseq A c B x →
  type-dependent-Coseq A B n (map-cone-Coseq A c n x)
map-cone-limit-dependent-Coseq A c B n x y = pr1 y n

triangle-cone-limit-dependent-Coseq :
  {l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  (B : dependent-Coseq-UU l3 A) (n : ℕ) (x : X) →
  (y : type-limit-dependent-Coseq A c B x) →
  Id ( tr
       ( type-dependent-Coseq A B n)
       ( triangle-cone-Coseq A c n x)
       ( map-dependent-Coseq A B n
         ( map-cone-Coseq A c (succ-ℕ n) x)
         ( map-cone-limit-dependent-Coseq A c B (succ-ℕ n) x y)))
     ( map-cone-limit-dependent-Coseq A c B n x y)
triangle-cone-limit-dependent-Coseq A c B n x y = pr2 y n

cone-limit-dependent-Coseq :
  {l1 l2 l3 : Level} (A : Coseq-UU l1) {X : UU l2} (c : cone-Coseq A X) →
  (B : dependent-Coseq-UU l3 A) →
  cone-dependent-Coseq A X B (type-limit-dependent-Coseq A c B) c
cone-limit-dependent-Coseq A c B =
  pair ( map-cone-limit-dependent-Coseq A c B)
       ( triangle-cone-limit-dependent-Coseq A c B)

{- The universal property of the canonical limit of a dependent cosequence -}

{- We introduce the total cosequence of a dependent cosequence -}

type-total-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A) →
  ℕ → UU (l1 ⊔ l2)
type-total-Coseq A B n =
  Σ (type-Coseq A n) (type-dependent-Coseq A B n)

map-total-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A) (n : ℕ) →
  type-total-Coseq A B (succ-ℕ n) → type-total-Coseq A B n
map-total-Coseq A B n =
  map-Σ
    ( type-dependent-Coseq A B n)
    ( map-Coseq A n)
    ( map-dependent-Coseq A B n)

total-Coseq :
  {l1 l2 : Level} (A : Coseq-UU l1) (B : dependent-Coseq-UU l2 A) →
  Coseq-UU (l1 ⊔ l2)
total-Coseq A B =
  pair (type-total-Coseq A B) (map-total-Coseq A B)

{- We show that Σ preserves sequential limits -}
