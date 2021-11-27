{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module extra.seven-trees-in-one where

open import book public

{-------------------------------------------------------------------------------

  We formalise a result of Andreas Blass, that there is an explicit equivalence
  from the type T of planar binary trees to the type T⁷ of septuples of planar
  binary trees.

  https://arxiv.org/abs/math/9405205

  The theorem makes crucial use of the fact that we can write

-------------------------------------------------------------------------------}

data binary-trees : UU lzero where
  root-binary-trees : binary-trees
  branch-binary-trees : (X Y : binary-trees) → binary-trees

is-root-binary-trees : binary-trees → UU lzero
is-root-binary-trees x = Id x root-binary-trees

is-not-root-binary-trees : binary-trees → UU lzero
is-not-root-binary-trees X = ¬ (is-root-binary-trees X)

pair-binary-trees-is-not-root-binary-trees :
  (X : binary-trees) → is-not-root-binary-trees X → binary-trees × binary-trees
pair-binary-trees-is-not-root-binary-trees root-binary-trees f =
  ex-falso (f refl)
pair-binary-trees-is-not-root-binary-trees (branch-binary-trees X1 X2) f =
  pair X1 X2

left-pair-binary-trees-is-not-root-binary-trees :
  (X : binary-trees) → is-not-root-binary-trees X → binary-trees
left-pair-binary-trees-is-not-root-binary-trees X f =
  pr1 (pair-binary-trees-is-not-root-binary-trees X f)

right-pair-binary-trees-is-not-root-binary-trees :
  (X : binary-trees) → is-not-root-binary-trees X → binary-trees
right-pair-binary-trees-is-not-root-binary-trees X f =
  pr2 (pair-binary-trees-is-not-root-binary-trees X f)

Eq-binary-trees : (X Y : binary-trees) → UU lzero
Eq-binary-trees root-binary-trees root-binary-trees =
  unit
Eq-binary-trees
  root-binary-trees (branch-binary-trees Y1 Y2) =
  empty
Eq-binary-trees
  (branch-binary-trees X1 X2) root-binary-trees =
  empty
Eq-binary-trees
  (branch-binary-trees X1 X2) (branch-binary-trees Y1 Y2) =
  Eq-binary-trees X1 Y1 × Eq-binary-trees X2 Y2

refl-Eq-binary-trees :
  (X : binary-trees) → Eq-binary-trees X X
refl-Eq-binary-trees root-binary-trees = star
refl-Eq-binary-trees (branch-binary-trees X1 X2) =
  pair (refl-Eq-binary-trees X1) (refl-Eq-binary-trees X2)

Eq-eq-binary-trees :
  {X Y : binary-trees} → Id X Y → Eq-binary-trees X Y
Eq-eq-binary-trees {X} refl = refl-Eq-binary-trees X

contraction-total-Eq-binary-trees :
  (X : binary-trees) →
  (u : Σ binary-trees (Eq-binary-trees X)) →
  Id (pair X (refl-Eq-binary-trees X)) u
contraction-total-Eq-binary-trees
  root-binary-trees (pair root-binary-trees star) = refl
contraction-total-Eq-binary-trees
  (branch-binary-trees X1 X2)
  (pair (branch-binary-trees Y1 Y2) (pair e1 e2)) =
    ap-binary f
      ( contraction-total-Eq-binary-trees X1 (pair Y1 e1))
      ( contraction-total-Eq-binary-trees X2 (pair Y2 e2))
  where
  f : (Z1 : Σ binary-trees (Eq-binary-trees X1)) →
      (Z2 : Σ binary-trees (Eq-binary-trees X2)) →
      Σ binary-trees
        ( Eq-binary-trees (branch-binary-trees X1 X2))
  f (pair Z1 d1) (pair Z2 d2) =
    pair (branch-binary-trees Z1 Z2) (pair d1 d2)

is-contr-total-Eq-binary-trees :
  (X : binary-trees) →
  is-contr (Σ binary-trees (Eq-binary-trees X))
is-contr-total-Eq-binary-trees X =
  pair ( pair X (refl-Eq-binary-trees X))
       ( contraction-total-Eq-binary-trees X)

is-equiv-Eq-eq-binary-trees :
  (X Y : binary-trees) → is-equiv (Eq-eq-binary-trees {X} {Y})
is-equiv-Eq-eq-binary-trees X =
  fundamental-theorem-id X
    ( refl-Eq-binary-trees X)
    ( is-contr-total-Eq-binary-trees X)
    ( λ Y → Eq-eq-binary-trees {X} {Y})

eq-Eq-binary-trees :
  {X Y : binary-trees} → Eq-binary-trees X Y → Id X Y
eq-Eq-binary-trees
  {root-binary-trees} {root-binary-trees} e = refl
eq-Eq-binary-trees
  {branch-binary-trees X1 X2} {branch-binary-trees Y1 Y2}
  (pair e1 e2) =
  ap-binary branch-binary-trees
    ( eq-Eq-binary-trees e1)
    ( eq-Eq-binary-trees e2)

is-prop-Eq-binary-trees :
  (X Y : binary-trees) → is-prop (Eq-binary-trees X Y)
is-prop-Eq-binary-trees
  root-binary-trees root-binary-trees = is-prop-unit
is-prop-Eq-binary-trees
  root-binary-trees (branch-binary-trees Y1 Y2) =
  is-prop-empty
is-prop-Eq-binary-trees
  (branch-binary-trees X1 X2) root-binary-trees =
  is-prop-empty
is-prop-Eq-binary-trees
  (branch-binary-trees X1 X2) (branch-binary-trees Y1 Y2) =
  is-prop-prod
    ( is-prop-Eq-binary-trees X1 Y1)
    ( is-prop-Eq-binary-trees X2 Y2)

is-set-binary-trees : is-set binary-trees
is-set-binary-trees X Y =
  is-prop-is-equiv
    ( is-equiv-Eq-eq-binary-trees X Y)
    ( is-prop-Eq-binary-trees X Y)

binary-trees-Set : UU-Set lzero
binary-trees-Set = pair binary-trees is-set-binary-trees

is-decidable-Eq-binary-trees :
  (X Y : binary-trees) → is-decidable (Eq-binary-trees X Y)
is-decidable-Eq-binary-trees root-binary-trees root-binary-trees =
  inl star
is-decidable-Eq-binary-trees root-binary-trees (branch-binary-trees Y1 Y2) =
  inr id
is-decidable-Eq-binary-trees (branch-binary-trees X1 X2) root-binary-trees =
  inr id
is-decidable-Eq-binary-trees
  (branch-binary-trees X1 X2) (branch-binary-trees Y1 Y2) =
  is-decidable-prod
    ( is-decidable-Eq-binary-trees X1 Y1)
    ( is-decidable-Eq-binary-trees X2 Y2)

has-decidable-equality-binary-trees :
  (X Y : binary-trees) → is-decidable (Id X Y)
has-decidable-equality-binary-trees X Y =
  is-decidable-iff eq-Eq-binary-trees Eq-eq-binary-trees
    ( is-decidable-Eq-binary-trees X Y)

is-decidable-is-root-binary-trees :
  (X : binary-trees) → is-decidable (is-root-binary-trees X)
is-decidable-is-root-binary-trees X =
  has-decidable-equality-binary-trees X root-binary-trees

is-decidable-is-not-root-binary-trees :
  (X : binary-trees) → is-decidable (is-not-root-binary-trees X)
is-decidable-is-not-root-binary-trees X =
  is-decidable-neg (is-decidable-is-root-binary-trees X)

seven-binary-trees : UU lzero
seven-binary-trees =
  binary-trees ×
    ( binary-trees ×
      ( binary-trees ×
        ( binary-trees ×
          ( binary-trees ×
            ( binary-trees × binary-trees)))))

seven-tuple :
  {l1 l2 l3 l4 l5 l6 l7 : Level} {X1 : UU l1} {X2 : UU l2} {X3 : UU l3 }
  {X4 : UU l4} {X5 : UU l5} {X6 : UU l6} {X7 : UU l7} →
  X1 → X2 → X3 → X4 → X5 → X6 → X7 → X1 × (X2 × (X3 × (X4 × (X5 × (X6 × X7)))))
seven-tuple x1 x2 x3 x4 x5 x6 x7 =
  pair x1 (pair x2 (pair x3 (pair x4 (pair x5 (pair x6 x7)))))

Eq-seven-binary-trees : (X Y : seven-binary-trees) → UU lzero
Eq-seven-binary-trees
  (pair X1 (pair X2 (pair X3 (pair X4 (pair X5 (pair X6 X7))))))
  (pair Y1 (pair Y2 (pair Y3 (pair Y4 (pair Y5 (pair Y6 Y7)))))) =
  Eq-binary-trees X1 Y1 ×
    ( Eq-binary-trees X2 Y2 ×
      ( Eq-binary-trees X3 Y3 ×
        ( Eq-binary-trees X4 Y4 ×
          ( Eq-binary-trees X5 Y5 ×
            ( Eq-binary-trees X6 Y6 × Eq-binary-trees X7 Y7)))))

refl-Eq-seven-binary-trees :
  (X : seven-binary-trees) → Eq-seven-binary-trees X X
refl-Eq-seven-binary-trees
  (pair X1 (pair X2 (pair X3 (pair X4 (pair X5 (pair X6 X7)))))) =
  seven-tuple
    ( refl-Eq-binary-trees X1)
    ( refl-Eq-binary-trees X2)
    ( refl-Eq-binary-trees X3)
    ( refl-Eq-binary-trees X4)
    ( refl-Eq-binary-trees X5)
    ( refl-Eq-binary-trees X6)
    ( refl-Eq-binary-trees X7)

map-seven-trees-in-one : seven-binary-trees → binary-trees
map-seven-trees-in-one
  (pair X1 (pair X2 (pair X3 (pair X4 (pair X5 (pair X6 X7)))))) with
  is-decidable-is-root-binary-trees X1
... | inr f1 =
  branch-binary-trees X1
    ( branch-binary-trees X2
      ( branch-binary-trees X3
        ( branch-binary-trees X4
          ( branch-binary-trees X5
            ( branch-binary-trees X6 X7)))))
... | inl p1 with is-decidable-is-root-binary-trees X2
... | inr f2 =
  branch-binary-trees X1
    ( branch-binary-trees X2
      ( branch-binary-trees X3
        ( branch-binary-trees X4
          ( branch-binary-trees X5
            ( branch-binary-trees X6 X7)))))
... | inl p2 with is-decidable-is-root-binary-trees X3
... | inr f3 =
  branch-binary-trees X1
    ( branch-binary-trees X2
      ( branch-binary-trees X3
        ( branch-binary-trees X4
          ( branch-binary-trees X5
            ( branch-binary-trees X6 X7)))))
... | inl p3 with is-decidable-is-root-binary-trees X4
... | inr f4 =
  branch-binary-trees X1
    ( branch-binary-trees X2
      ( branch-binary-trees X3
        ( branch-binary-trees X4
          ( branch-binary-trees X5
            ( branch-binary-trees X6 X7)))))
... | inl p4 with is-decidable-is-root-binary-trees X5
... | inr f5 =
  branch-binary-trees left-X5
    ( branch-binary-trees right-X5
      ( branch-binary-trees X6
        ( branch-binary-trees X7 root-binary-trees)))
  where
  left-X5 = left-pair-binary-trees-is-not-root-binary-trees X5 f5
  right-X5 = right-pair-binary-trees-is-not-root-binary-trees X5 f5
... | inl p5 with is-decidable-is-root-binary-trees X6
... | inr f6 =
  branch-binary-trees root-binary-trees
    ( branch-binary-trees root-binary-trees
      ( branch-binary-trees root-binary-trees
        ( branch-binary-trees root-binary-trees
          ( branch-binary-trees X7 X6))))
map-seven-trees-in-one
  (pair X1 (pair X2 (pair X3 (pair X4 (pair X5 (pair X6 root-binary-trees))))))
  | inl p1 | inl p2 | inl p3 | inl p4 | inl p5 | inl p6 = root-binary-trees
map-seven-trees-in-one
  ( pair X1
    ( pair X2
      ( pair X3
        ( pair X4
          ( pair X5 (pair X6 (branch-binary-trees X7 root-binary-trees)))))))
  | inl p1 | inl p2 | inl p3 | inl p4 | inl p5 | inl p6 =
  branch-binary-trees X7 root-binary-trees
map-seven-trees-in-one
  ( pair X1
    ( pair X2
      ( pair X3
        ( pair X4
          ( pair X5
            ( pair X6
              ( branch-binary-trees X7
                ( branch-binary-trees X8 root-binary-trees))))))))
  | inl p1 | inl p2 | inl p3 | inl p4 | inl p5 | inl p6 =
  branch-binary-trees X7 (branch-binary-trees X8 root-binary-trees)
map-seven-trees-in-one
  ( pair X1
    ( pair X2
      ( pair X3
        ( pair X4
          ( pair X5
            ( pair X6
              ( branch-binary-trees X7
                ( branch-binary-trees X8
                  ( branch-binary-trees X9 root-binary-trees)))))))))
  | inl p1 | inl p2 | inl p3 | inl p4 | inl p5 | inl p6 =
  branch-binary-trees X7
    ( branch-binary-trees X8
      ( branch-binary-trees X9 root-binary-trees))
map-seven-trees-in-one
  ( pair X1
    ( pair X2
      ( pair X3
        ( pair X4
          ( pair X5
            ( pair X6
              ( branch-binary-trees X7
                ( branch-binary-trees X8
                  ( branch-binary-trees X9
                    ( branch-binary-trees X10 root-binary-trees))))))))))
  | inl p1 | inl p2 | inl p3 | inl p4 | inl p5 | inl p6 =
  branch-binary-trees X7
    ( branch-binary-trees X8
      ( branch-binary-trees X9
        ( branch-binary-trees X10 root-binary-trees)))
map-seven-trees-in-one
  ( pair X1
    ( pair X2
      ( pair X3
        ( pair X4
          ( pair X5
            ( pair X6
              ( branch-binary-trees X7
                ( branch-binary-trees X8
                  ( branch-binary-trees X9
                    ( branch-binary-trees X10
                      ( branch-binary-trees X11 X12)))))))))))
  | inl p1 | inl p2 | inl p3 | inl p4 | inl p5 | inl p6 =
  branch-binary-trees X7
    ( branch-binary-trees X8
      ( branch-binary-trees X9
        ( branch-binary-trees X10
          ( branch-binary-trees X11
            ( branch-binary-trees X12 root-binary-trees)))))
