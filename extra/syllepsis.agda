{-# OPTIONS --without-K --exact-split #-}

module extra.syllepsis where

open import extra.interchange public

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

-- Triple loop spaces

x-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} → type-Ω³ a → type-Ω³ a → type-Ω³ a
x-concat-Ω³ = x-concat-Id³

ap-x-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} {α α' β β' : type-Ω³ a}
  (s : Id α α') (t : Id β β') → Id (x-concat-Ω³ α β) (x-concat-Ω³ α' β')
ap-x-concat-Ω³ s t = ap-binary x-concat-Ω³ s t

y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} → type-Ω³ a → type-Ω³ a → type-Ω³ a
y-concat-Ω³ = y-concat-Id³

ap-y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} {α α' β β' : type-Ω³ a}
  (s : Id α α') (t : Id β β') → Id (y-concat-Ω³ α β) (y-concat-Ω³ α' β')
ap-y-concat-Ω³ s t = ap-y-concat-Id³ s t

z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} → type-Ω³ a → type-Ω³ a → type-Ω³ a
z-concat-Ω³ = z-concat-Id³

ap-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} {α α' β β' : type-Ω³ a}
  (s : Id α α') (t : Id β β') → Id (z-concat-Ω³ α β) (z-concat-Ω³ α' β')
ap-z-concat-Ω³ s t = ap-z-concat-Id³ s t

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

coherence-interchange-Ω³ :
  {l : Level} {A : UU l} {a : A} (α β γ δ ε ζ η θ : type-Ω³ a) →
  Id ( ( interchange-y-z-concat-Ω³
         ( x-concat-Ω³ α β)
         ( x-concat-Ω³ γ δ)
         ( x-concat-Ω³ ε ζ)
         ( x-concat-Ω³ η θ)) ∙
       ( ( ap-y-concat-Ω³
           ( interchange-x-z-concat-Ω³ α β ε ζ)
           ( interchange-x-z-concat-Ω³ γ δ η θ)) ∙
         ( interchange-x-y-concat-Ω³
           ( z-concat-Ω³ α ε)
           ( z-concat-Ω³ β ζ)
           ( z-concat-Ω³ γ η)
           ( z-concat-Ω³ δ θ))))
     ( ( ap-z-concat-Ω³
         ( interchange-x-y-concat-Ω³ α β γ δ)
         ( interchange-x-y-concat-Ω³ ε ζ η θ)) ∙
       ( ( interchange-x-z-concat-Ω³
           ( y-concat-Ω³ α γ)
           ( y-concat-Ω³ β δ)
           ( y-concat-Ω³ ε η)
           ( y-concat-Ω³ ζ θ)) ∙
         ( ap-x-concat-Ω³
           ( interchange-y-z-concat-Ω³ α γ ε η)
           ( interchange-y-z-concat-Ω³ β δ ζ θ))))
coherence-interchange-Ω³ α β γ δ ε ζ η θ =
  ( assoc
    ( inv right-unit)
    ( interchange-y-z-concat-Id³
      ( x-concat-Id³ α β)
      ( x-concat-Id³ γ δ)
      ( x-concat-Id³ ε ζ)
      ( x-concat-Id³ η θ))
    ( ( ap-y-concat-Id³
        ( interchange-x-z-concat-Id³ α β ε ζ)
        ( interchange-x-z-concat-Id³ γ δ η θ)) ∙
      ( interchange-x-y-concat-Id³
        ( z-concat-Id³ α ε)
        ( z-concat-Id³ β ζ)
        ( z-concat-Id³ γ η)
        ( z-concat-Id³ δ θ)))) ∙
  ( ( ap
      ( concat
        ( inv right-unit)
        ( ( y-concat-Id³ (z-concat-Id³ α ε) (z-concat-Id³ γ η)) ∙
          ( y-concat-Id³ (z-concat-Id³ β ζ) (z-concat-Id³ δ θ)))) 
      ( ( inv
          ( ap
            ( concat
              ( interchange-y-z-concat-Id³
                ( x-concat-Id³ α β)
                ( x-concat-Id³ γ δ)
                ( x-concat-Id³ ε ζ)
                ( x-concat-Id³ η θ))
              ( ( y-concat-Id³ (z-concat-Id³ α ε) (z-concat-Id³ γ η)) ∙
                ( y-concat-Id³ (z-concat-Id³ β ζ) (z-concat-Id³ δ θ))))
            ( ap-id
              ( ( ap-binary horizontal-concat
                  ( interchange-x-z-concat-Id³ α β ε ζ)
                  ( interchange-x-z-concat-Id³ γ δ η θ)) ∙
                ( interchange-Id²
                  ( z-concat-Id³ α ε)
                  ( z-concat-Id³ β ζ)
                  ( z-concat-Id³ γ η)
                  ( z-concat-Id³ δ θ)))))) ∙
        ( coherence-interchange-Id³ α β γ δ ε ζ η θ))) ∙
    ( ( ap
        ( concat
          ( inv right-unit)
          ( x-concat-Id³
            ( y-concat-Id³ (z-concat-Id³ α ε) (z-concat-Id³ γ η))
            ( y-concat-Id³ (z-concat-Id³ β ζ) (z-concat-Id³ δ θ))))
        ( right-unit)) ∙
      ( ( inv
          ( assoc
            ( inv right-unit)
            ( ap
              ( concat' refl refl)
              ( ap-z-concat-Id³ 
                ( interchange-x-y-concat-Id³ α β γ δ)
                ( interchange-x-y-concat-Id³ ε ζ η θ)))
            ( ( ap 
                ( concat' refl refl)
                ( interchange-x-z-concat-Id³ 
                  ( y-concat-Id³ α γ) 
                  ( y-concat-Id³ β δ)
                  ( y-concat-Id³ ε η) 
                  ( y-concat-Id³ ζ θ))) ∙
              ( ( assoc 
                  ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η))
                  ( z-concat-Id³ (y-concat-Id³ β δ) (y-concat-Id³ ζ θ)) 
                  ( refl)) ∙
                ( ( ap
                    ( concat
                      ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η))
                      ( refl))
                    ( interchange-y-z-concat-Id³ β δ ζ θ)) ∙
                  ( ( inv
                      ( assoc 
                        ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η)) 
                        ( refl)
                        ( y-concat-Id³
                          ( z-concat-Id³ β ζ)
                          ( z-concat-Id³ δ θ)))) ∙
                    ( ap
                      ( concat'
                        ( refl)
                        ( y-concat-Id³ (z-concat-Id³ β ζ) (z-concat-Id³ δ θ)))
                      ( interchange-y-z-concat-Id³ α γ ε η))))))) ∙
          ( ap
            ( concat'
              ( z-concat-Id³
                ( y-concat-Id³ (x-concat-Id³ α β) (x-concat-Id³ γ δ))
                ( y-concat-Id³ (x-concat-Id³ ε ζ) (x-concat-Id³ η θ)))
              ( ( ap
                  ( concat'
                    ( refl)
                    ( refl))
                  ( interchange-x-z-concat-Id³
                    ( y-concat-Id³ α γ)
                    ( y-concat-Id³ β δ)
                    ( y-concat-Id³ ε η)
                    ( y-concat-Id³ ζ θ))) ∙
                ( ( assoc
                    ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η))
                    ( z-concat-Id³ (y-concat-Id³ β δ) (y-concat-Id³ ζ θ))
                    ( refl)) ∙
                  ( ( ap
                      ( concat
                        ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η))
                        ( refl))
                      ( interchange-y-z-concat-Id³ β δ ζ θ)) ∙
                    ( ( inv
                        ( assoc
                          ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η))
                          ( refl)
                          ( y-concat-Id³
                            ( z-concat-Id³ β ζ)
                            ( z-concat-Id³ δ θ)))) ∙
                      ( ap
                        ( concat'
                          ( refl)
                          ( y-concat-Id³
                            ( z-concat-Id³ β ζ)
                            ( z-concat-Id³ δ θ)))
                        ( interchange-y-z-concat-Id³ α γ ε η))))))))
          ( ( htpy-nat
              ( λ x → inv right-unit)
              ( ap-z-concat-Id³
                ( interchange-x-y-concat-Id³ α β γ δ)
                ( interchange-x-y-concat-Id³ ε ζ η θ))) ∙
            ( ap
              ( concat'
                ( z-concat-Id³
                  ( y-concat-Id³ (x-concat-Id³ α β) (x-concat-Id³ γ δ))
                  ( y-concat-Id³ (x-concat-Id³ ε ζ) (x-concat-Id³ η θ)))
                ( inv right-unit))
              ( ap-id
                ( ap-z-concat-Id³
                  ( interchange-x-y-concat-Id³ α β γ δ)
                  ( interchange-x-y-concat-Id³ ε ζ η θ)))))) ∙
        ( ( assoc
            ( ap-z-concat-Ω³
              ( interchange-x-y-concat-Ω³ α β γ δ)
              ( interchange-x-y-concat-Ω³ ε ζ η θ))
            ( inv right-unit)
            ( _)) ∙
          ( ap
            ( concat
              ( ap-z-concat-Ω³
                ( interchange-x-y-concat-Ω³ α β γ δ)
                ( interchange-x-y-concat-Ω³ ε ζ η θ))
              ( x-concat-Ω³
                ( y-concat-Ω³ (z-concat-Ω³ α ε) (z-concat-Ω³ γ η))
                ( y-concat-Ω³ (z-concat-Ω³ β ζ) (z-concat-Ω³ δ θ))))
            ( ( ( inv
                  ( assoc
                    ( inv right-unit)
                    ( ap
                      ( concat' refl refl)
                      ( interchange-x-z-concat-Id³
                        ( y-concat-Id³ α γ)
                        ( y-concat-Id³ β δ)
                        ( y-concat-Id³ ε η)
                        ( y-concat-Id³ ζ θ)))
                    ( ( ( assoc 
                          ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η))
                          ( z-concat-Id³ (y-concat-Id³ β δ) (y-concat-Id³ ζ θ)) 
                          ( refl)) ∙
                        ( ( ap
                            ( concat
                              ( z-concat-Id³
                                ( y-concat-Id³ α γ)
                                ( y-concat-Id³ ε η))
                              ( refl))
                            ( interchange-y-z-concat-Id³ β δ ζ θ)) ∙
                          ( ( inv
                              ( assoc 
                                ( z-concat-Id³
                                  ( y-concat-Id³ α γ)
                                  ( y-concat-Id³ ε η)) 
                                ( refl)
                                ( y-concat-Id³
                                  ( z-concat-Id³ β ζ)
                                  ( z-concat-Id³ δ θ)))) ∙
                            ( ap
                              ( concat'
                                ( refl)
                                ( y-concat-Id³
                                  ( z-concat-Id³ β ζ)
                                  ( z-concat-Id³ δ θ)))
                              ( interchange-y-z-concat-Id³ α γ ε η)))))))) ∙
                ( ap
                  ( concat'
                    ( z-concat-Ω³
                      ( x-concat-Ω³ (y-concat-Ω³ α γ) (y-concat-Ω³ β δ))
                      ( x-concat-Ω³ (y-concat-Ω³ ε η) (y-concat-Ω³ ζ θ)))
                    ( ( ( assoc 
                  ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η))
                  ( z-concat-Id³ (y-concat-Id³ β δ) (y-concat-Id³ ζ θ)) 
                  ( refl)) ∙
                ( ( ap
                    ( concat
                      ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η))
                      ( refl))
                    ( interchange-y-z-concat-Id³ β δ ζ θ)) ∙
                  ( ( inv
                      ( assoc 
                        ( z-concat-Id³ (y-concat-Id³ α γ) (y-concat-Id³ ε η)) 
                        ( refl)
                        ( y-concat-Id³
                          ( z-concat-Id³ β ζ)
                          ( z-concat-Id³ δ θ)))) ∙
                    ( ap
                      ( concat'
                        ( refl)
                        ( y-concat-Id³ (z-concat-Id³ β ζ) (z-concat-Id³ δ θ)))
                      ( interchange-y-z-concat-Id³ α γ ε η))))))))
                ( ( htpy-nat
                    ( λ x → inv right-unit)
                    ( interchange-x-z-concat-Ω³
                      ( y-concat-Ω³ α γ)
                      ( y-concat-Ω³ β δ)
                      ( y-concat-Ω³ ε η)
                      ( y-concat-Ω³ ζ θ))) ∙
                  ( ap
                    ( concat'
                      ( z-concat-Ω³
                        ( x-concat-Ω³ (y-concat-Ω³ α γ) (y-concat-Ω³ β δ))
                        ( x-concat-Ω³ (y-concat-Ω³ ε η) (y-concat-Ω³ ζ θ)))
                      ( inv right-unit))
                    ( ap-id
                      ( interchange-x-z-concat-Ω³
                        ( y-concat-Ω³ α γ)
                        ( y-concat-Ω³ β δ)
                        ( y-concat-Ω³ ε η)
                        ( y-concat-Ω³ ζ θ)))))) ∙
              ( ( assoc
                  ( interchange-x-z-concat-Ω³
                    ( y-concat-Ω³ α γ)
                    ( y-concat-Ω³ β δ)
                    ( y-concat-Ω³ ε η)
                    ( y-concat-Ω³ ζ θ))
                  ( inv right-unit)
                  ( _)) ∙
                ( ap
                  ( concat
                    ( interchange-x-z-concat-Ω³
                      ( y-concat-Ω³ α γ)
                      ( y-concat-Ω³ β δ)
                      ( y-concat-Ω³ ε η)
                      ( y-concat-Ω³ ζ θ))
                    ( x-concat-Ω³
                      ( y-concat-Ω³ (z-concat-Ω³ α ε) (z-concat-Ω³ γ η))
                      ( y-concat-Ω³ (z-concat-Ω³ β ζ) (z-concat-Ω³ δ θ))))
                  ( ( inv
                      ( assoc
                        ( inv right-unit)
                        ( assoc
                          ( z-concat-Ω³ (y-concat-Ω³ α γ) (y-concat-Ω³ ε η))
                          ( z-concat-Ω³ (y-concat-Ω³ β δ) (y-concat-Ω³ ζ θ))
                          ( refl))
                        ( _))) ∙
                    ( ( ap
                        ( concat'
                          ( x-concat-Ω³
                            ( z-concat-Ω³ (y-concat-Ω³ α γ) (y-concat-Ω³ ε η))
                            ( z-concat-Ω³ (y-concat-Ω³ β δ) (y-concat-Ω³ ζ θ)))
                          ( ( ap
                              ( concat
                                ( z-concat-Ω³
                                  ( y-concat-Ω³ α γ)
                                  ( y-concat-Ω³ ε η))
                                ( refl))
                              ( interchange-y-z-concat-Id³ β δ ζ θ)) ∙
                            ( ( inv
                                ( assoc
                                  ( z-concat-Ω³
                                    ( y-concat-Ω³ α γ)
                                    ( y-concat-Ω³ ε η))
                                  ( refl)
                                  ( y-concat-Ω³
                                    ( z-concat-Ω³ β ζ)
                                    ( z-concat-Ω³ δ θ)))) ∙
                              ( ap
                                ( concat'
                                  ( refl)
                                  ( y-concat-Ω³
                                    ( z-concat-Ω³ β ζ)
                                    ( z-concat-Ω³ δ θ)))
                                ( interchange-y-z-concat-Id³ α γ ε η)))))
                        ( unit-law-assoc-110'
                          ( z-concat-Ω³ (y-concat-Ω³ α γ) (y-concat-Ω³ ε η))
                          ( z-concat-Ω³ (y-concat-Ω³ β δ) (y-concat-Ω³ ζ θ)))) ∙
                      ( ( inv
                          ( assoc
                            ( ap
                              ( concat
                                ( z-concat-Ω³
                                  ( y-concat-Ω³ α γ)
                                  ( y-concat-Ω³ ε η))
                                ( refl))
                              ( inv right-unit))
                            ( ap
                              ( concat
                                ( z-concat-Ω³
                                  ( y-concat-Ω³ α γ)
                                  ( y-concat-Ω³ ε η))
                                ( refl))
                              ( interchange-y-z-concat-Id³ β δ ζ θ))
                            ( _))) ∙
                        ( ( ap
                            ( concat'
                              ( x-concat-Ω³
                                ( z-concat-Ω³
                                  ( y-concat-Ω³ α γ)
                                  ( y-concat-Ω³ ε η))
                                ( z-concat-Ω³
                                  ( y-concat-Ω³ β δ)
                                  ( y-concat-Ω³ ζ θ)))
                              ( ( inv
                                  ( assoc
                                    ( z-concat-Ω³
                                      ( y-concat-Ω³ α γ)
                                      ( y-concat-Ω³ ε η))
                                    ( refl)
                                    ( y-concat-Ω³
                                      ( z-concat-Ω³ β ζ)
                                      ( z-concat-Ω³ δ θ)))) ∙
                                ( ap
                                  ( concat'
                                    ( refl)
                                    ( y-concat-Ω³
                                      ( z-concat-Ω³ β ζ)
                                      ( z-concat-Ω³ δ θ)))
                                  ( interchange-y-z-concat-Id³ α γ ε η))))
                            ( inv
                              ( ap-concat
                                ( concat
                                  ( z-concat-Ω³
                                    ( y-concat-Ω³ α γ)
                                    ( y-concat-Ω³ ε η))
                                  ( refl))
                                ( inv right-unit)
                                ( interchange-y-z-concat-Id³ β δ ζ θ)))) ∙
                          ( ( ap
                              ( concat
                                ( ap
                                  ( concat
                                    ( z-concat-Ω³
                                      ( y-concat-Ω³ α γ)
                                      ( y-concat-Ω³ ε η))
                                    ( refl))
                                  ( interchange-y-z-concat-Ω³ β δ ζ θ))
                                ( x-concat-Ω³
                                  ( y-concat-Ω³
                                    ( z-concat-Ω³ α ε)
                                    ( z-concat-Ω³ γ η))
                                  ( y-concat-Ω³
                                    ( z-concat-Ω³ β ζ)
                                    ( z-concat-Ω³ δ θ))))
                              ( ( ap
                                  ( concat'
                                    ( x-concat-Ω³
                                      ( z-concat-Ω³
                                        ( y-concat-Ω³ α γ)
                                        ( y-concat-Ω³ ε η))
                                      ( y-concat-Ω³
                                        ( z-concat-Ω³ β ζ)
                                        ( z-concat-Ω³ δ θ)))
                                    ( ap
                                      ( concat'
                                        ( refl)
                                        ( y-concat-Ω³
                                          ( z-concat-Ω³ β ζ)
                                          ( z-concat-Ω³ δ θ)))
                                      ( interchange-y-z-concat-Id³ α γ ε η)))
                                  ( unit-law-assoc-101'
                                    ( z-concat-Ω³
                                      ( y-concat-Ω³ α γ)
                                      ( y-concat-Ω³ ε η))
                                    ( y-concat-Ω³
                                      ( z-concat-Id³ β ζ)
                                      ( z-concat-Id³ δ θ)))) ∙
                                ( inv
                                  ( ap-concat
                                    ( concat'
                                      ( refl)
                                      ( y-concat-Ω³
                                        ( z-concat-Ω³ β ζ)
                                        ( z-concat-Ω³ δ θ)))
                                    ( inv right-unit)
                                    ( interchange-y-z-concat-Id³ α γ ε η))))) ∙
                            ( inv
                              ( triangle-ap-binary'
                                ( x-concat-Ω³)
                                ( interchange-y-z-concat-Ω³ α γ ε η)
                                ( interchange-y-z-concat-Ω³ β δ ζ θ)
                              )))))))))))))))

-- syllepsis

{-
syllepsis :
  {l : Level} {A : UU l} {a : A} (s t : type-Ω³ a) →
  Id (eckmann-hilton-Ω² s t ∙ eckmann-hilton-Ω² t s) refl-Ω³
syllepsis s t = {!!}
-}
