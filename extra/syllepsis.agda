{-# OPTIONS --without-K --exact-split #-}

module extra.syllepsis where

open import extra.interchange public

source-coherence-interchange-Id³ :
  {l : Level} {X : UU l} {x y z : X} {p q r : Id x y} {u v w : Id y z}
  {α β γ : Id p q} {δ ε ζ : Id q r} {η θ ι : Id u v} {κ μ ν : Id v w}
  (A : Id α β) (B : Id β γ) (C : Id δ ε) (D : Id ε ζ) (E : Id η θ) (F : Id θ ι)
  (G : Id κ μ) (H : Id μ ν) →
  Id ( ( ( z-concat-Id³
           ( y-concat-Id³ (x-concat-Id³ A B) (x-concat-Id³ C D))
           ( y-concat-Id³ (x-concat-Id³ E F) (x-concat-Id³ G H))) ∙
         ( interchange-Id² γ ζ ι ν)))
     ( ( interchange-Id² α δ η κ) ∙
       ( x-concat-Id³
         ( y-concat-Id³ (z-concat-Id³ A E) (z-concat-Id³ C G))
         ( y-concat-Id³ (z-concat-Id³ B F) (z-concat-Id³ D H))))
source-coherence-interchange-Id³ {l} {X} {x} {y} {z} {p} {q} {r} {u} {v} {w}
  {α} {β} {γ} {δ} {ε} {ζ} {η} {θ} {ι} {κ} {μ} {ν} A B C D E F G H =
  ( interchange-y-z-concat-Id³ (A ∙ B) (C ∙ D) (E ∙ F) (G ∙ H)) ∙
  ( ( ap ( concat
           ( interchange-Id² α δ η κ)
           ( horizontal-concat-Id² γ ι ∙ horizontal-concat-Id² ζ ν))
         ( ( z-concat-Id³
             ( interchange-x-z-concat-Id³ A B E F)
             ( interchange-x-z-concat-Id³ C D G H)) ∙
           ( interchange-x-y-concat-Id³
             ( z-concat-Id³ A E)
             ( z-concat-Id³ B F)
             ( z-concat-Id³ C G)
             ( z-concat-Id³ D H)))))

target-coherence-interchange-Id³ :
  {l : Level} {X : UU l} {x y z : X} {p q r : Id x y} {u v w : Id y z}
  {α β γ : Id p q} {δ ε ζ : Id q r} {η θ ι : Id u v} {κ μ ν : Id v w}
  (A : Id α β) (B : Id β γ) (C : Id δ ε) (D : Id ε ζ) (E : Id η θ) (F : Id θ ι)
  (G : Id κ μ) (H : Id μ ν) →
  Id ( ( ( z-concat-Id³
           ( y-concat-Id³ (x-concat-Id³ A B) (x-concat-Id³ C D))
           ( y-concat-Id³ (x-concat-Id³ E F) (x-concat-Id³ G H))) ∙
         ( interchange-Id² γ ζ ι ν)))
     ( ( interchange-Id² α δ η κ) ∙
       ( x-concat-Id³
         ( y-concat-Id³ (z-concat-Id³ A E) (z-concat-Id³ C G))
         ( y-concat-Id³ (z-concat-Id³ B F) (z-concat-Id³ D H))))
target-coherence-interchange-Id³ {l} {X} {x} {y} {z} {p} {q} {r} {u} {v} {w}
  {α} {β} {γ} {δ} {ε} {ζ} {η} {θ} {ι} {κ} {μ} {ν} A B C D E F G H =
  ( ( ap
      ( concat'
        ( horizontal-concat-Id² (α ∙ δ) (η ∙ κ))
        ( interchange-Id² γ ζ ι ν))
      ( k-concat-Id⁴
        ( interchange-x-y-concat-Id³ A B C D)
        ( interchange-x-y-concat-Id³ E F G H))) ∙
    ( ( ap
        ( concat'
          ( horizontal-concat-Id² (α ∙ δ) (η ∙ κ))
          ( interchange-Id² γ ζ ι ν))
        ( interchange-x-z-concat-Id³
          ( y-concat-Id³ A C)
          ( y-concat-Id³ B D)
          ( y-concat-Id³ E G)
          ( y-concat-Id³ F H))) ∙
      ( ( assoc
          ( z-concat-Id³ (y-concat-Id³ A C) (y-concat-Id³ E G))
          ( z-concat-Id³ (y-concat-Id³ B D) (y-concat-Id³ F H))
          ( interchange-Id² γ ζ ι ν)) ∙
        ( ( ap ( concat
                 ( z-concat-Id³ (y-concat-Id³ A C) (y-concat-Id³ E G))
                 ( horizontal-concat-Id² γ ι ∙ horizontal-concat-Id² ζ ν))
               ( interchange-y-z-concat-Id³ B D F H)) ∙
          ( ( inv
              ( assoc
                ( z-concat-Id³ (y-concat-Id³ A C) (y-concat-Id³ E G))
                ( interchange-Id² β ε θ μ)
                ( y-concat-Id³ (z-concat-Id³ B F) (z-concat-Id³ D H)))) ∙
            ( ap
              ( concat'
                ( horizontal-concat-Id² (α ∙ δ) (η ∙ κ))
                ( y-concat-Id³ (z-concat-Id³ B F) (z-concat-Id³ D H)))
              ( interchange-y-z-concat-Id³ A C E G))))))) ∙
  ( assoc
    ( interchange-Id² α δ η κ)
    ( y-concat-Id³ (z-concat-Id³ A E) (z-concat-Id³ C G))
    ( y-concat-Id³ (z-concat-Id³ B F) (z-concat-Id³ D H)))
  
coherence-interchange-Id³ :
  {l : Level} {X : UU l} {x y z : X} {p q r : Id x y} {u v w : Id y z}
  {α β γ : Id p q} {δ ε ζ : Id q r} {η θ ι : Id u v} {κ μ ν : Id v w}
  (A : Id α β) (B : Id β γ) (C : Id δ ε) (D : Id ε ζ) (E : Id η θ) (F : Id θ ι)
  (G : Id κ μ) (H : Id μ ν) →
  Id ( source-coherence-interchange-Id³ A B C D E F G H)
     ( target-coherence-interchange-Id³ A B C D E F G H)
coherence-interchange-Id³
  {l} {X} {x} {y} {z} {p} {.p} {.p} {u} {.u} {.u} {refl} {.refl} {.refl} {refl}
  {.refl} {.refl} {refl} {.refl} {.refl} {refl} {.refl} {.refl} refl refl refl
  refl refl refl refl refl = refl

--------------------------------------------------------------------------------

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
    ( ( j-concat-Id⁴
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
              ( ( ap-binary horizontal-concat-Id²
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
              ( k-concat-Id⁴ 
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
              ( k-concat-Id⁴
                ( interchange-x-y-concat-Id³ α β γ δ)
                ( interchange-x-y-concat-Id³ ε ζ η θ))) ∙
            ( ap
              ( concat'
                ( z-concat-Id³
                  ( y-concat-Id³ (x-concat-Id³ α β) (x-concat-Id³ γ δ))
                  ( y-concat-Id³ (x-concat-Id³ ε ζ) (x-concat-Id³ η θ)))
                ( inv right-unit))
              ( ap-id
                ( k-concat-Id⁴
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

syllepsis :
  {l : Level} {A : UU l} {a : A} (s t : type-Ω³ a) →
  Id (eckmann-hilton-Ω² s t ∙ eckmann-hilton-Ω² t s) refl
syllepsis s t = {!!}
