# Descent for coproduct types

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module foundation.descent-coproduct-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-fibers-of-mapsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import foundation-core.coproduct-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.families-of-equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.pullbacksᵉ
```

</details>

## Theorem

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l1'ᵉ l2'ᵉ l3'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {X'ᵉ : UUᵉ l3'ᵉ}
  (fᵉ : A'ᵉ → Aᵉ) (gᵉ : B'ᵉ → Bᵉ) (hᵉ : X'ᵉ → Xᵉ)
  (αAᵉ : Aᵉ → Xᵉ) (αBᵉ : Bᵉ → Xᵉ) (αA'ᵉ : A'ᵉ → X'ᵉ) (αB'ᵉ : B'ᵉ → X'ᵉ)
  (HAᵉ : αAᵉ ∘ᵉ fᵉ ~ᵉ hᵉ ∘ᵉ αA'ᵉ) (HBᵉ : αBᵉ ∘ᵉ gᵉ ~ᵉ hᵉ ∘ᵉ αB'ᵉ)
  where

  triangle-descent-square-fiber-map-coproduct-inl-fiberᵉ :
    (xᵉ : Aᵉ) →
    ( map-fiber-vertical-map-coneᵉ αAᵉ hᵉ (fᵉ ,ᵉ αA'ᵉ ,ᵉ HAᵉ) xᵉ) ~ᵉ
    ( map-fiber-vertical-map-coneᵉ (ind-coproductᵉ _ αAᵉ αBᵉ) hᵉ
      ( map-coproductᵉ fᵉ gᵉ ,ᵉ ind-coproductᵉ _ αA'ᵉ αB'ᵉ ,ᵉ ind-coproductᵉ _ HAᵉ HBᵉ)
      ( inlᵉ xᵉ)) ∘ᵉ
    ( fiber-map-coproduct-inl-fiberᵉ fᵉ gᵉ xᵉ)
  triangle-descent-square-fiber-map-coproduct-inl-fiberᵉ xᵉ (a'ᵉ ,ᵉ pᵉ) =
    eq-pair-eq-fiberᵉ
      ( left-whisker-concatᵉ
        ( invᵉ (HAᵉ a'ᵉ))
        ( ap-compᵉ (ind-coproductᵉ _ αAᵉ αBᵉ) inlᵉ pᵉ))

  triangle-descent-square-fiber-map-coproduct-inr-fiberᵉ :
    (yᵉ : Bᵉ) →
    ( map-fiber-vertical-map-coneᵉ αBᵉ hᵉ (gᵉ ,ᵉ αB'ᵉ ,ᵉ HBᵉ) yᵉ) ~ᵉ
    ( map-fiber-vertical-map-coneᵉ (ind-coproductᵉ _ αAᵉ αBᵉ) hᵉ
      ( map-coproductᵉ fᵉ gᵉ ,ᵉ ind-coproductᵉ _ αA'ᵉ αB'ᵉ ,ᵉ ind-coproductᵉ _ HAᵉ HBᵉ)
      ( inrᵉ yᵉ)) ∘ᵉ
    ( fiber-map-coproduct-inr-fiberᵉ fᵉ gᵉ yᵉ)
  triangle-descent-square-fiber-map-coproduct-inr-fiberᵉ yᵉ (b'ᵉ ,ᵉ pᵉ) =
    eq-pair-eq-fiberᵉ
      ( left-whisker-concatᵉ
        ( invᵉ (HBᵉ b'ᵉ))
        ( ap-compᵉ (ind-coproductᵉ _ αAᵉ αBᵉ) inrᵉ pᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l1'ᵉ l2'ᵉ l3'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {X'ᵉ : UUᵉ l3'ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (iᵉ : X'ᵉ → Xᵉ)
  where

  cone-descent-coproductᵉ :
    (cone-A'ᵉ : coneᵉ fᵉ iᵉ A'ᵉ) (cone-B'ᵉ : coneᵉ gᵉ iᵉ B'ᵉ) →
    coneᵉ (ind-coproductᵉ _ fᵉ gᵉ) iᵉ (A'ᵉ +ᵉ B'ᵉ)
  pr1ᵉ (cone-descent-coproductᵉ (hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) (kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ)) = map-coproductᵉ hᵉ kᵉ
  pr1ᵉ (pr2ᵉ (cone-descent-coproductᵉ (hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) (kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ))) (inlᵉ a'ᵉ) = f'ᵉ a'ᵉ
  pr1ᵉ (pr2ᵉ (cone-descent-coproductᵉ (hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) (kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ))) (inrᵉ b'ᵉ) = g'ᵉ b'ᵉ
  pr2ᵉ (pr2ᵉ (cone-descent-coproductᵉ (hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) (kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ))) (inlᵉ a'ᵉ) = Hᵉ a'ᵉ
  pr2ᵉ (pr2ᵉ (cone-descent-coproductᵉ (hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) (kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ))) (inrᵉ b'ᵉ) = Kᵉ b'ᵉ

  abstract
    descent-coproductᵉ :
      (cone-A'ᵉ : coneᵉ fᵉ iᵉ A'ᵉ) (cone-B'ᵉ : coneᵉ gᵉ iᵉ B'ᵉ) →
      is-pullbackᵉ fᵉ iᵉ cone-A'ᵉ →
      is-pullbackᵉ gᵉ iᵉ cone-B'ᵉ →
      is-pullbackᵉ
        ( ind-coproductᵉ _ fᵉ gᵉ)
        ( iᵉ)
        ( cone-descent-coproductᵉ cone-A'ᵉ cone-B'ᵉ)
    descent-coproductᵉ (hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) (kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ) is-pb-cone-A'ᵉ is-pb-cone-B'ᵉ =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-coneᵉ
        ( ind-coproductᵉ _ fᵉ gᵉ)
        ( iᵉ)
        ( cone-descent-coproductᵉ (hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) (kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ))
        ( αᵉ)
      where
      αᵉ :
        is-fiberwise-equivᵉ
          ( map-fiber-vertical-map-coneᵉ
            ( ind-coproductᵉ (λ _ → Xᵉ) fᵉ gᵉ)
            ( iᵉ)
            ( cone-descent-coproductᵉ (hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) (kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ)))
      αᵉ (inlᵉ xᵉ) =
        is-equiv-right-map-triangleᵉ
          ( map-fiber-vertical-map-coneᵉ fᵉ iᵉ (hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) xᵉ)
          ( map-fiber-vertical-map-coneᵉ (ind-coproductᵉ _ fᵉ gᵉ) iᵉ
            ( cone-descent-coproductᵉ (hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) (kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ))
            ( inlᵉ xᵉ))
          ( fiber-map-coproduct-inl-fiberᵉ hᵉ kᵉ xᵉ)
          ( triangle-descent-square-fiber-map-coproduct-inl-fiberᵉ
            hᵉ kᵉ iᵉ fᵉ gᵉ f'ᵉ g'ᵉ Hᵉ Kᵉ xᵉ)
          ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ fᵉ iᵉ
            ( hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) is-pb-cone-A'ᵉ xᵉ)
          ( is-equiv-fiber-map-coproduct-inl-fiberᵉ hᵉ kᵉ xᵉ)
      αᵉ (inrᵉ yᵉ) =
        is-equiv-right-map-triangleᵉ
          ( map-fiber-vertical-map-coneᵉ gᵉ iᵉ (kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ) yᵉ)
          ( map-fiber-vertical-map-coneᵉ
            ( ind-coproductᵉ _ fᵉ gᵉ) iᵉ
            ( cone-descent-coproductᵉ (hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) (kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ))
            ( inrᵉ yᵉ))
          ( fiber-map-coproduct-inr-fiberᵉ hᵉ kᵉ yᵉ)
          ( triangle-descent-square-fiber-map-coproduct-inr-fiberᵉ
            hᵉ kᵉ iᵉ fᵉ gᵉ f'ᵉ g'ᵉ Hᵉ Kᵉ yᵉ)
          ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ gᵉ iᵉ
            ( kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ) is-pb-cone-B'ᵉ yᵉ)
          ( is-equiv-fiber-map-coproduct-inr-fiberᵉ hᵉ kᵉ yᵉ)

  abstract
    descent-coproduct-inlᵉ :
      (cone-A'ᵉ : coneᵉ fᵉ iᵉ A'ᵉ) (cone-B'ᵉ : coneᵉ gᵉ iᵉ B'ᵉ) →
      is-pullbackᵉ
        ( ind-coproductᵉ _ fᵉ gᵉ)
        ( iᵉ)
        ( cone-descent-coproductᵉ cone-A'ᵉ cone-B'ᵉ) →
      is-pullbackᵉ fᵉ iᵉ cone-A'ᵉ
    descent-coproduct-inlᵉ (hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) (kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ) is-pb-dsqᵉ =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-coneᵉ fᵉ iᵉ
        ( hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ)
        ( λ aᵉ →
          is-equiv-left-map-triangleᵉ
          ( map-fiber-vertical-map-coneᵉ fᵉ iᵉ (hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) aᵉ)
          ( map-fiber-vertical-map-coneᵉ (ind-coproductᵉ _ fᵉ gᵉ) iᵉ
            ( cone-descent-coproductᵉ (hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) (kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ))
            ( inlᵉ aᵉ))
          ( fiber-map-coproduct-inl-fiberᵉ hᵉ kᵉ aᵉ)
          ( triangle-descent-square-fiber-map-coproduct-inl-fiberᵉ
            hᵉ kᵉ iᵉ fᵉ gᵉ f'ᵉ g'ᵉ Hᵉ Kᵉ aᵉ)
          ( is-equiv-fiber-map-coproduct-inl-fiberᵉ hᵉ kᵉ aᵉ)
          ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ
            ( ind-coproductᵉ _ fᵉ gᵉ)
            ( iᵉ)
            ( cone-descent-coproductᵉ ( hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) (kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ))
            ( is-pb-dsqᵉ)
            ( inlᵉ aᵉ)))

  abstract
    descent-coproduct-inrᵉ :
      (cone-A'ᵉ : coneᵉ fᵉ iᵉ A'ᵉ) (cone-B'ᵉ : coneᵉ gᵉ iᵉ B'ᵉ) →
      is-pullbackᵉ
        ( ind-coproductᵉ _ fᵉ gᵉ)
        ( iᵉ)
        ( cone-descent-coproductᵉ cone-A'ᵉ cone-B'ᵉ) →
      is-pullbackᵉ gᵉ iᵉ cone-B'ᵉ
    descent-coproduct-inrᵉ (hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) (kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ) is-pb-dsqᵉ =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-coneᵉ gᵉ iᵉ
        ( kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ)
        ( λ bᵉ →
          is-equiv-left-map-triangleᵉ
          ( map-fiber-vertical-map-coneᵉ gᵉ iᵉ (kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ) bᵉ)
          ( map-fiber-vertical-map-coneᵉ (ind-coproductᵉ _ fᵉ gᵉ) iᵉ
            ( cone-descent-coproductᵉ (hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) (kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ))
            ( inrᵉ bᵉ))
          ( fiber-map-coproduct-inr-fiberᵉ hᵉ kᵉ bᵉ)
          ( triangle-descent-square-fiber-map-coproduct-inr-fiberᵉ
            hᵉ kᵉ iᵉ fᵉ gᵉ f'ᵉ g'ᵉ Hᵉ Kᵉ bᵉ)
          ( is-equiv-fiber-map-coproduct-inr-fiberᵉ hᵉ kᵉ bᵉ)
          ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ
            ( ind-coproductᵉ _ fᵉ gᵉ)
            ( iᵉ)
            ( cone-descent-coproductᵉ (hᵉ ,ᵉ f'ᵉ ,ᵉ Hᵉ) (kᵉ ,ᵉ g'ᵉ ,ᵉ Kᵉ))
            ( is-pb-dsqᵉ)
            ( inrᵉ bᵉ)))
```