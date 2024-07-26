# Products of pullbacks

```agda
module foundation.products-pullbacksᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.pullbacksᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.universal-property-pullbacksᵉ
```

</details>

## Idea

Givenᵉ twoᵉ
[commutingᵉ squaresᵉ ofᵉ maps](foundation-core.commuting-squares-of-maps.md),ᵉ

```text
    Cᵉ ------>ᵉ Bᵉ                  C'ᵉ ----->ᵉ B'ᵉ
    |         |                  |         |
    |         |  gᵉ     andᵉ       |         | g'ᵉ
    ∨ᵉ         ∨ᵉ                  ∨ᵉ         ∨ᵉ
    Aᵉ ------>ᵉ Xᵉ                  A'ᵉ ----->ᵉ X'ᵉ
         fᵉ                            f'ᵉ
```

thenᵉ theirᵉ productᵉ

```text
  Cᵉ ×ᵉ C'ᵉ ---->ᵉ Bᵉ ×ᵉ B'ᵉ
    |            |
    |            | gᵉ ×ᵉ g'ᵉ
    ∨ᵉ            ∨ᵉ
  Aᵉ ×ᵉ A'ᵉ ---->ᵉ Xᵉ ×ᵉ X'ᵉ
         fᵉ ×ᵉ f'ᵉ
```

isᵉ aᵉ [pullback](foundation-core.pullbacks.mdᵉ) ifᵉ eachᵉ factorᵉ is.ᵉ Conversely,ᵉ ifᵉ
theᵉ productᵉ isᵉ aᵉ pullbackᵉ andᵉ theᵉ standardᵉ pullbackᵉ ofᵉ eachᵉ factorᵉ isᵉ inhabited,ᵉ
thenᵉ eachᵉ factorᵉ isᵉ alsoᵉ aᵉ pullback.ᵉ

## Definitions

### Product cones

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l4'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {X'ᵉ : UUᵉ l3'ᵉ} {C'ᵉ : UUᵉ l4'ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (f'ᵉ : A'ᵉ → X'ᵉ) (g'ᵉ : B'ᵉ → X'ᵉ)
  where

  product-coneᵉ :
    coneᵉ fᵉ gᵉ Cᵉ → coneᵉ f'ᵉ g'ᵉ C'ᵉ →
    coneᵉ (map-productᵉ fᵉ f'ᵉ) (map-productᵉ gᵉ g'ᵉ) (Cᵉ ×ᵉ C'ᵉ)
  pr1ᵉ (product-coneᵉ (pᵉ ,ᵉ qᵉ ,ᵉ Hᵉ) (p'ᵉ ,ᵉ q'ᵉ ,ᵉ H'ᵉ)) = map-productᵉ pᵉ p'ᵉ
  pr1ᵉ (pr2ᵉ (product-coneᵉ (pᵉ ,ᵉ qᵉ ,ᵉ Hᵉ) (p'ᵉ ,ᵉ q'ᵉ ,ᵉ H'ᵉ))) = map-productᵉ qᵉ q'ᵉ
  pr2ᵉ (pr2ᵉ (product-coneᵉ (pᵉ ,ᵉ qᵉ ,ᵉ Hᵉ) (p'ᵉ ,ᵉ q'ᵉ ,ᵉ H'ᵉ))) = htpy-map-productᵉ Hᵉ H'ᵉ
```

## Properties

### Computing the standard pullback of a product

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l1'ᵉ l2'ᵉ l3'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {X'ᵉ : UUᵉ l3'ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (f'ᵉ : A'ᵉ → X'ᵉ) (g'ᵉ : B'ᵉ → X'ᵉ)
  where

  map-product-cone-standard-pullbackᵉ :
    (standard-pullbackᵉ fᵉ gᵉ) ×ᵉ (standard-pullbackᵉ f'ᵉ g'ᵉ) →
    standard-pullbackᵉ (map-productᵉ fᵉ f'ᵉ) (map-productᵉ gᵉ g'ᵉ)
  map-product-cone-standard-pullbackᵉ =
    ( totᵉ
      ( λ tᵉ →
        ( totᵉ (λ sᵉ → eq-pair'ᵉ)) ∘ᵉ
        ( map-interchange-Σ-Σᵉ (λ yᵉ pᵉ y'ᵉ → f'ᵉ (pr2ᵉ tᵉ) ＝ᵉ g'ᵉ y'ᵉ)))) ∘ᵉ
    ( map-interchange-Σ-Σᵉ (λ xᵉ tᵉ x'ᵉ → Σᵉ B'ᵉ (λ y'ᵉ → f'ᵉ x'ᵉ ＝ᵉ g'ᵉ y'ᵉ)))

  abstract
    is-equiv-map-product-cone-standard-pullbackᵉ :
      is-equivᵉ map-product-cone-standard-pullbackᵉ
    is-equiv-map-product-cone-standard-pullbackᵉ =
      is-equiv-compᵉ
        ( totᵉ (λ tᵉ → totᵉ (λ sᵉ → eq-pair'ᵉ) ∘ᵉ map-interchange-Σ-Σᵉ _))
        ( map-interchange-Σ-Σᵉ _)
        ( is-equiv-map-interchange-Σ-Σᵉ _)
        ( is-equiv-tot-is-fiberwise-equivᵉ
          ( λ tᵉ →
            is-equiv-compᵉ
              ( totᵉ (λ sᵉ → eq-pair'ᵉ))
              ( map-interchange-Σ-Σᵉ (λ yᵉ pᵉ y'ᵉ → f'ᵉ (pr2ᵉ tᵉ) ＝ᵉ g'ᵉ y'ᵉ))
              ( is-equiv-map-interchange-Σ-Σᵉ _)
              ( is-equiv-tot-is-fiberwise-equivᵉ
                ( λ sᵉ →
                  is-equiv-eq-pairᵉ (map-productᵉ fᵉ f'ᵉ tᵉ) (map-productᵉ gᵉ g'ᵉ sᵉ)))))

  compute-product-standard-pullbackᵉ :
    (standard-pullbackᵉ fᵉ gᵉ) ×ᵉ (standard-pullbackᵉ f'ᵉ g'ᵉ) ≃ᵉ
    standard-pullbackᵉ (map-productᵉ fᵉ f'ᵉ) (map-productᵉ gᵉ g'ᵉ)
  compute-product-standard-pullbackᵉ =
    ( map-product-cone-standard-pullbackᵉ ,ᵉ
      is-equiv-map-product-cone-standard-pullbackᵉ)
```

### The gap map of the standard pullback of a product computes as a product of gap maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l4'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {X'ᵉ : UUᵉ l3'ᵉ} {C'ᵉ : UUᵉ l4'ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (f'ᵉ : A'ᵉ → X'ᵉ) (g'ᵉ : B'ᵉ → X'ᵉ)
  where

  triangle-map-product-cone-standard-pullbackᵉ :
    (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ f'ᵉ g'ᵉ C'ᵉ) →
    ( gapᵉ (map-productᵉ fᵉ f'ᵉ) (map-productᵉ gᵉ g'ᵉ) (product-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ)) ~ᵉ
    ( ( map-product-cone-standard-pullbackᵉ fᵉ gᵉ f'ᵉ g'ᵉ) ∘ᵉ
      ( map-productᵉ (gapᵉ fᵉ gᵉ cᵉ) (gapᵉ f'ᵉ g'ᵉ c'ᵉ)))
  triangle-map-product-cone-standard-pullbackᵉ cᵉ c'ᵉ = refl-htpyᵉ
```

### Products of pullbacks are pullbacks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l4'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {X'ᵉ : UUᵉ l3'ᵉ} {C'ᵉ : UUᵉ l4'ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (f'ᵉ : A'ᵉ → X'ᵉ) (g'ᵉ : B'ᵉ → X'ᵉ)
  where

  abstract
    is-pullback-product-is-pullbackᵉ :
      (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ f'ᵉ g'ᵉ C'ᵉ) →
      is-pullbackᵉ fᵉ gᵉ cᵉ →
      is-pullbackᵉ f'ᵉ g'ᵉ c'ᵉ →
      is-pullbackᵉ
        ( map-productᵉ fᵉ f'ᵉ)
        ( map-productᵉ gᵉ g'ᵉ)
        ( product-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ)
    is-pullback-product-is-pullbackᵉ cᵉ c'ᵉ is-pb-cᵉ is-pb-c'ᵉ =
      is-equiv-left-map-triangleᵉ
        ( gapᵉ
          ( map-productᵉ fᵉ f'ᵉ)
          ( map-productᵉ gᵉ g'ᵉ)
          ( product-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ))
        ( map-product-cone-standard-pullbackᵉ fᵉ gᵉ f'ᵉ g'ᵉ)
        ( map-productᵉ (gapᵉ fᵉ gᵉ cᵉ) (gapᵉ f'ᵉ g'ᵉ c'ᵉ))
        ( triangle-map-product-cone-standard-pullbackᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ)
        ( is-equiv-map-productᵉ (gapᵉ fᵉ gᵉ cᵉ) (gapᵉ f'ᵉ g'ᵉ c'ᵉ) is-pb-cᵉ is-pb-c'ᵉ)
        ( is-equiv-map-product-cone-standard-pullbackᵉ fᵉ gᵉ f'ᵉ g'ᵉ)
```

### Products of cones satisfying the universal property of pullbacks satisfy the universal property of pullbacks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l4'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {X'ᵉ : UUᵉ l3'ᵉ} {C'ᵉ : UUᵉ l4'ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ)
  (f'ᵉ : A'ᵉ → X'ᵉ) (g'ᵉ : B'ᵉ → X'ᵉ) (c'ᵉ : coneᵉ f'ᵉ g'ᵉ C'ᵉ)
  where

  universal-property-pullback-product-universal-property-pullbackᵉ :
    universal-property-pullbackᵉ fᵉ gᵉ cᵉ →
    universal-property-pullbackᵉ f'ᵉ g'ᵉ c'ᵉ →
    universal-property-pullbackᵉ
      ( map-productᵉ fᵉ f'ᵉ)
      ( map-productᵉ gᵉ g'ᵉ)
      ( product-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ)
  universal-property-pullback-product-universal-property-pullbackᵉ Hᵉ H'ᵉ =
    universal-property-pullback-is-pullbackᵉ
      ( map-productᵉ fᵉ f'ᵉ)
      ( map-productᵉ gᵉ g'ᵉ)
      ( product-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ)
      ( is-pullback-product-is-pullbackᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ
        ( is-pullback-universal-property-pullbackᵉ fᵉ gᵉ cᵉ Hᵉ)
        ( is-pullback-universal-property-pullbackᵉ f'ᵉ g'ᵉ c'ᵉ H'ᵉ))
```

### If the product is a pullback and the standard pullback of each factor is inhabited then both factors are pullbacks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l4'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {X'ᵉ : UUᵉ l3'ᵉ} {C'ᵉ : UUᵉ l4'ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (f'ᵉ : A'ᵉ → X'ᵉ) (g'ᵉ : B'ᵉ → X'ᵉ)
  (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ f'ᵉ g'ᵉ C'ᵉ)
  where

  abstract
    is-pullback-left-factor-is-inhabited-standard-pullback-right-factor-is-pullback-product'ᵉ :
      is-pullbackᵉ
        ( map-productᵉ fᵉ f'ᵉ)
        ( map-productᵉ gᵉ g'ᵉ)
        ( product-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ) →
      standard-pullbackᵉ f'ᵉ g'ᵉ →
      is-pullbackᵉ fᵉ gᵉ cᵉ
    is-pullback-left-factor-is-inhabited-standard-pullback-right-factor-is-pullback-product'ᵉ
      Hᵉ tᵉ =
      is-equiv-left-factor-is-equiv-map-product'ᵉ
        ( gapᵉ fᵉ gᵉ cᵉ)
        ( gapᵉ f'ᵉ g'ᵉ c'ᵉ)
        ( tᵉ)
        ( is-equiv-top-map-triangleᵉ
          ( gapᵉ
            ( map-productᵉ fᵉ f'ᵉ)
            ( map-productᵉ gᵉ g'ᵉ)
            ( product-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ))
          ( map-product-cone-standard-pullbackᵉ fᵉ gᵉ f'ᵉ g'ᵉ)
            ( map-productᵉ (gapᵉ fᵉ gᵉ cᵉ) (gapᵉ f'ᵉ g'ᵉ c'ᵉ))
            ( triangle-map-product-cone-standard-pullbackᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ)
            ( is-equiv-map-product-cone-standard-pullbackᵉ fᵉ gᵉ f'ᵉ g'ᵉ)
            ( Hᵉ))

  abstract
    is-pullback-left-factor-is-inhabited-standard-pullback-right-factor-is-pullback-productᵉ :
      is-pullbackᵉ
        ( map-productᵉ fᵉ f'ᵉ)
        ( map-productᵉ gᵉ g'ᵉ)
        ( product-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ) →
      is-inhabitedᵉ (standard-pullbackᵉ f'ᵉ g'ᵉ) →
      is-pullbackᵉ fᵉ gᵉ cᵉ
    is-pullback-left-factor-is-inhabited-standard-pullback-right-factor-is-pullback-productᵉ
      Hᵉ =
      rec-trunc-Propᵉ
        ( is-pullback-Propᵉ fᵉ gᵉ cᵉ)
        ( is-pullback-left-factor-is-inhabited-standard-pullback-right-factor-is-pullback-product'ᵉ
          ( Hᵉ))

  is-pullback-left-factor-is-inhabited-right-factor-is-pullback-product'ᵉ :
    is-pullbackᵉ
      ( map-productᵉ fᵉ f'ᵉ)
      ( map-productᵉ gᵉ g'ᵉ)
      ( product-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ) →
    C'ᵉ →
    is-pullbackᵉ fᵉ gᵉ cᵉ
  is-pullback-left-factor-is-inhabited-right-factor-is-pullback-product'ᵉ Hᵉ tᵉ =
    is-pullback-left-factor-is-inhabited-standard-pullback-right-factor-is-pullback-product'ᵉ
      ( Hᵉ)
      ( gapᵉ f'ᵉ g'ᵉ c'ᵉ tᵉ)

  is-pullback-left-factor-is-inhabited-right-factor-is-pullback-productᵉ :
    is-pullbackᵉ
      ( map-productᵉ fᵉ f'ᵉ)
      ( map-productᵉ gᵉ g'ᵉ)
      ( product-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ) →
    is-inhabitedᵉ C'ᵉ →
    is-pullbackᵉ fᵉ gᵉ cᵉ
  is-pullback-left-factor-is-inhabited-right-factor-is-pullback-productᵉ Hᵉ =
      rec-trunc-Propᵉ
        ( is-pullback-Propᵉ fᵉ gᵉ cᵉ)
        ( is-pullback-left-factor-is-inhabited-right-factor-is-pullback-product'ᵉ
          ( Hᵉ))

  abstract
    is-pullback-right-factor-is-inhabited-standard-pullback-left-factor-is-pullback-product'ᵉ :
      is-pullbackᵉ
        ( map-productᵉ fᵉ f'ᵉ)
        ( map-productᵉ gᵉ g'ᵉ)
        ( product-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ) →
      standard-pullbackᵉ fᵉ gᵉ →
      is-pullbackᵉ f'ᵉ g'ᵉ c'ᵉ
    is-pullback-right-factor-is-inhabited-standard-pullback-left-factor-is-pullback-product'ᵉ
      Hᵉ tᵉ =
      is-equiv-right-factor-is-equiv-map-product'ᵉ
        ( gapᵉ fᵉ gᵉ cᵉ)
        ( gapᵉ f'ᵉ g'ᵉ c'ᵉ)
        ( tᵉ)
        ( is-equiv-top-map-triangleᵉ
          ( gapᵉ
            ( map-productᵉ fᵉ f'ᵉ)
            ( map-productᵉ gᵉ g'ᵉ)
            ( product-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ))
          ( map-product-cone-standard-pullbackᵉ fᵉ gᵉ f'ᵉ g'ᵉ)
          ( map-productᵉ (gapᵉ fᵉ gᵉ cᵉ) (gapᵉ f'ᵉ g'ᵉ c'ᵉ))
          ( triangle-map-product-cone-standard-pullbackᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ)
          ( is-equiv-map-product-cone-standard-pullbackᵉ fᵉ gᵉ f'ᵉ g'ᵉ)
          ( Hᵉ))

  abstract
    is-pullback-right-factor-is-inhabited-standard-pullback-left-factor-is-pullback-productᵉ :
      is-pullbackᵉ
        ( map-productᵉ fᵉ f'ᵉ)
        ( map-productᵉ gᵉ g'ᵉ)
        ( product-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ) →
      is-inhabitedᵉ (standard-pullbackᵉ fᵉ gᵉ) →
      is-pullbackᵉ f'ᵉ g'ᵉ c'ᵉ
    is-pullback-right-factor-is-inhabited-standard-pullback-left-factor-is-pullback-productᵉ
      Hᵉ =
      rec-trunc-Propᵉ
        ( is-pullback-Propᵉ f'ᵉ g'ᵉ c'ᵉ)
        ( is-pullback-right-factor-is-inhabited-standard-pullback-left-factor-is-pullback-product'ᵉ
          ( Hᵉ))

  is-pullback-right-factor-is-inhabited-left-factor-is-pullback-product'ᵉ :
    is-pullbackᵉ
      ( map-productᵉ fᵉ f'ᵉ)
      ( map-productᵉ gᵉ g'ᵉ)
      ( product-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ) →
    Cᵉ →
    is-pullbackᵉ f'ᵉ g'ᵉ c'ᵉ
  is-pullback-right-factor-is-inhabited-left-factor-is-pullback-product'ᵉ Hᵉ tᵉ =
    is-pullback-right-factor-is-inhabited-standard-pullback-left-factor-is-pullback-product'ᵉ
      ( Hᵉ)
      ( gapᵉ fᵉ gᵉ cᵉ tᵉ)

  is-pullback-right-factor-is-inhabited-left-factor-is-pullback-productᵉ :
    is-pullbackᵉ
      ( map-productᵉ fᵉ f'ᵉ)
      ( map-productᵉ gᵉ g'ᵉ)
      ( product-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ) →
    is-inhabitedᵉ Cᵉ →
    is-pullbackᵉ f'ᵉ g'ᵉ c'ᵉ
  is-pullback-right-factor-is-inhabited-left-factor-is-pullback-productᵉ Hᵉ =
      rec-trunc-Propᵉ
        ( is-pullback-Propᵉ f'ᵉ g'ᵉ c'ᵉ)
        ( is-pullback-right-factor-is-inhabited-left-factor-is-pullback-product'ᵉ
          ( Hᵉ))
```

## Table of files about pullbacks

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ pullbacksᵉ asᵉ aᵉ generalᵉ concept.ᵉ

{{#includeᵉ tables/pullbacks.mdᵉ}}