# Type arithmetic for dependent pair types

```agda
module foundation.type-arithmetic-dependent-pair-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.singleton-inductionᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Weᵉ proveᵉ lawsᵉ forᵉ theᵉ manipulationᵉ ofᵉ dependentᵉ pairᵉ typesᵉ with respectᵉ to
themselvesᵉ andᵉ arithmeticalᵉ lawsᵉ with respectᵉ to contractibleᵉ types.ᵉ

## Properties

### The left unit law for Σ using a contractible base type

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Cᵉ : is-contrᵉ Aᵉ) (aᵉ : Aᵉ)
  where

  map-inv-left-unit-law-Σ-is-contrᵉ : Bᵉ aᵉ → Σᵉ Aᵉ Bᵉ
  pr1ᵉ (map-inv-left-unit-law-Σ-is-contrᵉ bᵉ) = aᵉ
  pr2ᵉ (map-inv-left-unit-law-Σ-is-contrᵉ bᵉ) = bᵉ

  map-left-unit-law-Σ-is-contrᵉ : Σᵉ Aᵉ Bᵉ → Bᵉ aᵉ
  map-left-unit-law-Σ-is-contrᵉ =
    ind-Σᵉ (ind-singletonᵉ aᵉ Cᵉ (λ xᵉ → Bᵉ xᵉ → Bᵉ aᵉ) (idᵉ))

  is-section-map-inv-left-unit-law-Σ-is-contrᵉ :
    map-left-unit-law-Σ-is-contrᵉ ∘ᵉ map-inv-left-unit-law-Σ-is-contrᵉ ~ᵉ idᵉ
  is-section-map-inv-left-unit-law-Σ-is-contrᵉ bᵉ =
    apᵉ
      ( λ (fᵉ : Bᵉ aᵉ → Bᵉ aᵉ) → fᵉ bᵉ)
      ( compute-ind-singletonᵉ aᵉ Cᵉ (λ xᵉ → Bᵉ xᵉ → Bᵉ aᵉ) idᵉ)

  is-retraction-map-inv-left-unit-law-Σ-is-contrᵉ :
    map-inv-left-unit-law-Σ-is-contrᵉ ∘ᵉ map-left-unit-law-Σ-is-contrᵉ ~ᵉ idᵉ
  is-retraction-map-inv-left-unit-law-Σ-is-contrᵉ =
    ind-Σᵉ
      ( ind-singletonᵉ aᵉ Cᵉ
        ( λ xᵉ →
          ( yᵉ : Bᵉ xᵉ) →
            Idᵉ
              ( ( map-inv-left-unit-law-Σ-is-contrᵉ ∘ᵉ
                  map-left-unit-law-Σ-is-contrᵉ)
                ( xᵉ ,ᵉ yᵉ))
              ( xᵉ ,ᵉ yᵉ))
        ( λ yᵉ → apᵉ
          ( map-inv-left-unit-law-Σ-is-contrᵉ)
          ( apᵉ
            ( λ fᵉ → fᵉ yᵉ)
            ( compute-ind-singletonᵉ aᵉ Cᵉ (λ xᵉ → Bᵉ xᵉ → Bᵉ aᵉ) idᵉ))))

  is-equiv-map-left-unit-law-Σ-is-contrᵉ :
    is-equivᵉ map-left-unit-law-Σ-is-contrᵉ
  is-equiv-map-left-unit-law-Σ-is-contrᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-left-unit-law-Σ-is-contrᵉ
      is-section-map-inv-left-unit-law-Σ-is-contrᵉ
      is-retraction-map-inv-left-unit-law-Σ-is-contrᵉ

  left-unit-law-Σ-is-contrᵉ : Σᵉ Aᵉ Bᵉ ≃ᵉ Bᵉ aᵉ
  pr1ᵉ left-unit-law-Σ-is-contrᵉ = map-left-unit-law-Σ-is-contrᵉ
  pr2ᵉ left-unit-law-Σ-is-contrᵉ = is-equiv-map-left-unit-law-Σ-is-contrᵉ

  abstract
    is-equiv-map-inv-left-unit-law-Σ-is-contrᵉ :
      is-equivᵉ map-inv-left-unit-law-Σ-is-contrᵉ
    is-equiv-map-inv-left-unit-law-Σ-is-contrᵉ =
      is-equiv-is-invertibleᵉ
        map-left-unit-law-Σ-is-contrᵉ
        is-retraction-map-inv-left-unit-law-Σ-is-contrᵉ
        is-section-map-inv-left-unit-law-Σ-is-contrᵉ

  inv-left-unit-law-Σ-is-contrᵉ : Bᵉ aᵉ ≃ᵉ Σᵉ Aᵉ Bᵉ
  pr1ᵉ inv-left-unit-law-Σ-is-contrᵉ = map-inv-left-unit-law-Σ-is-contrᵉ
  pr2ᵉ inv-left-unit-law-Σ-is-contrᵉ = is-equiv-map-inv-left-unit-law-Σ-is-contrᵉ
```

### Right unit law for dependent pair types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  abstract
    is-equiv-pr1-is-contrᵉ : ((aᵉ : Aᵉ) → is-contrᵉ (Bᵉ aᵉ)) → is-equivᵉ (pr1ᵉ {Bᵉ = Bᵉ})
    is-equiv-pr1-is-contrᵉ is-contr-Bᵉ =
      is-equiv-is-contr-mapᵉ
        ( λ xᵉ → is-contr-equivᵉ
          ( Bᵉ xᵉ)
          ( equiv-fiber-pr1ᵉ Bᵉ xᵉ)
          ( is-contr-Bᵉ xᵉ))

  equiv-pr1ᵉ : ((aᵉ : Aᵉ) → is-contrᵉ (Bᵉ aᵉ)) → (Σᵉ Aᵉ Bᵉ) ≃ᵉ Aᵉ
  pr1ᵉ (equiv-pr1ᵉ is-contr-Bᵉ) = pr1ᵉ
  pr2ᵉ (equiv-pr1ᵉ is-contr-Bᵉ) = is-equiv-pr1-is-contrᵉ is-contr-Bᵉ

  right-unit-law-Σ-is-contrᵉ : ((aᵉ : Aᵉ) → is-contrᵉ (Bᵉ aᵉ)) → (Σᵉ Aᵉ Bᵉ) ≃ᵉ Aᵉ
  right-unit-law-Σ-is-contrᵉ = equiv-pr1ᵉ

  abstract
    is-contr-is-equiv-pr1ᵉ : is-equivᵉ (pr1ᵉ {Bᵉ = Bᵉ}) → ((aᵉ : Aᵉ) → is-contrᵉ (Bᵉ aᵉ))
    is-contr-is-equiv-pr1ᵉ is-equiv-pr1-Bᵉ aᵉ =
      is-contr-equiv'ᵉ
        ( fiberᵉ pr1ᵉ aᵉ)
        ( equiv-fiber-pr1ᵉ Bᵉ aᵉ)
        ( is-contr-map-is-equivᵉ is-equiv-pr1-Bᵉ aᵉ)

  map-inv-right-unit-law-Σ-is-contrᵉ :
    ((aᵉ : Aᵉ) → is-contrᵉ (Bᵉ aᵉ)) → Aᵉ → Σᵉ Aᵉ Bᵉ
  map-inv-right-unit-law-Σ-is-contrᵉ Hᵉ aᵉ = (aᵉ ,ᵉ centerᵉ (Hᵉ aᵉ))

  is-section-map-inv-right-unit-law-Σ-is-contrᵉ :
    (Hᵉ : (aᵉ : Aᵉ) → is-contrᵉ (Bᵉ aᵉ)) →
    pr1ᵉ ∘ᵉ map-inv-right-unit-law-Σ-is-contrᵉ Hᵉ ~ᵉ idᵉ
  is-section-map-inv-right-unit-law-Σ-is-contrᵉ Hᵉ = refl-htpyᵉ

  is-retraction-map-inv-right-unit-law-Σ-is-contrᵉ :
    (Hᵉ : (aᵉ : Aᵉ) → is-contrᵉ (Bᵉ aᵉ)) →
    map-inv-right-unit-law-Σ-is-contrᵉ Hᵉ ∘ᵉ pr1ᵉ ~ᵉ idᵉ
  is-retraction-map-inv-right-unit-law-Σ-is-contrᵉ Hᵉ (aᵉ ,ᵉ bᵉ) =
    eq-pair-eq-fiberᵉ (eq-is-contrᵉ (Hᵉ aᵉ))

  is-equiv-map-inv-right-unit-law-Σ-is-contrᵉ :
    (Hᵉ : (aᵉ : Aᵉ) → is-contrᵉ (Bᵉ aᵉ)) →
    is-equivᵉ (map-inv-right-unit-law-Σ-is-contrᵉ Hᵉ)
  is-equiv-map-inv-right-unit-law-Σ-is-contrᵉ Hᵉ =
    is-equiv-is-invertibleᵉ
      ( pr1ᵉ)
      ( is-retraction-map-inv-right-unit-law-Σ-is-contrᵉ Hᵉ)
      ( is-section-map-inv-right-unit-law-Σ-is-contrᵉ Hᵉ)

  inv-right-unit-law-Σ-is-contrᵉ :
    (Hᵉ : (aᵉ : Aᵉ) → is-contrᵉ (Bᵉ aᵉ)) → Aᵉ ≃ᵉ Σᵉ Aᵉ Bᵉ
  pr1ᵉ (inv-right-unit-law-Σ-is-contrᵉ Hᵉ) = map-inv-right-unit-law-Σ-is-contrᵉ Hᵉ
  pr2ᵉ (inv-right-unit-law-Σ-is-contrᵉ Hᵉ) =
    is-equiv-map-inv-right-unit-law-Σ-is-contrᵉ Hᵉ
```

### Associativity of dependent pair types

Thereᵉ areᵉ twoᵉ waysᵉ to expressᵉ associativityᵉ forᵉ dependentᵉ pairᵉ types.ᵉ Weᵉ
formalizeᵉ bothᵉ ways.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : Σᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ)
  where

  map-associative-Σᵉ : Σᵉ (Σᵉ Aᵉ Bᵉ) Cᵉ → Σᵉ Aᵉ (λ xᵉ → Σᵉ (Bᵉ xᵉ) (λ yᵉ → Cᵉ (xᵉ ,ᵉ yᵉ)))
  pr1ᵉ (map-associative-Σᵉ ((xᵉ ,ᵉ yᵉ) ,ᵉ zᵉ)) = xᵉ
  pr1ᵉ (pr2ᵉ (map-associative-Σᵉ ((xᵉ ,ᵉ yᵉ) ,ᵉ zᵉ))) = yᵉ
  pr2ᵉ (pr2ᵉ (map-associative-Σᵉ ((xᵉ ,ᵉ yᵉ) ,ᵉ zᵉ))) = zᵉ

  map-inv-associative-Σᵉ : Σᵉ Aᵉ (λ xᵉ → Σᵉ (Bᵉ xᵉ) (λ yᵉ → Cᵉ (xᵉ ,ᵉ yᵉ))) → Σᵉ (Σᵉ Aᵉ Bᵉ) Cᵉ
  pr1ᵉ (pr1ᵉ (map-inv-associative-Σᵉ (xᵉ ,ᵉ yᵉ ,ᵉ zᵉ))) = xᵉ
  pr2ᵉ (pr1ᵉ (map-inv-associative-Σᵉ (xᵉ ,ᵉ yᵉ ,ᵉ zᵉ))) = yᵉ
  pr2ᵉ (map-inv-associative-Σᵉ (xᵉ ,ᵉ yᵉ ,ᵉ zᵉ)) = zᵉ

  is-retraction-map-inv-associative-Σᵉ :
    map-inv-associative-Σᵉ ∘ᵉ map-associative-Σᵉ ~ᵉ idᵉ
  is-retraction-map-inv-associative-Σᵉ ((xᵉ ,ᵉ yᵉ) ,ᵉ zᵉ) = reflᵉ

  is-section-map-inv-associative-Σᵉ :
    map-associative-Σᵉ ∘ᵉ map-inv-associative-Σᵉ ~ᵉ idᵉ
  is-section-map-inv-associative-Σᵉ (xᵉ ,ᵉ (yᵉ ,ᵉ zᵉ)) = reflᵉ

  abstract
    is-equiv-map-associative-Σᵉ : is-equivᵉ map-associative-Σᵉ
    is-equiv-map-associative-Σᵉ =
      is-equiv-is-invertibleᵉ
        map-inv-associative-Σᵉ
        is-section-map-inv-associative-Σᵉ
        is-retraction-map-inv-associative-Σᵉ

  associative-Σᵉ : Σᵉ (Σᵉ Aᵉ Bᵉ) Cᵉ ≃ᵉ Σᵉ Aᵉ (λ xᵉ → Σᵉ (Bᵉ xᵉ) (λ yᵉ → Cᵉ (xᵉ ,ᵉ yᵉ)))
  pr1ᵉ associative-Σᵉ = map-associative-Σᵉ
  pr2ᵉ associative-Σᵉ = is-equiv-map-associative-Σᵉ

  abstract
    is-equiv-map-inv-associative-Σᵉ : is-equivᵉ map-inv-associative-Σᵉ
    is-equiv-map-inv-associative-Σᵉ =
      is-equiv-is-invertibleᵉ
        map-associative-Σᵉ
        is-retraction-map-inv-associative-Σᵉ
        is-section-map-inv-associative-Σᵉ

  inv-associative-Σᵉ : Σᵉ Aᵉ (λ xᵉ → Σᵉ (Bᵉ xᵉ) (λ yᵉ → Cᵉ (xᵉ ,ᵉ yᵉ))) ≃ᵉ Σᵉ (Σᵉ Aᵉ Bᵉ) Cᵉ
  pr1ᵉ inv-associative-Σᵉ = map-inv-associative-Σᵉ
  pr2ᵉ inv-associative-Σᵉ = is-equiv-map-inv-associative-Σᵉ
```

### Associativity, second formulation

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ)
  where

  map-associative-Σ'ᵉ :
    Σᵉ (Σᵉ Aᵉ Bᵉ) (λ wᵉ → Cᵉ (pr1ᵉ wᵉ) (pr2ᵉ wᵉ)) → Σᵉ Aᵉ (λ xᵉ → Σᵉ (Bᵉ xᵉ) (Cᵉ xᵉ))
  pr1ᵉ (map-associative-Σ'ᵉ ((xᵉ ,ᵉ yᵉ) ,ᵉ zᵉ)) = xᵉ
  pr1ᵉ (pr2ᵉ (map-associative-Σ'ᵉ ((xᵉ ,ᵉ yᵉ) ,ᵉ zᵉ))) = yᵉ
  pr2ᵉ (pr2ᵉ (map-associative-Σ'ᵉ ((xᵉ ,ᵉ yᵉ) ,ᵉ zᵉ))) = zᵉ

  map-inv-associative-Σ'ᵉ :
    Σᵉ Aᵉ (λ xᵉ → Σᵉ (Bᵉ xᵉ) (Cᵉ xᵉ)) → Σᵉ (Σᵉ Aᵉ Bᵉ) (λ wᵉ → Cᵉ (pr1ᵉ wᵉ) (pr2ᵉ wᵉ))
  pr1ᵉ (pr1ᵉ (map-inv-associative-Σ'ᵉ (xᵉ ,ᵉ yᵉ ,ᵉ zᵉ))) = xᵉ
  pr2ᵉ (pr1ᵉ (map-inv-associative-Σ'ᵉ (xᵉ ,ᵉ yᵉ ,ᵉ zᵉ))) = yᵉ
  pr2ᵉ (map-inv-associative-Σ'ᵉ (xᵉ ,ᵉ yᵉ ,ᵉ zᵉ)) = zᵉ

  is-section-map-inv-associative-Σ'ᵉ :
    map-associative-Σ'ᵉ ∘ᵉ map-inv-associative-Σ'ᵉ ~ᵉ idᵉ
  is-section-map-inv-associative-Σ'ᵉ (xᵉ ,ᵉ (yᵉ ,ᵉ zᵉ)) = reflᵉ

  is-retraction-map-inv-associative-Σ'ᵉ :
    map-inv-associative-Σ'ᵉ ∘ᵉ map-associative-Σ'ᵉ ~ᵉ idᵉ
  is-retraction-map-inv-associative-Σ'ᵉ ((xᵉ ,ᵉ yᵉ) ,ᵉ zᵉ) = reflᵉ

  is-equiv-map-associative-Σ'ᵉ : is-equivᵉ map-associative-Σ'ᵉ
  is-equiv-map-associative-Σ'ᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-associative-Σ'ᵉ
      is-section-map-inv-associative-Σ'ᵉ
      is-retraction-map-inv-associative-Σ'ᵉ

  associative-Σ'ᵉ :
    Σᵉ (Σᵉ Aᵉ Bᵉ) (λ wᵉ → Cᵉ (pr1ᵉ wᵉ) (pr2ᵉ wᵉ)) ≃ᵉ Σᵉ Aᵉ (λ xᵉ → Σᵉ (Bᵉ xᵉ) (Cᵉ xᵉ))
  pr1ᵉ associative-Σ'ᵉ = map-associative-Σ'ᵉ
  pr2ᵉ associative-Σ'ᵉ = is-equiv-map-associative-Σ'ᵉ

  inv-associative-Σ'ᵉ :
    Σᵉ Aᵉ (λ xᵉ → Σᵉ (Bᵉ xᵉ) (Cᵉ xᵉ)) ≃ᵉ Σᵉ (Σᵉ Aᵉ Bᵉ) (λ wᵉ → Cᵉ (pr1ᵉ wᵉ) (pr2ᵉ wᵉ))
  pr1ᵉ inv-associative-Σ'ᵉ = map-inv-associative-Σ'ᵉ
  pr2ᵉ inv-associative-Σ'ᵉ =
    is-equiv-is-invertibleᵉ
      map-associative-Σ'ᵉ
      is-retraction-map-inv-associative-Σ'ᵉ
      is-section-map-inv-associative-Σ'ᵉ
```

### The interchange law

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  ( Dᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ → UUᵉ l4ᵉ)
  where

  map-interchange-Σ-Σᵉ :
    Σᵉ (Σᵉ Aᵉ Bᵉ) (λ tᵉ → Σᵉ (Cᵉ (pr1ᵉ tᵉ)) (Dᵉ (pr1ᵉ tᵉ) (pr2ᵉ tᵉ))) →
    Σᵉ (Σᵉ Aᵉ Cᵉ) (λ tᵉ → Σᵉ (Bᵉ (pr1ᵉ tᵉ)) (λ yᵉ → Dᵉ (pr1ᵉ tᵉ) yᵉ (pr2ᵉ tᵉ)))
  pr1ᵉ (pr1ᵉ (map-interchange-Σ-Σᵉ tᵉ)) = pr1ᵉ (pr1ᵉ tᵉ)
  pr2ᵉ (pr1ᵉ (map-interchange-Σ-Σᵉ tᵉ)) = pr1ᵉ (pr2ᵉ tᵉ)
  pr1ᵉ (pr2ᵉ (map-interchange-Σ-Σᵉ tᵉ)) = pr2ᵉ (pr1ᵉ tᵉ)
  pr2ᵉ (pr2ᵉ (map-interchange-Σ-Σᵉ tᵉ)) = pr2ᵉ (pr2ᵉ tᵉ)

  map-inv-interchange-Σ-Σᵉ :
    Σᵉ (Σᵉ Aᵉ Cᵉ) (λ tᵉ → Σᵉ (Bᵉ (pr1ᵉ tᵉ)) (λ yᵉ → Dᵉ (pr1ᵉ tᵉ) yᵉ (pr2ᵉ tᵉ))) →
    Σᵉ (Σᵉ Aᵉ Bᵉ) (λ tᵉ → Σᵉ (Cᵉ (pr1ᵉ tᵉ)) (Dᵉ (pr1ᵉ tᵉ) (pr2ᵉ tᵉ)))
  pr1ᵉ (pr1ᵉ (map-inv-interchange-Σ-Σᵉ tᵉ)) = pr1ᵉ (pr1ᵉ tᵉ)
  pr2ᵉ (pr1ᵉ (map-inv-interchange-Σ-Σᵉ tᵉ)) = pr1ᵉ (pr2ᵉ tᵉ)
  pr1ᵉ (pr2ᵉ (map-inv-interchange-Σ-Σᵉ tᵉ)) = pr2ᵉ (pr1ᵉ tᵉ)
  pr2ᵉ (pr2ᵉ (map-inv-interchange-Σ-Σᵉ tᵉ)) = pr2ᵉ (pr2ᵉ tᵉ)

  is-section-map-inv-interchange-Σ-Σᵉ :
    map-interchange-Σ-Σᵉ ∘ᵉ map-inv-interchange-Σ-Σᵉ ~ᵉ idᵉ
  is-section-map-inv-interchange-Σ-Σᵉ ((aᵉ ,ᵉ cᵉ) ,ᵉ (bᵉ ,ᵉ dᵉ)) = reflᵉ

  is-retraction-map-inv-interchange-Σ-Σᵉ :
    map-inv-interchange-Σ-Σᵉ ∘ᵉ map-interchange-Σ-Σᵉ ~ᵉ idᵉ
  is-retraction-map-inv-interchange-Σ-Σᵉ ((aᵉ ,ᵉ bᵉ) ,ᵉ (cᵉ ,ᵉ dᵉ)) = reflᵉ

  abstract
    is-equiv-map-interchange-Σ-Σᵉ : is-equivᵉ map-interchange-Σ-Σᵉ
    is-equiv-map-interchange-Σ-Σᵉ =
      is-equiv-is-invertibleᵉ
        map-inv-interchange-Σ-Σᵉ
        is-section-map-inv-interchange-Σ-Σᵉ
        is-retraction-map-inv-interchange-Σ-Σᵉ

  interchange-Σ-Σᵉ :
    Σᵉ (Σᵉ Aᵉ Bᵉ) (λ tᵉ → Σᵉ (Cᵉ (pr1ᵉ tᵉ)) (Dᵉ (pr1ᵉ tᵉ) (pr2ᵉ tᵉ))) ≃ᵉ
    Σᵉ (Σᵉ Aᵉ Cᵉ) (λ tᵉ → Σᵉ (Bᵉ (pr1ᵉ tᵉ)) (λ yᵉ → Dᵉ (pr1ᵉ tᵉ) yᵉ (pr2ᵉ tᵉ)))
  pr1ᵉ interchange-Σ-Σᵉ = map-interchange-Σ-Σᵉ
  pr2ᵉ interchange-Σ-Σᵉ = is-equiv-map-interchange-Σ-Σᵉ

  interchange-Σ-Σ-Σᵉ :
    Σᵉ Aᵉ (λ xᵉ → Σᵉ (Bᵉ xᵉ) (λ yᵉ → Σᵉ (Cᵉ xᵉ) (Dᵉ xᵉ yᵉ))) ≃ᵉ
    Σᵉ Aᵉ (λ xᵉ → Σᵉ (Cᵉ xᵉ) (λ zᵉ → Σᵉ (Bᵉ xᵉ) λ yᵉ → Dᵉ xᵉ yᵉ zᵉ))
  interchange-Σ-Σ-Σᵉ =
    associative-Σ'ᵉ Aᵉ Cᵉ (λ xᵉ zᵉ → Σᵉ (Bᵉ xᵉ) λ yᵉ → Dᵉ xᵉ yᵉ zᵉ) ∘eᵉ
    interchange-Σ-Σᵉ ∘eᵉ
    inv-associative-Σ'ᵉ Aᵉ Bᵉ (λ xᵉ yᵉ → Σᵉ (Cᵉ xᵉ) (Dᵉ xᵉ yᵉ))

  eq-interchange-Σ-Σ-is-contrᵉ :
    {aᵉ : Aᵉ} {bᵉ : Bᵉ aᵉ} → is-torsorialᵉ (Dᵉ aᵉ bᵉ) →
    {xᵉ yᵉ : Σᵉ (Cᵉ aᵉ) (Dᵉ aᵉ bᵉ)} →
    map-equivᵉ interchange-Σ-Σᵉ ((aᵉ ,ᵉ bᵉ) ,ᵉ xᵉ) ＝ᵉ
    map-equivᵉ interchange-Σ-Σᵉ ((aᵉ ,ᵉ bᵉ) ,ᵉ yᵉ)
  eq-interchange-Σ-Σ-is-contrᵉ Hᵉ =
    apᵉ (map-equivᵉ interchange-Σ-Σᵉ) (eq-pair-eq-fiberᵉ (eq-is-contrᵉ Hᵉ))
```

### Swapping the order of quantification in a Σ-type, on the left

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ → Bᵉ → UUᵉ l3ᵉ}
  where

  map-left-swap-Σᵉ : Σᵉ Aᵉ (λ xᵉ → Σᵉ Bᵉ (Cᵉ xᵉ)) → Σᵉ Bᵉ (λ yᵉ → Σᵉ Aᵉ (λ xᵉ → Cᵉ xᵉ yᵉ))
  pr1ᵉ (map-left-swap-Σᵉ (aᵉ ,ᵉ bᵉ ,ᵉ cᵉ)) = bᵉ
  pr1ᵉ (pr2ᵉ (map-left-swap-Σᵉ (aᵉ ,ᵉ bᵉ ,ᵉ cᵉ))) = aᵉ
  pr2ᵉ (pr2ᵉ (map-left-swap-Σᵉ (aᵉ ,ᵉ bᵉ ,ᵉ cᵉ))) = cᵉ

  map-inv-left-swap-Σᵉ :
    Σᵉ Bᵉ (λ yᵉ → Σᵉ Aᵉ (λ xᵉ → Cᵉ xᵉ yᵉ)) → Σᵉ Aᵉ (λ xᵉ → Σᵉ Bᵉ (Cᵉ xᵉ))
  pr1ᵉ (map-inv-left-swap-Σᵉ (bᵉ ,ᵉ aᵉ ,ᵉ cᵉ)) = aᵉ
  pr1ᵉ (pr2ᵉ (map-inv-left-swap-Σᵉ (bᵉ ,ᵉ aᵉ ,ᵉ cᵉ))) = bᵉ
  pr2ᵉ (pr2ᵉ (map-inv-left-swap-Σᵉ (bᵉ ,ᵉ aᵉ ,ᵉ cᵉ))) = cᵉ

  is-retraction-map-inv-left-swap-Σᵉ :
    map-inv-left-swap-Σᵉ ∘ᵉ map-left-swap-Σᵉ ~ᵉ idᵉ
  is-retraction-map-inv-left-swap-Σᵉ (aᵉ ,ᵉ (bᵉ ,ᵉ cᵉ)) = reflᵉ

  is-section-map-inv-left-swap-Σᵉ : map-left-swap-Σᵉ ∘ᵉ map-inv-left-swap-Σᵉ ~ᵉ idᵉ
  is-section-map-inv-left-swap-Σᵉ (bᵉ ,ᵉ (aᵉ ,ᵉ cᵉ)) = reflᵉ

  abstract
    is-equiv-map-left-swap-Σᵉ : is-equivᵉ map-left-swap-Σᵉ
    is-equiv-map-left-swap-Σᵉ =
      is-equiv-is-invertibleᵉ
        map-inv-left-swap-Σᵉ
        is-section-map-inv-left-swap-Σᵉ
        is-retraction-map-inv-left-swap-Σᵉ

  equiv-left-swap-Σᵉ : Σᵉ Aᵉ (λ aᵉ → Σᵉ Bᵉ (Cᵉ aᵉ)) ≃ᵉ Σᵉ Bᵉ (λ bᵉ → Σᵉ Aᵉ (λ aᵉ → Cᵉ aᵉ bᵉ))
  pr1ᵉ equiv-left-swap-Σᵉ = map-left-swap-Σᵉ
  pr2ᵉ equiv-left-swap-Σᵉ = is-equiv-map-left-swap-Σᵉ
```

### Swapping the order of quantification in a Σ-type, on the right

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  where

  map-right-swap-Σᵉ : Σᵉ (Σᵉ Aᵉ Bᵉ) (Cᵉ ∘ᵉ pr1ᵉ) → Σᵉ (Σᵉ Aᵉ Cᵉ) (Bᵉ ∘ᵉ pr1ᵉ)
  pr1ᵉ (pr1ᵉ (map-right-swap-Σᵉ ((aᵉ ,ᵉ bᵉ) ,ᵉ cᵉ))) = aᵉ
  pr2ᵉ (pr1ᵉ (map-right-swap-Σᵉ ((aᵉ ,ᵉ bᵉ) ,ᵉ cᵉ))) = cᵉ
  pr2ᵉ (map-right-swap-Σᵉ ((aᵉ ,ᵉ bᵉ) ,ᵉ cᵉ)) = bᵉ

  map-inv-right-swap-Σᵉ : Σᵉ (Σᵉ Aᵉ Cᵉ) (Bᵉ ∘ᵉ pr1ᵉ) → Σᵉ (Σᵉ Aᵉ Bᵉ) (Cᵉ ∘ᵉ pr1ᵉ)
  pr1ᵉ (pr1ᵉ (map-inv-right-swap-Σᵉ ((aᵉ ,ᵉ cᵉ) ,ᵉ bᵉ))) = aᵉ
  pr2ᵉ (pr1ᵉ (map-inv-right-swap-Σᵉ ((aᵉ ,ᵉ cᵉ) ,ᵉ bᵉ))) = bᵉ
  pr2ᵉ (map-inv-right-swap-Σᵉ ((aᵉ ,ᵉ cᵉ) ,ᵉ bᵉ)) = cᵉ

  is-section-map-inv-right-swap-Σᵉ :
    map-right-swap-Σᵉ ∘ᵉ map-inv-right-swap-Σᵉ ~ᵉ idᵉ
  is-section-map-inv-right-swap-Σᵉ ((xᵉ ,ᵉ yᵉ) ,ᵉ zᵉ) = reflᵉ

  is-retraction-map-inv-right-swap-Σᵉ :
    map-inv-right-swap-Σᵉ ∘ᵉ map-right-swap-Σᵉ ~ᵉ idᵉ
  is-retraction-map-inv-right-swap-Σᵉ ((xᵉ ,ᵉ zᵉ) ,ᵉ yᵉ) = reflᵉ

  is-equiv-map-right-swap-Σᵉ : is-equivᵉ map-right-swap-Σᵉ
  is-equiv-map-right-swap-Σᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-right-swap-Σᵉ
      is-section-map-inv-right-swap-Σᵉ
      is-retraction-map-inv-right-swap-Σᵉ

  equiv-right-swap-Σᵉ : Σᵉ (Σᵉ Aᵉ Bᵉ) (Cᵉ ∘ᵉ pr1ᵉ) ≃ᵉ Σᵉ (Σᵉ Aᵉ Cᵉ) (Bᵉ ∘ᵉ pr1ᵉ)
  pr1ᵉ equiv-right-swap-Σᵉ = map-right-swap-Σᵉ
  pr2ᵉ equiv-right-swap-Σᵉ = is-equiv-map-right-swap-Σᵉ
```

### Distributive laws of cartesian products over Σ

```agda
left-distributive-product-Σᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Bᵉ → UUᵉ l3ᵉ} →
  (Aᵉ ×ᵉ (Σᵉ Bᵉ Cᵉ)) ≃ᵉ Σᵉ Bᵉ (λ bᵉ → Aᵉ ×ᵉ (Cᵉ bᵉ))
left-distributive-product-Σᵉ =
  equiv-left-swap-Σᵉ

right-distributive-product-Σᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} →
  ((Σᵉ Aᵉ Bᵉ) ×ᵉ Cᵉ) ≃ᵉ Σᵉ Aᵉ (λ aᵉ → Bᵉ aᵉ ×ᵉ Cᵉ)
right-distributive-product-Σᵉ {Aᵉ} =
  associative-Σᵉ _ _ _
```

## See also

-ᵉ Functorialᵉ propertiesᵉ ofᵉ dependentᵉ pairᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-dependent-pair-types`](foundation.functoriality-dependent-pair-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in dependentᵉ pairᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).ᵉ
-ᵉ Theᵉ universalᵉ propertyᵉ ofᵉ dependentᵉ pairᵉ typesᵉ isᵉ treatedᵉ in
  [`foundation.universal-property-dependent-pair-types`](foundation.universal-property-dependent-pair-types.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ cartesianᵉ productᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-cartesian-product-types`](foundation.type-arithmetic-cartesian-product-types.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ dependentᵉ productᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ coproductᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-coproduct-types`](foundation.type-arithmetic-coproduct-types.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ theᵉ unitᵉ typeᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-unit-type`](foundation.type-arithmetic-unit-type.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ theᵉ emptyᵉ typeᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-empty-type`](foundation.type-arithmetic-empty-type.md).ᵉ