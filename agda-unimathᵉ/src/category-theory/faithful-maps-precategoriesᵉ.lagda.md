# Faithful maps between precategories

```agda
module category-theory.faithful-maps-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.maps-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [map](category-theory.maps-precategories.mdᵉ) betweenᵉ
[precategories](category-theory.precategories.mdᵉ) `C`ᵉ andᵉ `D`ᵉ isᵉ **faithful**ᵉ ifᵉ
it'sᵉ anᵉ [embedding](foundation-core.embeddings.mdᵉ) onᵉ hom-sets.ᵉ

Noteᵉ thatᵉ embeddingsᵉ onᵉ [sets](foundation-core.sets.mdᵉ) happenᵉ to coincideᵉ with
[injections](foundation.injective-maps.md),ᵉ butᵉ weᵉ defineᵉ itᵉ in termsᵉ ofᵉ theᵉ
strongerᵉ notion,ᵉ asᵉ thisᵉ isᵉ theᵉ notionᵉ thatᵉ generalizes.ᵉ

## Definition

### The predicate on maps between precategories of being faithful

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-faithful-map-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-faithful-map-Precategoryᵉ =
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) → is-embᵉ (hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ {xᵉ} {yᵉ})

  is-prop-is-faithful-map-Precategoryᵉ : is-propᵉ is-faithful-map-Precategoryᵉ
  is-prop-is-faithful-map-Precategoryᵉ =
    is-prop-iterated-Πᵉ 2
      ( λ xᵉ yᵉ → is-property-is-embᵉ (hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ {xᵉ} {yᵉ}))

  is-faithful-prop-map-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ is-faithful-prop-map-Precategoryᵉ = is-faithful-map-Precategoryᵉ
  pr2ᵉ is-faithful-prop-map-Precategoryᵉ = is-prop-is-faithful-map-Precategoryᵉ
```

### The type of faithful maps between two precategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  faithful-map-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  faithful-map-Precategoryᵉ =
    Σᵉ (map-Precategoryᵉ Cᵉ Dᵉ) (is-faithful-map-Precategoryᵉ Cᵉ Dᵉ)

  map-faithful-map-Precategoryᵉ :
    faithful-map-Precategoryᵉ → map-Precategoryᵉ Cᵉ Dᵉ
  map-faithful-map-Precategoryᵉ = pr1ᵉ

  is-faithful-faithful-map-Precategoryᵉ :
    (Fᵉ : faithful-map-Precategoryᵉ) →
    is-faithful-map-Precategoryᵉ Cᵉ Dᵉ (map-faithful-map-Precategoryᵉ Fᵉ)
  is-faithful-faithful-map-Precategoryᵉ = pr2ᵉ

  obj-faithful-map-Precategoryᵉ :
    faithful-map-Precategoryᵉ → obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Dᵉ
  obj-faithful-map-Precategoryᵉ =
    obj-map-Precategoryᵉ Cᵉ Dᵉ ∘ᵉ map-faithful-map-Precategoryᵉ

  hom-faithful-map-Precategoryᵉ :
    (Fᵉ : faithful-map-Precategoryᵉ) {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Dᵉ
      ( obj-faithful-map-Precategoryᵉ Fᵉ xᵉ)
      ( obj-faithful-map-Precategoryᵉ Fᵉ yᵉ)
  hom-faithful-map-Precategoryᵉ =
    hom-map-Precategoryᵉ Cᵉ Dᵉ ∘ᵉ map-faithful-map-Precategoryᵉ
```

### The predicate on maps between precategories of being injective on hom-sets

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-injective-hom-map-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-injective-hom-map-Precategoryᵉ =
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) → is-injectiveᵉ (hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ {xᵉ} {yᵉ})

  is-prop-is-injective-hom-map-Precategoryᵉ :
    is-propᵉ is-injective-hom-map-Precategoryᵉ
  is-prop-is-injective-hom-map-Precategoryᵉ =
    is-prop-iterated-Πᵉ 2
      ( λ xᵉ yᵉ →
        is-prop-is-injectiveᵉ
          ( is-set-hom-Precategoryᵉ Cᵉ xᵉ yᵉ)
          ( hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ {xᵉ} {yᵉ}))

  is-injective-hom-prop-map-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ is-injective-hom-prop-map-Precategoryᵉ =
    is-injective-hom-map-Precategoryᵉ
  pr2ᵉ is-injective-hom-prop-map-Precategoryᵉ =
    is-prop-is-injective-hom-map-Precategoryᵉ
```

## Properties

### A map of precategories is faithful if and only if it is injective on hom-sets

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-injective-hom-is-faithful-map-Precategoryᵉ :
    is-faithful-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ →
    is-injective-hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  is-injective-hom-is-faithful-map-Precategoryᵉ is-faithful-Fᵉ xᵉ yᵉ =
    is-injective-is-embᵉ (is-faithful-Fᵉ xᵉ yᵉ)

  is-faithful-is-injective-hom-map-Precategoryᵉ :
    is-injective-hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ →
    is-faithful-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  is-faithful-is-injective-hom-map-Precategoryᵉ is-injective-hom-Fᵉ xᵉ yᵉ =
    is-emb-is-injectiveᵉ
      ( is-set-hom-Precategoryᵉ Dᵉ
        ( obj-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
        ( obj-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ))
      ( is-injective-hom-Fᵉ xᵉ yᵉ)

  is-equiv-is-injective-hom-is-faithful-map-Precategoryᵉ :
    is-equivᵉ is-injective-hom-is-faithful-map-Precategoryᵉ
  is-equiv-is-injective-hom-is-faithful-map-Precategoryᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-is-faithful-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( is-prop-is-injective-hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( is-faithful-is-injective-hom-map-Precategoryᵉ)

  is-equiv-is-faithful-is-injective-hom-map-Precategoryᵉ :
    is-equivᵉ is-faithful-is-injective-hom-map-Precategoryᵉ
  is-equiv-is-faithful-is-injective-hom-map-Precategoryᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-is-injective-hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( is-prop-is-faithful-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( is-injective-hom-is-faithful-map-Precategoryᵉ)

  equiv-is-injective-hom-is-faithful-map-Precategoryᵉ :
    is-faithful-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ ≃ᵉ
    is-injective-hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  pr1ᵉ equiv-is-injective-hom-is-faithful-map-Precategoryᵉ =
    is-injective-hom-is-faithful-map-Precategoryᵉ
  pr2ᵉ equiv-is-injective-hom-is-faithful-map-Precategoryᵉ =
    is-equiv-is-injective-hom-is-faithful-map-Precategoryᵉ

  equiv-is-faithful-is-injective-hom-map-Precategoryᵉ :
    is-injective-hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ ≃ᵉ
    is-faithful-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  pr1ᵉ equiv-is-faithful-is-injective-hom-map-Precategoryᵉ =
    is-faithful-is-injective-hom-map-Precategoryᵉ
  pr2ᵉ equiv-is-faithful-is-injective-hom-map-Precategoryᵉ =
    is-equiv-is-faithful-is-injective-hom-map-Precategoryᵉ
```

## See also

-ᵉ [Faithfulᵉ functorsᵉ betweenᵉ precategories](category-theory.faithful-functors-precategories.mdᵉ)