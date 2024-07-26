# Faithful functors between precategories

```agda
module category-theory.faithful-functors-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.faithful-maps-precategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [functor](category-theory.functors-precategories.mdᵉ) betweenᵉ
[precategories](category-theory.precategories.mdᵉ) `C`ᵉ andᵉ `D`ᵉ isᵉ **faithful**ᵉ ifᵉ
it'sᵉ anᵉ [embedding](foundation-core.embeddings.mdᵉ) onᵉ hom-sets.ᵉ

Noteᵉ thatᵉ embeddingsᵉ onᵉ [sets](foundation-core.sets.mdᵉ) happenᵉ to coincideᵉ with
[injections](foundation.injective-maps.md).ᵉ However,ᵉ weᵉ defineᵉ faithfulᵉ functorsᵉ
in termsᵉ ofᵉ embeddingsᵉ becauseᵉ thisᵉ isᵉ theᵉ notionᵉ thatᵉ generalizes.ᵉ

## Definition

### The predicate on functors between precategories of being faithful

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-faithful-functor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-faithful-functor-Precategoryᵉ =
    is-faithful-map-Precategoryᵉ Cᵉ Dᵉ (map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  is-prop-is-faithful-functor-Precategoryᵉ :
    is-propᵉ is-faithful-functor-Precategoryᵉ
  is-prop-is-faithful-functor-Precategoryᵉ =
    is-prop-is-faithful-map-Precategoryᵉ Cᵉ Dᵉ (map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  is-faithful-prop-functor-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-faithful-prop-functor-Precategoryᵉ =
    is-faithful-prop-map-Precategoryᵉ Cᵉ Dᵉ (map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
```

### The type of faithful functors between two precategories

```agda
faithful-functor-Precategoryᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
faithful-functor-Precategoryᵉ Cᵉ Dᵉ =
  Σᵉ (functor-Precategoryᵉ Cᵉ Dᵉ) (is-faithful-functor-Precategoryᵉ Cᵉ Dᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : faithful-functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  functor-faithful-functor-Precategoryᵉ : functor-Precategoryᵉ Cᵉ Dᵉ
  functor-faithful-functor-Precategoryᵉ = pr1ᵉ Fᵉ

  is-faithful-faithful-functor-Precategoryᵉ :
    is-faithful-functor-Precategoryᵉ Cᵉ Dᵉ functor-faithful-functor-Precategoryᵉ
  is-faithful-faithful-functor-Precategoryᵉ = pr2ᵉ Fᵉ

  obj-faithful-functor-Precategoryᵉ : obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Dᵉ
  obj-faithful-functor-Precategoryᵉ =
    obj-functor-Precategoryᵉ Cᵉ Dᵉ functor-faithful-functor-Precategoryᵉ

  hom-faithful-functor-Precategoryᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Dᵉ
      ( obj-faithful-functor-Precategoryᵉ xᵉ)
      ( obj-faithful-functor-Precategoryᵉ yᵉ)
  hom-faithful-functor-Precategoryᵉ =
    hom-functor-Precategoryᵉ Cᵉ Dᵉ functor-faithful-functor-Precategoryᵉ
```

### The predicate on functors between precategories of being injective on hom-sets

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-injective-hom-functor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-injective-hom-functor-Precategoryᵉ =
    is-injective-hom-map-Precategoryᵉ Cᵉ Dᵉ (map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  is-prop-is-injective-hom-functor-Precategoryᵉ :
    is-propᵉ is-injective-hom-functor-Precategoryᵉ
  is-prop-is-injective-hom-functor-Precategoryᵉ =
    is-prop-is-injective-hom-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  is-injective-hom-prop-functor-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-injective-hom-prop-functor-Precategoryᵉ =
    is-injective-hom-prop-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
```

## Properties

### A functor of precategories is faithful if and only if it is injective on hom-sets

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-injective-hom-is-faithful-functor-Precategoryᵉ :
    is-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ →
    is-injective-hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  is-injective-hom-is-faithful-functor-Precategoryᵉ =
    is-injective-hom-is-faithful-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  is-faithful-is-injective-hom-functor-Precategoryᵉ :
    is-injective-hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ →
    is-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  is-faithful-is-injective-hom-functor-Precategoryᵉ =
    is-faithful-is-injective-hom-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  is-equiv-is-injective-hom-is-faithful-functor-Precategoryᵉ :
    is-equivᵉ is-injective-hom-is-faithful-functor-Precategoryᵉ
  is-equiv-is-injective-hom-is-faithful-functor-Precategoryᵉ =
    is-equiv-is-injective-hom-is-faithful-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  is-equiv-is-faithful-is-injective-hom-functor-Precategoryᵉ :
    is-equivᵉ is-faithful-is-injective-hom-functor-Precategoryᵉ
  is-equiv-is-faithful-is-injective-hom-functor-Precategoryᵉ =
    is-equiv-is-faithful-is-injective-hom-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  equiv-is-injective-hom-is-faithful-functor-Precategoryᵉ :
    is-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ ≃ᵉ
    is-injective-hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  equiv-is-injective-hom-is-faithful-functor-Precategoryᵉ =
    equiv-is-injective-hom-is-faithful-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  equiv-is-faithful-is-injective-hom-functor-Precategoryᵉ :
    is-injective-hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ ≃ᵉ
    is-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  equiv-is-faithful-is-injective-hom-functor-Precategoryᵉ =
    equiv-is-faithful-is-injective-hom-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
```

### Faithful functors are faithful on isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (is-faithful-Fᵉ : is-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
  where

  is-faithful-on-isos-is-faithful-functor-Precategoryᵉ :
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) →
    is-embᵉ (preserves-iso-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ {xᵉ} {yᵉ})
  is-faithful-on-isos-is-faithful-functor-Precategoryᵉ xᵉ yᵉ =
    is-emb-right-factorᵉ _ _
      ( is-emb-inclusion-subtypeᵉ (is-iso-prop-Precategoryᵉ Dᵉ))
      ( is-emb-compᵉ _ _
        ( is-faithful-Fᵉ xᵉ yᵉ)
        ( is-emb-inclusion-subtypeᵉ (is-iso-prop-Precategoryᵉ Cᵉ)))
```