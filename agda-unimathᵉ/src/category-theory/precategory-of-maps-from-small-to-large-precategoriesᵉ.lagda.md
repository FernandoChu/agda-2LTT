# The precategory of maps and natural transformations from a small to a large precategory

```agda
module category-theory.precategory-of-maps-from-small-to-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategoriesᵉ
open import category-theory.maps-from-small-to-large-precategoriesᵉ
open import category-theory.natural-transformations-maps-from-small-to-large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.identity-typesᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

[Maps](category-theory.maps-from-small-to-large-precategories.mdᵉ) fromᵉ
[(smallᵉ) precategories](category-theory.precategories.mdᵉ) to
[largeᵉ precategories](category-theory.large-precategories.mdᵉ) andᵉ
[naturalᵉ transformations](category-theory.natural-transformations-maps-precategories.mdᵉ)
betweenᵉ themᵉ introduceᵉ aᵉ newᵉ largeᵉ precategoryᵉ whoseᵉ identityᵉ mapᵉ andᵉ
compositionᵉ structureᵉ areᵉ inheritedᵉ pointwiseᵉ fromᵉ theᵉ codomainᵉ precategory.ᵉ
Thisᵉ isᵉ calledᵉ theᵉ **precategoryᵉ ofᵉ mapsᵉ fromᵉ aᵉ smallᵉ to aᵉ largeᵉ precategory**.ᵉ

## Definitions

### The large precategory of maps and natural transformations from a small to a large precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  where

  comp-hom-map-large-precategory-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ γHᵉ : Level}
    {Fᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ}
    {Gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ}
    {Hᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γHᵉ} →
    natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ →
    natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ →
    natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  comp-hom-map-large-precategory-Small-Large-Precategoryᵉ {Fᵉ = Fᵉ} {Gᵉ} {Hᵉ} =
    comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ

  associative-comp-hom-map-large-precategory-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ γHᵉ γIᵉ : Level}
    {Fᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ}
    {Gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ}
    {Hᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γHᵉ}
    {Iᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γIᵉ}
    (hᵉ : natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ)
    (gᵉ : natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (fᵉ : natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ
      ( hᵉ)
      ( comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ gᵉ fᵉ)
  associative-comp-hom-map-large-precategory-Small-Large-Precategoryᵉ
    {Fᵉ = Fᵉ} {Gᵉ} {Hᵉ} {Iᵉ} hᵉ gᵉ fᵉ =
    associative-comp-natural-transformation-map-Small-Large-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ Iᵉ fᵉ gᵉ hᵉ

  involutive-eq-associative-comp-hom-map-large-precategory-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ γHᵉ γIᵉ : Level}
    {Fᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ}
    {Gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ}
    {Hᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γHᵉ}
    {Iᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γIᵉ}
    (hᵉ : natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ)
    (gᵉ : natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (fᵉ : natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ hᵉ gᵉ)
      ( fᵉ) ＝ⁱᵉ
    comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ
      ( hᵉ)
      ( comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-map-large-precategory-Small-Large-Precategoryᵉ
    {Fᵉ = Fᵉ} {Gᵉ} {Hᵉ} {Iᵉ} hᵉ gᵉ fᵉ =
    involutive-eq-associative-comp-natural-transformation-map-Small-Large-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ Iᵉ fᵉ gᵉ hᵉ

  id-hom-map-large-precategory-Small-Large-Precategoryᵉ :
    {γFᵉ : Level} {Fᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ} →
    natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
  id-hom-map-large-precategory-Small-Large-Precategoryᵉ {Fᵉ = Fᵉ} =
    id-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ

  left-unit-law-comp-hom-map-large-precategory-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ : Level}
    {Fᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ}
    {Gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ}
    (aᵉ : natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Gᵉ
      ( id-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ) aᵉ) ＝ᵉ
    ( aᵉ)
  left-unit-law-comp-hom-map-large-precategory-Small-Large-Precategoryᵉ
    { Fᵉ = Fᵉ} {Gᵉ} =
    left-unit-law-comp-natural-transformation-map-Small-Large-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ

  right-unit-law-comp-hom-map-large-precategory-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ : Level}
    {Fᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ}
    {Gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ}
    (aᵉ : natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( comp-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ Gᵉ
        aᵉ (id-natural-transformation-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)) ＝ᵉ
    ( aᵉ)
  right-unit-law-comp-hom-map-large-precategory-Small-Large-Precategoryᵉ
    { Fᵉ = Fᵉ} {Gᵉ} =
    right-unit-law-comp-natural-transformation-map-Small-Large-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ

  map-large-precategory-Small-Large-Precategoryᵉ :
    Large-Precategoryᵉ (λ lᵉ → l1ᵉ ⊔ l2ᵉ ⊔ αᵉ lᵉ ⊔ βᵉ lᵉ lᵉ) (λ lᵉ l'ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ βᵉ lᵉ l'ᵉ)
  obj-Large-Precategoryᵉ map-large-precategory-Small-Large-Precategoryᵉ =
    map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
  hom-set-Large-Precategoryᵉ map-large-precategory-Small-Large-Precategoryᵉ =
    natural-transformation-map-set-Small-Large-Precategoryᵉ Cᵉ Dᵉ
  comp-hom-Large-Precategoryᵉ map-large-precategory-Small-Large-Precategoryᵉ =
    comp-hom-map-large-precategory-Small-Large-Precategoryᵉ
  id-hom-Large-Precategoryᵉ map-large-precategory-Small-Large-Precategoryᵉ =
    id-hom-map-large-precategory-Small-Large-Precategoryᵉ
  involutive-eq-associative-comp-hom-Large-Precategoryᵉ
    map-large-precategory-Small-Large-Precategoryᵉ =
    involutive-eq-associative-comp-hom-map-large-precategory-Small-Large-Precategoryᵉ
  left-unit-law-comp-hom-Large-Precategoryᵉ
    map-large-precategory-Small-Large-Precategoryᵉ =
    left-unit-law-comp-hom-map-large-precategory-Small-Large-Precategoryᵉ
  right-unit-law-comp-hom-Large-Precategoryᵉ
    map-large-precategory-Small-Large-Precategoryᵉ =
    right-unit-law-comp-hom-map-large-precategory-Small-Large-Precategoryᵉ
```

### The small precategories of maps and natural transformations from a small to a large precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  where

  map-precategory-Small-Large-Precategoryᵉ :
    (lᵉ : Level) → Precategoryᵉ (l1ᵉ ⊔ l2ᵉ ⊔ αᵉ lᵉ ⊔ βᵉ lᵉ lᵉ) (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ lᵉ lᵉ)
  map-precategory-Small-Large-Precategoryᵉ =
    precategory-Large-Precategoryᵉ
      ( map-large-precategory-Small-Large-Precategoryᵉ Cᵉ Dᵉ)
```