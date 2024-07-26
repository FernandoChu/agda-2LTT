# The precategory of functors and natural transformations from small to large precategories

```agda
module category-theory.precategory-of-functors-from-small-to-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-from-small-to-large-precategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.natural-transformations-functors-from-small-to-large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.identity-typesᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

[Functors](category-theory.functors-from-small-to-large-precategories.mdᵉ) fromᵉ aᵉ
smallᵉ [precategory](category-theory.precategories.mdᵉ) `C`ᵉ to aᵉ
[largeᵉ precategory](category-theory.large-precategories.mdᵉ) `D`ᵉ andᵉ
[naturalᵉ transformations](category-theory.natural-transformations-functors-precategories.mdᵉ)
betweenᵉ themᵉ formᵉ aᵉ largeᵉ precategoryᵉ whoseᵉ identityᵉ mapᵉ andᵉ compositionᵉ
structureᵉ areᵉ inheritedᵉ pointwiseᵉ fromᵉ theᵉ codomainᵉ precategory.ᵉ Thisᵉ isᵉ calledᵉ
theᵉ **precategoryᵉ ofᵉ functorsᵉ fromᵉ smallᵉ to largeᵉ precategories**.ᵉ

## Definitions

### The large precategory of functors and natural transformations from a small to a large precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  where

  hom-functor-large-precategory-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ : Level}
    (Fᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ)
    (Gᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ γFᵉ γGᵉ)
  hom-functor-large-precategory-Small-Large-Precategoryᵉ =
    natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ

  comp-hom-functor-large-precategory-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ γHᵉ : Level}
    {Fᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ}
    {Gᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ}
    {Hᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γHᵉ} →
    natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ →
    natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ →
    natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  comp-hom-functor-large-precategory-Small-Large-Precategoryᵉ {Fᵉ = Fᵉ} {Gᵉ} {Hᵉ} =
    comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ

  associative-comp-hom-functor-large-precategory-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ γHᵉ γIᵉ : Level}
    {Fᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ}
    {Gᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ}
    {Hᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γHᵉ}
    {Iᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γIᵉ}
    (hᵉ : natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ)
    (gᵉ : natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (fᵉ : natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ
      ( hᵉ)
      ( comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ gᵉ fᵉ)
  associative-comp-hom-functor-large-precategory-Small-Large-Precategoryᵉ
    {Fᵉ = Fᵉ} {Gᵉ} {Hᵉ} {Iᵉ} hᵉ gᵉ fᵉ =
    associative-comp-natural-transformation-Small-Large-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ Iᵉ fᵉ gᵉ hᵉ

  involutive-eq-associative-comp-hom-functor-large-precategory-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ γHᵉ γIᵉ : Level}
    {Fᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ}
    {Gᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ}
    {Hᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γHᵉ}
    {Iᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γIᵉ}
    (hᵉ : natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ)
    (gᵉ : natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (fᵉ : natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ hᵉ gᵉ)
      ( fᵉ) ＝ⁱᵉ
    comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ
      ( hᵉ)
      ( comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-functor-large-precategory-Small-Large-Precategoryᵉ
    {Fᵉ = Fᵉ} {Gᵉ} {Hᵉ} {Iᵉ} hᵉ gᵉ fᵉ =
    involutive-eq-associative-comp-natural-transformation-Small-Large-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ Iᵉ fᵉ gᵉ hᵉ

  id-hom-functor-large-precategory-Small-Large-Precategoryᵉ :
    {γFᵉ : Level} {Fᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ} →
    natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
  id-hom-functor-large-precategory-Small-Large-Precategoryᵉ {Fᵉ = Fᵉ} =
    id-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ

  left-unit-law-comp-hom-functor-large-precategory-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ : Level}
    {Fᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ}
    {Gᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ}
    (aᵉ : natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Gᵉ
      ( id-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ) aᵉ ＝ᵉ
    aᵉ
  left-unit-law-comp-hom-functor-large-precategory-Small-Large-Precategoryᵉ
    { Fᵉ = Fᵉ} {Gᵉ} =
    left-unit-law-comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ

  right-unit-law-comp-hom-functor-large-precategory-Small-Large-Precategoryᵉ :
    {γFᵉ γGᵉ : Level}
    {Fᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γFᵉ}
    {Gᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γGᵉ}
    (aᵉ : natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ Gᵉ
        aᵉ (id-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ) ＝ᵉ
    aᵉ
  right-unit-law-comp-hom-functor-large-precategory-Small-Large-Precategoryᵉ
    { Fᵉ = Fᵉ} {Gᵉ} =
    right-unit-law-comp-natural-transformation-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ

  functor-large-precategory-Small-Large-Precategoryᵉ :
    Large-Precategoryᵉ (λ lᵉ → l1ᵉ ⊔ l2ᵉ ⊔ αᵉ lᵉ ⊔ βᵉ lᵉ lᵉ) (λ lᵉ l'ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ βᵉ lᵉ l'ᵉ)
  obj-Large-Precategoryᵉ functor-large-precategory-Small-Large-Precategoryᵉ =
    functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ
  hom-set-Large-Precategoryᵉ functor-large-precategory-Small-Large-Precategoryᵉ =
    natural-transformation-set-Small-Large-Precategoryᵉ Cᵉ Dᵉ
  comp-hom-Large-Precategoryᵉ
    functor-large-precategory-Small-Large-Precategoryᵉ {Xᵉ = Fᵉ} {Gᵉ} {Hᵉ} =
    comp-hom-functor-large-precategory-Small-Large-Precategoryᵉ {Fᵉ = Fᵉ} {Gᵉ} {Hᵉ}
  id-hom-Large-Precategoryᵉ
    functor-large-precategory-Small-Large-Precategoryᵉ {Xᵉ = Fᵉ} =
    id-hom-functor-large-precategory-Small-Large-Precategoryᵉ {Fᵉ = Fᵉ}
  involutive-eq-associative-comp-hom-Large-Precategoryᵉ
    functor-large-precategory-Small-Large-Precategoryᵉ {Xᵉ = Fᵉ} {Gᵉ} {Hᵉ} {Iᵉ} =
    involutive-eq-associative-comp-hom-functor-large-precategory-Small-Large-Precategoryᵉ
      { Fᵉ = Fᵉ} {Gᵉ} {Hᵉ} {Iᵉ}
  left-unit-law-comp-hom-Large-Precategoryᵉ
    functor-large-precategory-Small-Large-Precategoryᵉ {Xᵉ = Fᵉ} {Gᵉ} =
    left-unit-law-comp-hom-functor-large-precategory-Small-Large-Precategoryᵉ
      { Fᵉ = Fᵉ} {Gᵉ}
  right-unit-law-comp-hom-Large-Precategoryᵉ
    functor-large-precategory-Small-Large-Precategoryᵉ {Xᵉ = Fᵉ} {Gᵉ} =
    right-unit-law-comp-hom-functor-large-precategory-Small-Large-Precategoryᵉ
      { Fᵉ = Fᵉ} {Gᵉ}
```

### The small precategories of functors and natural transformations from a small to a large precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  where

  functor-precategory-Small-Large-Precategoryᵉ :
    (lᵉ : Level) → Precategoryᵉ (l1ᵉ ⊔ l2ᵉ ⊔ αᵉ lᵉ ⊔ βᵉ lᵉ lᵉ) (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ lᵉ lᵉ)
  functor-precategory-Small-Large-Precategoryᵉ =
    precategory-Large-Precategoryᵉ
      ( functor-large-precategory-Small-Large-Precategoryᵉ Cᵉ Dᵉ)
```