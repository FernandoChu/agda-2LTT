# Functors between large categories

```agda
module category-theory.functors-large-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategoriesᵉ
open import category-theory.large-categoriesᵉ

open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **functor**ᵉ fromᵉ aᵉ [largeᵉ category](category-theory.large-categories.mdᵉ) `C`ᵉ
to aᵉ largeᵉ categoryᵉ `D`ᵉ isᵉ aᵉ
[functor](category-theory.functors-large-precategories.mdᵉ) betweenᵉ theᵉ
underlyingᵉ [largeᵉ precategories](category-theory.large-precategories.mdᵉ) ofᵉ `C`ᵉ
andᵉ `D`.ᵉ Inᵉ otherᵉ words,ᵉ functorsᵉ ofᵉ largeᵉ categoriesᵉ consistᵉ ofᵉ:

-ᵉ aᵉ mapᵉ `F₀ᵉ : Cᵉ → D`ᵉ onᵉ objects,ᵉ
-ᵉ aᵉ mapᵉ `F₁ᵉ : homᵉ xᵉ yᵉ → homᵉ (F₀ᵉ xᵉ) (F₀ᵉ y)`ᵉ onᵉ morphisms,ᵉ suchᵉ thatᵉ theᵉ followingᵉ
  identitiesᵉ holdᵉ:
-ᵉ `Fᵉ id_xᵉ = id_(Fᵉ x)`,ᵉ
-ᵉ `Fᵉ (gᵉ ∘ᵉ fᵉ) = Fᵉ gᵉ ∘ᵉ Fᵉ f`.ᵉ

## Definition

```agda
module _
  {αCᵉ αDᵉ : Level → Level} {βCᵉ βDᵉ : Level → Level → Level} (γᵉ : Level → Level)
  (Cᵉ : Large-Categoryᵉ αCᵉ βCᵉ) (Dᵉ : Large-Categoryᵉ αDᵉ βDᵉ)
  where

  functor-Large-Categoryᵉ : UUωᵉ
  functor-Large-Categoryᵉ =
    functor-Large-Precategoryᵉ γᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)

module _
  {αCᵉ αDᵉ : Level → Level} {βCᵉ βDᵉ : Level → Level → Level} {γᵉ : Level → Level}
  (Cᵉ : Large-Categoryᵉ αCᵉ βCᵉ) (Dᵉ : Large-Categoryᵉ αDᵉ βDᵉ)
  (Fᵉ : functor-Large-Categoryᵉ γᵉ Cᵉ Dᵉ)
  where

  obj-functor-Large-Categoryᵉ :
    {l1ᵉ : Level} → obj-Large-Categoryᵉ Cᵉ l1ᵉ → obj-Large-Categoryᵉ Dᵉ (γᵉ l1ᵉ)
  obj-functor-Large-Categoryᵉ =
    obj-functor-Large-Precategoryᵉ Fᵉ

  hom-functor-Large-Categoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ} →
    hom-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ →
    hom-Large-Categoryᵉ Dᵉ
      ( obj-functor-Large-Categoryᵉ Xᵉ)
      ( obj-functor-Large-Categoryᵉ Yᵉ)
  hom-functor-Large-Categoryᵉ =
    hom-functor-Large-Precategoryᵉ Fᵉ

  preserves-id-functor-Large-Categoryᵉ :
    {l1ᵉ : Level} {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ} →
    hom-functor-Large-Categoryᵉ (id-hom-Large-Categoryᵉ Cᵉ {Xᵉ = Xᵉ}) ＝ᵉ
    id-hom-Large-Categoryᵉ Dᵉ
  preserves-id-functor-Large-Categoryᵉ =
    preserves-id-functor-Large-Precategoryᵉ Fᵉ

  preserves-comp-functor-Large-Categoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
    {Zᵉ : obj-Large-Categoryᵉ Cᵉ l3ᵉ}
    (gᵉ : hom-Large-Categoryᵉ Cᵉ Yᵉ Zᵉ) (fᵉ : hom-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ) →
    hom-functor-Large-Categoryᵉ (comp-hom-Large-Categoryᵉ Cᵉ gᵉ fᵉ) ＝ᵉ
    comp-hom-Large-Categoryᵉ Dᵉ
      ( hom-functor-Large-Categoryᵉ gᵉ)
      ( hom-functor-Large-Categoryᵉ fᵉ)
  preserves-comp-functor-Large-Categoryᵉ =
    preserves-comp-functor-Large-Precategoryᵉ Fᵉ
```

### The identity functor

Thereᵉ isᵉ anᵉ identityᵉ functorᵉ onᵉ anyᵉ largeᵉ category.ᵉ

```agda
id-functor-Large-Categoryᵉ :
  {αCᵉ : Level → Level} {βCᵉ : Level → Level → Level} →
  (Cᵉ : Large-Categoryᵉ αCᵉ βCᵉ) →
  functor-Large-Categoryᵉ (λ lᵉ → lᵉ) Cᵉ Cᵉ
id-functor-Large-Categoryᵉ Cᵉ =
  id-functor-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ)
```

### Composition of functors

Anyᵉ twoᵉ compatibleᵉ functorsᵉ canᵉ beᵉ composedᵉ to aᵉ newᵉ functor.ᵉ

```agda
comp-functor-Large-Categoryᵉ :
  {αCᵉ αDᵉ αEᵉ γGᵉ γFᵉ : Level → Level}
  {βCᵉ βDᵉ βEᵉ : Level → Level → Level} →
  (Cᵉ : Large-Categoryᵉ αCᵉ βCᵉ)
  (Dᵉ : Large-Categoryᵉ αDᵉ βDᵉ)
  (Eᵉ : Large-Categoryᵉ αEᵉ βEᵉ) →
  functor-Large-Categoryᵉ γGᵉ Dᵉ Eᵉ →
  functor-Large-Categoryᵉ γFᵉ Cᵉ Dᵉ →
  functor-Large-Categoryᵉ (λ lᵉ → γGᵉ (γFᵉ lᵉ)) Cᵉ Eᵉ
comp-functor-Large-Categoryᵉ Cᵉ Dᵉ Eᵉ =
  comp-functor-Large-Precategoryᵉ
    ( large-precategory-Large-Categoryᵉ Cᵉ)
    ( large-precategory-Large-Categoryᵉ Dᵉ)
    ( large-precategory-Large-Categoryᵉ Eᵉ)
```