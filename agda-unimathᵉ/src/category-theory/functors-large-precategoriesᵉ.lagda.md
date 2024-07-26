# Functors between large precategories

```agda
module category-theory.functors-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **functor**ᵉ fromᵉ aᵉ [largeᵉ precategory](category-theory.large-precategories.mdᵉ)
`C`ᵉ to aᵉ largeᵉ precategoryᵉ `D`ᵉ consistsᵉ ofᵉ:

-ᵉ aᵉ mapᵉ `F₀ᵉ : Cᵉ → D`ᵉ onᵉ objects,ᵉ
-ᵉ aᵉ mapᵉ `F₁ᵉ : homᵉ xᵉ yᵉ → homᵉ (F₀ᵉ xᵉ) (F₀ᵉ y)`ᵉ onᵉ morphisms,ᵉ suchᵉ thatᵉ theᵉ followingᵉ
  identitiesᵉ holdᵉ:
-ᵉ `Fᵉ id_xᵉ = id_(Fᵉ x)`,ᵉ
-ᵉ `Fᵉ (gᵉ ∘ᵉ fᵉ) = Fᵉ gᵉ ∘ᵉ Fᵉ f`.ᵉ

## Definition

```agda
module _
  {αCᵉ αDᵉ : Level → Level} {βCᵉ βDᵉ : Level → Level → Level} (γᵉ : Level → Level)
  (Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ) (Dᵉ : Large-Precategoryᵉ αDᵉ βDᵉ)
  where

  record functor-Large-Precategoryᵉ : UUωᵉ
    where
    constructor make-functorᵉ
    field
      obj-functor-Large-Precategoryᵉ :
        { l1ᵉ : Level} →
        obj-Large-Precategoryᵉ Cᵉ l1ᵉ → obj-Large-Precategoryᵉ Dᵉ (γᵉ l1ᵉ)
      hom-functor-Large-Precategoryᵉ :
        { l1ᵉ l2ᵉ : Level}
        { Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
        { Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ} →
        hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ →
        hom-Large-Precategoryᵉ Dᵉ
          ( obj-functor-Large-Precategoryᵉ Xᵉ)
          ( obj-functor-Large-Precategoryᵉ Yᵉ)
      preserves-comp-functor-Large-Precategoryᵉ :
        { l1ᵉ l2ᵉ l3ᵉ : Level}
        { Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
        { Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
        { Zᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ}
        ( gᵉ : hom-Large-Precategoryᵉ Cᵉ Yᵉ Zᵉ)
        ( fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ) →
        ( hom-functor-Large-Precategoryᵉ
          ( comp-hom-Large-Precategoryᵉ Cᵉ gᵉ fᵉ)) ＝ᵉ
        ( comp-hom-Large-Precategoryᵉ Dᵉ
          ( hom-functor-Large-Precategoryᵉ gᵉ)
          ( hom-functor-Large-Precategoryᵉ fᵉ))
      preserves-id-functor-Large-Precategoryᵉ :
        { l1ᵉ : Level} {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} →
        ( hom-functor-Large-Precategoryᵉ
          ( id-hom-Large-Precategoryᵉ Cᵉ {Xᵉ = Xᵉ})) ＝ᵉ
        ( id-hom-Large-Precategoryᵉ Dᵉ {Xᵉ = obj-functor-Large-Precategoryᵉ Xᵉ})

  open functor-Large-Precategoryᵉ public
```

### The identity functor

```agda
id-functor-Large-Precategoryᵉ :
  {αCᵉ : Level → Level} {βCᵉ : Level → Level → Level} →
  (Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ) →
  functor-Large-Precategoryᵉ (λ lᵉ → lᵉ) Cᵉ Cᵉ
obj-functor-Large-Precategoryᵉ
  ( id-functor-Large-Precategoryᵉ Cᵉ) =
  idᵉ
hom-functor-Large-Precategoryᵉ
  ( id-functor-Large-Precategoryᵉ Cᵉ) =
  idᵉ
preserves-comp-functor-Large-Precategoryᵉ
  ( id-functor-Large-Precategoryᵉ Cᵉ) gᵉ fᵉ =
  reflᵉ
preserves-id-functor-Large-Precategoryᵉ
  ( id-functor-Large-Precategoryᵉ Cᵉ) =
  reflᵉ
```

### Composition of functors

```agda
module _
  {αCᵉ αDᵉ αEᵉ γGᵉ γFᵉ : Level → Level}
  {βCᵉ βDᵉ βEᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ)
  (Dᵉ : Large-Precategoryᵉ αDᵉ βDᵉ)
  (Eᵉ : Large-Precategoryᵉ αEᵉ βEᵉ)
  (Gᵉ : functor-Large-Precategoryᵉ γGᵉ Dᵉ Eᵉ)
  (Fᵉ : functor-Large-Precategoryᵉ γFᵉ Cᵉ Dᵉ)
  where

  obj-comp-functor-Large-Precategoryᵉ :
    {l1ᵉ : Level} →
    obj-Large-Precategoryᵉ Cᵉ l1ᵉ → obj-Large-Precategoryᵉ Eᵉ (γGᵉ (γFᵉ l1ᵉ))
  obj-comp-functor-Large-Precategoryᵉ =
    obj-functor-Large-Precategoryᵉ Gᵉ ∘ᵉ obj-functor-Large-Precategoryᵉ Fᵉ

  hom-comp-functor-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ} →
    hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ →
    hom-Large-Precategoryᵉ Eᵉ
      ( obj-comp-functor-Large-Precategoryᵉ Xᵉ)
      ( obj-comp-functor-Large-Precategoryᵉ Yᵉ)
  hom-comp-functor-Large-Precategoryᵉ =
    hom-functor-Large-Precategoryᵉ Gᵉ ∘ᵉ hom-functor-Large-Precategoryᵉ Fᵉ

  preserves-comp-comp-functor-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
    {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
    {Zᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ}
    (gᵉ : hom-Large-Precategoryᵉ Cᵉ Yᵉ Zᵉ) (fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ) →
    hom-comp-functor-Large-Precategoryᵉ
      ( comp-hom-Large-Precategoryᵉ Cᵉ gᵉ fᵉ) ＝ᵉ
    comp-hom-Large-Precategoryᵉ Eᵉ
      ( hom-comp-functor-Large-Precategoryᵉ gᵉ)
      ( hom-comp-functor-Large-Precategoryᵉ fᵉ)
  preserves-comp-comp-functor-Large-Precategoryᵉ gᵉ fᵉ =
    ( apᵉ
      ( hom-functor-Large-Precategoryᵉ Gᵉ)
      ( preserves-comp-functor-Large-Precategoryᵉ Fᵉ gᵉ fᵉ)) ∙ᵉ
    ( preserves-comp-functor-Large-Precategoryᵉ Gᵉ
      ( hom-functor-Large-Precategoryᵉ Fᵉ gᵉ)
      ( hom-functor-Large-Precategoryᵉ Fᵉ fᵉ))

  preserves-id-comp-functor-Large-Precategoryᵉ :
    {l1ᵉ : Level} {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} →
    hom-comp-functor-Large-Precategoryᵉ (id-hom-Large-Precategoryᵉ Cᵉ {Xᵉ = Xᵉ}) ＝ᵉ
    id-hom-Large-Precategoryᵉ Eᵉ
  preserves-id-comp-functor-Large-Precategoryᵉ =
    ( apᵉ
      ( hom-functor-Large-Precategoryᵉ Gᵉ)
      ( preserves-id-functor-Large-Precategoryᵉ Fᵉ)) ∙ᵉ
    ( preserves-id-functor-Large-Precategoryᵉ Gᵉ)

  comp-functor-Large-Precategoryᵉ :
    functor-Large-Precategoryᵉ (λ lᵉ → γGᵉ (γFᵉ lᵉ)) Cᵉ Eᵉ
  obj-functor-Large-Precategoryᵉ
    comp-functor-Large-Precategoryᵉ =
    obj-comp-functor-Large-Precategoryᵉ
  hom-functor-Large-Precategoryᵉ
    comp-functor-Large-Precategoryᵉ =
    hom-comp-functor-Large-Precategoryᵉ
  preserves-comp-functor-Large-Precategoryᵉ
    comp-functor-Large-Precategoryᵉ =
    preserves-comp-comp-functor-Large-Precategoryᵉ
  preserves-id-functor-Large-Precategoryᵉ
    comp-functor-Large-Precategoryᵉ =
    preserves-id-comp-functor-Large-Precategoryᵉ
```