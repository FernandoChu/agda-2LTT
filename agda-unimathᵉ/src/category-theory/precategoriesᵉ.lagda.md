# Precategories

```agda
module category-theory.precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.nonunital-precategoriesᵉ
open import category-theory.set-magmoidsᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "precategory"ᵉ Agda=Precategoryᵉ}} `𝒞`ᵉ in Homotopyᵉ Typeᵉ Theoryᵉ isᵉ theᵉ
structureᵉ ofᵉ anᵉ associativeᵉ andᵉ unitalᵉ
[compositionᵉ operation](category-theory.composition-operations-on-binary-families-of-sets.mdᵉ)
onᵉ aᵉ binaryᵉ familiyᵉ ofᵉ sets.ᵉ

Thisᵉ meansᵉ aᵉ precategoryᵉ consistsᵉ ofᵉ:

-ᵉ **Objects.**ᵉ Aᵉ typeᵉ `Obᵉ 𝒞`ᵉ ofᵉ _objects_.ᵉ
-ᵉ **Morphisms.**ᵉ Forᵉ eachᵉ pairᵉ ofᵉ objectsᵉ `xᵉ yᵉ : Obᵉ 𝒞`,ᵉ aᵉ
  [set](foundation-core.sets.mdᵉ) ofᵉ _morphismsᵉ_ `homᵉ 𝒞ᵉ xᵉ yᵉ : Set`.ᵉ
-ᵉ **Composition.**ᵉ Forᵉ everyᵉ tripleᵉ ofᵉ objectsᵉ `xᵉ yᵉ zᵉ : Obᵉ 𝒞`ᵉ thereᵉ isᵉ aᵉ
  _compositionᵉ operationᵉ_ onᵉ morphismsᵉ
  ```text
    _∘ᵉ_ : homᵉ 𝒞ᵉ yᵉ zᵉ → homᵉ 𝒞ᵉ xᵉ yᵉ → homᵉ 𝒞ᵉ xᵉ z.ᵉ
  ```
-ᵉ **Associativity.**ᵉ Forᵉ everyᵉ tripleᵉ ofᵉ composableᵉ morphisms,ᵉ weᵉ haveᵉ
  ```text
    (hᵉ ∘ᵉ gᵉ) ∘ᵉ fᵉ ＝ᵉ hᵉ ∘ᵉ (gᵉ ∘ᵉ f).ᵉ
  ```
-ᵉ **Identityᵉ morphisms.**ᵉ Forᵉ everyᵉ objectᵉ `xᵉ : Obᵉ 𝒞`,ᵉ thereᵉ isᵉ aᵉ distinguishedᵉ
  _identityᵉ_ morphismᵉ `id_xᵉ : homᵉ 𝒞ᵉ xᵉ x`.ᵉ
-ᵉ **Unitality.**ᵉ Theᵉ identityᵉ morphismsᵉ areᵉ two-sidedᵉ unitsᵉ forᵉ theᵉ compositionᵉ
  operation,ᵉ meaningᵉ thatᵉ forᵉ everyᵉ `fᵉ : homᵉ 𝒞ᵉ xᵉ y`ᵉ weᵉ haveᵉ
  ```text
    id_yᵉ ∘ᵉ fᵉ ＝ᵉ fᵉ   andᵉ   fᵉ ∘ᵉ id_xᵉ ＝ᵉ f.ᵉ
  ```

**Note.**ᵉ Theᵉ reasonᵉ thisᵉ isᵉ calledᵉ aᵉ *pre*categoryᵉ andᵉ notᵉ aᵉ _categoryᵉ_ in
Homotopyᵉ Typeᵉ Theoryᵉ isᵉ thatᵉ weᵉ reserveᵉ thatᵉ nameᵉ forᵉ precategoriesᵉ where theᵉ
[identityᵉ types](foundation-core.identity-types.mdᵉ) ofᵉ theᵉ typeᵉ ofᵉ objectsᵉ areᵉ
characterizedᵉ byᵉ theᵉ
[isomorphismᵉ sets](category-theory.isomorphisms-in-precategories.md).ᵉ

## Definitions

### The predicate on composition operations on binary families of sets of being a precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (hom-setᵉ : Aᵉ → Aᵉ → Setᵉ l2ᵉ)
  (comp-homᵉ : composition-operation-binary-family-Setᵉ hom-setᵉ)
  where

  is-precategory-prop-composition-operation-binary-family-Setᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-precategory-prop-composition-operation-binary-family-Setᵉ =
    product-Propᵉ
      ( is-unital-prop-composition-operation-binary-family-Setᵉ hom-setᵉ comp-homᵉ)
      ( is-associative-prop-composition-operation-binary-family-Setᵉ
        ( hom-setᵉ)
        ( comp-homᵉ))

  is-precategory-composition-operation-binary-family-Setᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-precategory-composition-operation-binary-family-Setᵉ =
    type-Propᵉ is-precategory-prop-composition-operation-binary-family-Setᵉ

  is-prop-is-precategory-composition-operation-binary-family-Setᵉ :
    is-propᵉ is-precategory-composition-operation-binary-family-Setᵉ
  is-prop-is-precategory-composition-operation-binary-family-Setᵉ =
    is-prop-type-Propᵉ
      is-precategory-prop-composition-operation-binary-family-Setᵉ
```

### The type of precategories

```agda
Precategoryᵉ :
  (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Precategoryᵉ l1ᵉ l2ᵉ =
  Σᵉ ( UUᵉ l1ᵉ)
    ( λ Aᵉ →
      Σᵉ ( Aᵉ → Aᵉ → Setᵉ l2ᵉ)
        ( λ hom-setᵉ →
          Σᵉ ( associative-composition-operation-binary-family-Setᵉ hom-setᵉ)
            ( λ (comp-homᵉ ,ᵉ assoc-compᵉ) →
              is-unital-composition-operation-binary-family-Setᵉ
                ( hom-setᵉ)
                ( comp-homᵉ))))

make-Precategoryᵉ :
  { l1ᵉ l2ᵉ : Level}
  ( objᵉ : UUᵉ l1ᵉ)
  ( hom-setᵉ : objᵉ → objᵉ → Setᵉ l2ᵉ)
  ( _∘ᵉ_ : composition-operation-binary-family-Setᵉ hom-setᵉ)
  ( idᵉ : (xᵉ : objᵉ) → type-Setᵉ (hom-setᵉ xᵉ xᵉ))
  ( assoc-comp-homᵉ :
    { xᵉ yᵉ zᵉ wᵉ : objᵉ} →
    ( hᵉ : type-Setᵉ (hom-setᵉ zᵉ wᵉ))
    ( gᵉ : type-Setᵉ (hom-setᵉ yᵉ zᵉ))
    ( fᵉ : type-Setᵉ (hom-setᵉ xᵉ yᵉ)) →
    ( (hᵉ ∘ᵉ gᵉ) ∘ᵉ fᵉ ＝ᵉ hᵉ ∘ᵉ (gᵉ ∘ᵉ fᵉ)))
  ( left-unit-comp-homᵉ :
    { xᵉ yᵉ : objᵉ} (fᵉ : type-Setᵉ (hom-setᵉ xᵉ yᵉ)) → idᵉ yᵉ ∘ᵉ fᵉ ＝ᵉ fᵉ)
  ( right-unit-comp-homᵉ :
    { xᵉ yᵉ : objᵉ} (fᵉ : type-Setᵉ (hom-setᵉ xᵉ yᵉ)) → fᵉ ∘ᵉ idᵉ xᵉ ＝ᵉ fᵉ) →
  Precategoryᵉ l1ᵉ l2ᵉ
make-Precategoryᵉ
  objᵉ hom-setᵉ _∘ᵉ_ idᵉ assoc-comp-homᵉ left-unit-comp-homᵉ right-unit-comp-homᵉ =
  ( ( objᵉ) ,ᵉ
    ( hom-setᵉ) ,ᵉ
    ( _∘ᵉ_ ,ᵉ (λ hᵉ gᵉ fᵉ → involutive-eq-eqᵉ (assoc-comp-homᵉ hᵉ gᵉ fᵉ))) ,ᵉ
    ( idᵉ) ,ᵉ
    ( left-unit-comp-homᵉ) ,ᵉ
    ( right-unit-comp-homᵉ))

{-# INLINE make-Precategoryᵉ #-}

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  obj-Precategoryᵉ : UUᵉ l1ᵉ
  obj-Precategoryᵉ = pr1ᵉ Cᵉ

  hom-set-Precategoryᵉ : (xᵉ yᵉ : obj-Precategoryᵉ) → Setᵉ l2ᵉ
  hom-set-Precategoryᵉ = pr1ᵉ (pr2ᵉ Cᵉ)

  hom-Precategoryᵉ : (xᵉ yᵉ : obj-Precategoryᵉ) → UUᵉ l2ᵉ
  hom-Precategoryᵉ xᵉ yᵉ = type-Setᵉ (hom-set-Precategoryᵉ xᵉ yᵉ)

  is-set-hom-Precategoryᵉ :
    (xᵉ yᵉ : obj-Precategoryᵉ) → is-setᵉ (hom-Precategoryᵉ xᵉ yᵉ)
  is-set-hom-Precategoryᵉ xᵉ yᵉ = is-set-type-Setᵉ (hom-set-Precategoryᵉ xᵉ yᵉ)

  associative-composition-operation-Precategoryᵉ :
    associative-composition-operation-binary-family-Setᵉ hom-set-Precategoryᵉ
  associative-composition-operation-Precategoryᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ Cᵉ))

  comp-hom-Precategoryᵉ :
    {xᵉ yᵉ zᵉ : obj-Precategoryᵉ} →
    hom-Precategoryᵉ yᵉ zᵉ →
    hom-Precategoryᵉ xᵉ yᵉ →
    hom-Precategoryᵉ xᵉ zᵉ
  comp-hom-Precategoryᵉ =
    comp-hom-associative-composition-operation-binary-family-Setᵉ
      ( hom-set-Precategoryᵉ)
      ( associative-composition-operation-Precategoryᵉ)

  comp-hom-Precategory'ᵉ :
    {xᵉ yᵉ zᵉ : obj-Precategoryᵉ} →
    hom-Precategoryᵉ xᵉ yᵉ →
    hom-Precategoryᵉ yᵉ zᵉ →
    hom-Precategoryᵉ xᵉ zᵉ
  comp-hom-Precategory'ᵉ fᵉ gᵉ = comp-hom-Precategoryᵉ gᵉ fᵉ

  involutive-eq-associative-comp-hom-Precategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Precategoryᵉ}
    (hᵉ : hom-Precategoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Precategoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Precategoryᵉ xᵉ yᵉ) →
    ( comp-hom-Precategoryᵉ (comp-hom-Precategoryᵉ hᵉ gᵉ) fᵉ) ＝ⁱᵉ
    ( comp-hom-Precategoryᵉ hᵉ (comp-hom-Precategoryᵉ gᵉ fᵉ))
  involutive-eq-associative-comp-hom-Precategoryᵉ =
    involutive-eq-associative-composition-operation-binary-family-Setᵉ
      ( hom-set-Precategoryᵉ)
      ( associative-composition-operation-Precategoryᵉ)

  associative-comp-hom-Precategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Precategoryᵉ}
    (hᵉ : hom-Precategoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Precategoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Precategoryᵉ xᵉ yᵉ) →
    ( comp-hom-Precategoryᵉ (comp-hom-Precategoryᵉ hᵉ gᵉ) fᵉ) ＝ᵉ
    ( comp-hom-Precategoryᵉ hᵉ (comp-hom-Precategoryᵉ gᵉ fᵉ))
  associative-comp-hom-Precategoryᵉ =
    witness-associative-composition-operation-binary-family-Setᵉ
      ( hom-set-Precategoryᵉ)
      ( associative-composition-operation-Precategoryᵉ)

  is-unital-composition-operation-Precategoryᵉ :
    is-unital-composition-operation-binary-family-Setᵉ
      ( hom-set-Precategoryᵉ)
      ( comp-hom-Precategoryᵉ)
  is-unital-composition-operation-Precategoryᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ Cᵉ))

  id-hom-Precategoryᵉ : {xᵉ : obj-Precategoryᵉ} → hom-Precategoryᵉ xᵉ xᵉ
  id-hom-Precategoryᵉ {xᵉ} = pr1ᵉ is-unital-composition-operation-Precategoryᵉ xᵉ

  left-unit-law-comp-hom-Precategoryᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ} (fᵉ : hom-Precategoryᵉ xᵉ yᵉ) →
    comp-hom-Precategoryᵉ id-hom-Precategoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Precategoryᵉ =
    pr1ᵉ (pr2ᵉ is-unital-composition-operation-Precategoryᵉ)

  right-unit-law-comp-hom-Precategoryᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ} (fᵉ : hom-Precategoryᵉ xᵉ yᵉ) →
    comp-hom-Precategoryᵉ fᵉ id-hom-Precategoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-hom-Precategoryᵉ =
    pr2ᵉ (pr2ᵉ is-unital-composition-operation-Precategoryᵉ)
```

### The underlying nonunital precategory of a precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  nonunital-precategory-Precategoryᵉ : Nonunital-Precategoryᵉ l1ᵉ l2ᵉ
  pr1ᵉ nonunital-precategory-Precategoryᵉ = obj-Precategoryᵉ Cᵉ
  pr1ᵉ (pr2ᵉ nonunital-precategory-Precategoryᵉ) = hom-set-Precategoryᵉ Cᵉ
  pr2ᵉ (pr2ᵉ nonunital-precategory-Precategoryᵉ) =
    associative-composition-operation-Precategoryᵉ Cᵉ
```

### The underlying set-magmoid of a precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  set-magmoid-Precategoryᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ
  set-magmoid-Precategoryᵉ =
    set-magmoid-Nonunital-Precategoryᵉ (nonunital-precategory-Precategoryᵉ Cᵉ)
```

### The total hom-type of a precategory

```agda
total-hom-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
total-hom-Precategoryᵉ Cᵉ =
  total-hom-Nonunital-Precategoryᵉ (nonunital-precategory-Precategoryᵉ Cᵉ)

obj-total-hom-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) →
  total-hom-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Cᵉ ×ᵉ obj-Precategoryᵉ Cᵉ
obj-total-hom-Precategoryᵉ Cᵉ =
  obj-total-hom-Nonunital-Precategoryᵉ (nonunital-precategory-Precategoryᵉ Cᵉ)
```

### Equalities induce morphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  hom-eq-Precategoryᵉ :
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) → xᵉ ＝ᵉ yᵉ → hom-Precategoryᵉ Cᵉ xᵉ yᵉ
  hom-eq-Precategoryᵉ xᵉ .xᵉ reflᵉ = id-hom-Precategoryᵉ Cᵉ

  hom-inv-eq-Precategoryᵉ :
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) → xᵉ ＝ᵉ yᵉ → hom-Precategoryᵉ Cᵉ yᵉ xᵉ
  hom-inv-eq-Precategoryᵉ xᵉ yᵉ = hom-eq-Precategoryᵉ yᵉ xᵉ ∘ᵉ invᵉ
```

### Pre- and postcomposition by a morphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ)
  (zᵉ : obj-Precategoryᵉ Cᵉ)
  where

  precomp-hom-Precategoryᵉ : hom-Precategoryᵉ Cᵉ yᵉ zᵉ → hom-Precategoryᵉ Cᵉ xᵉ zᵉ
  precomp-hom-Precategoryᵉ gᵉ = comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ

  postcomp-hom-Precategoryᵉ : hom-Precategoryᵉ Cᵉ zᵉ xᵉ → hom-Precategoryᵉ Cᵉ zᵉ yᵉ
  postcomp-hom-Precategoryᵉ = comp-hom-Precategoryᵉ Cᵉ fᵉ
```

## Properties

### If the objects of a precategory are `k`-truncated for nonnegative `k`, the total hom-type is `k`-truncated

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-trunc-total-hom-is-trunc-obj-Precategoryᵉ :
    is-truncᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) (obj-Precategoryᵉ Cᵉ) →
    is-truncᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) (total-hom-Precategoryᵉ Cᵉ)
  is-trunc-total-hom-is-trunc-obj-Precategoryᵉ =
    is-trunc-total-hom-is-trunc-obj-Nonunital-Precategoryᵉ
      ( nonunital-precategory-Precategoryᵉ Cᵉ)

  total-hom-truncated-type-is-trunc-obj-Precategoryᵉ :
    is-truncᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) (obj-Precategoryᵉ Cᵉ) →
    Truncated-Typeᵉ (l1ᵉ ⊔ l2ᵉ) (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ))
  total-hom-truncated-type-is-trunc-obj-Precategoryᵉ =
    total-hom-truncated-type-is-trunc-obj-Nonunital-Precategoryᵉ
      ( nonunital-precategory-Precategoryᵉ Cᵉ)
```

## See also

-ᵉ [Categories](category-theory.categories.mdᵉ) areᵉ univalentᵉ precategories.ᵉ
-ᵉ [Functorsᵉ betweenᵉ precategories](category-theory.functors-precategories.mdᵉ)
  areᵉ [structure](foundation.structure.md)-preservingᵉ mapsᵉ ofᵉ precategories.ᵉ
-ᵉ [Largeᵉ precategories](category-theory.large-precategories.mdᵉ) areᵉ
  precategoriesᵉ whoseᵉ collectionsᵉ ofᵉ objectsᵉ andᵉ morphismsᵉ formᵉ largeᵉ types.ᵉ

## External links

-ᵉ [Precategories](https://1lab.dev/Cat.Base.htmlᵉ) atᵉ 1labᵉ
-ᵉ [precategory](https://ncatlab.org/nlab/show/precategoryᵉ) atᵉ $n$Labᵉ