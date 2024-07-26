# Set-magmoids

```agda
module category-theory.set-magmoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-setsᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **set-magmoid**ᵉ isᵉ theᵉ [structure](foundation.structure.mdᵉ) ofᵉ aᵉ
[compositionᵉ operationᵉ onᵉ aᵉ binaryᵉ familyᵉ ofᵉ sets](category-theory.composition-operations-on-binary-families-of-sets.md),ᵉ
andᵉ areᵉ in oneᵉ senseᵉ theᵉ "oidification"ᵉ ofᵉ [magmas](structured-types.magmas.mdᵉ)
in [sets](foundation-core.sets.md).ᵉ Weᵉ callᵉ elementsᵉ ofᵉ theᵉ indexingᵉ typeᵉ
**objects**,ᵉ andᵉ elementsᵉ ofᵉ theᵉ set-familyᵉ **morphisms**ᵉ orᵉ **homomorphisms**.ᵉ

Theseᵉ objectsᵉ serveᵉ asᵉ ourᵉ startingᵉ pointᵉ in theᵉ studyᵉ ofᵉ theᵉ
[stucture](foundation.structure.mdᵉ) ofᵉ
[categories](category-theory.categories.md).ᵉ Indeed,ᵉ categoriesᵉ formᵉ aᵉ
[subtype](foundation-core.subtypes.mdᵉ) ofᵉ set-magmoids,ᵉ althoughᵉ
structure-preservingᵉ mapsᵉ ofᵉ set-magmoidsᵉ do notᵉ automaticallyᵉ preserveᵉ
identity-morphisms.ᵉ

Set-magmoidsᵉ areᵉ commonlyᵉ referredᵉ to asᵉ _magmoidsᵉ_ in theᵉ literature,ᵉ butᵉ weᵉ
useᵉ theᵉ "set-"ᵉ prefixᵉ to makeᵉ clearᵉ itsᵉ relationᵉ to magmas.ᵉ Set-magmoidsᵉ shouldᵉ
notᵉ beᵉ confusedᵉ with _strictᵉ_ magmoids,ᵉ whichᵉ wouldᵉ beᵉ set-magmoidsᵉ whoseᵉ
objectsᵉ formᵉ aᵉ set.ᵉ

## Definitions

### The type of set-magmoids

```agda
Set-Magmoidᵉ :
  (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Set-Magmoidᵉ l1ᵉ l2ᵉ =
  Σᵉ ( UUᵉ l1ᵉ)
    ( λ Aᵉ →
      Σᵉ ( Aᵉ → Aᵉ → Setᵉ l2ᵉ)
        ( composition-operation-binary-family-Setᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ)
  where

  obj-Set-Magmoidᵉ : UUᵉ l1ᵉ
  obj-Set-Magmoidᵉ = pr1ᵉ Mᵉ

  hom-set-Set-Magmoidᵉ : (xᵉ yᵉ : obj-Set-Magmoidᵉ) → Setᵉ l2ᵉ
  hom-set-Set-Magmoidᵉ = pr1ᵉ (pr2ᵉ Mᵉ)

  hom-Set-Magmoidᵉ : (xᵉ yᵉ : obj-Set-Magmoidᵉ) → UUᵉ l2ᵉ
  hom-Set-Magmoidᵉ xᵉ yᵉ = type-Setᵉ (hom-set-Set-Magmoidᵉ xᵉ yᵉ)

  is-set-hom-Set-Magmoidᵉ :
    (xᵉ yᵉ : obj-Set-Magmoidᵉ) → is-setᵉ (hom-Set-Magmoidᵉ xᵉ yᵉ)
  is-set-hom-Set-Magmoidᵉ xᵉ yᵉ =
    is-set-type-Setᵉ (hom-set-Set-Magmoidᵉ xᵉ yᵉ)

  comp-hom-Set-Magmoidᵉ :
    {xᵉ yᵉ zᵉ : obj-Set-Magmoidᵉ} →
    hom-Set-Magmoidᵉ yᵉ zᵉ →
    hom-Set-Magmoidᵉ xᵉ yᵉ →
    hom-Set-Magmoidᵉ xᵉ zᵉ
  comp-hom-Set-Magmoidᵉ = pr2ᵉ (pr2ᵉ Mᵉ)

  comp-hom-Set-Magmoid'ᵉ :
    {xᵉ yᵉ zᵉ : obj-Set-Magmoidᵉ} →
    hom-Set-Magmoidᵉ xᵉ yᵉ →
    hom-Set-Magmoidᵉ yᵉ zᵉ →
    hom-Set-Magmoidᵉ xᵉ zᵉ
  comp-hom-Set-Magmoid'ᵉ fᵉ gᵉ = comp-hom-Set-Magmoidᵉ gᵉ fᵉ
```

### The total hom-type of a set-magmoid

```agda
total-hom-Set-Magmoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
total-hom-Set-Magmoidᵉ Mᵉ =
  Σᵉ ( obj-Set-Magmoidᵉ Mᵉ)
    ( λ xᵉ → Σᵉ (obj-Set-Magmoidᵉ Mᵉ) (hom-Set-Magmoidᵉ Mᵉ xᵉ))

obj-total-hom-Set-Magmoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ) →
  total-hom-Set-Magmoidᵉ Mᵉ → obj-Set-Magmoidᵉ Mᵉ ×ᵉ obj-Set-Magmoidᵉ Mᵉ
pr1ᵉ (obj-total-hom-Set-Magmoidᵉ Mᵉ (xᵉ ,ᵉ yᵉ ,ᵉ fᵉ)) = xᵉ
pr2ᵉ (obj-total-hom-Set-Magmoidᵉ Mᵉ (xᵉ ,ᵉ yᵉ ,ᵉ fᵉ)) = yᵉ
```

### Pre- and postcomposition by a morphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Set-Magmoidᵉ Mᵉ}
  (fᵉ : hom-Set-Magmoidᵉ Mᵉ xᵉ yᵉ)
  (zᵉ : obj-Set-Magmoidᵉ Mᵉ)
  where

  precomp-hom-Set-Magmoidᵉ : hom-Set-Magmoidᵉ Mᵉ yᵉ zᵉ → hom-Set-Magmoidᵉ Mᵉ xᵉ zᵉ
  precomp-hom-Set-Magmoidᵉ gᵉ = comp-hom-Set-Magmoidᵉ Mᵉ gᵉ fᵉ

  postcomp-hom-Set-Magmoidᵉ : hom-Set-Magmoidᵉ Mᵉ zᵉ xᵉ → hom-Set-Magmoidᵉ Mᵉ zᵉ yᵉ
  postcomp-hom-Set-Magmoidᵉ = comp-hom-Set-Magmoidᵉ Mᵉ fᵉ
```

### The predicate on set-magmoids of being associative

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ)
  where

  is-associative-Set-Magmoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-associative-Set-Magmoidᵉ =
    is-associative-composition-operation-binary-family-Setᵉ
      ( hom-set-Set-Magmoidᵉ Mᵉ)
      ( comp-hom-Set-Magmoidᵉ Mᵉ)

  is-prop-is-associative-Set-Magmoidᵉ :
    is-propᵉ
      ( is-associative-composition-operation-binary-family-Setᵉ
        ( hom-set-Set-Magmoidᵉ Mᵉ)
        ( comp-hom-Set-Magmoidᵉ Mᵉ))
  is-prop-is-associative-Set-Magmoidᵉ =
    is-prop-is-associative-composition-operation-binary-family-Setᵉ
      ( hom-set-Set-Magmoidᵉ Mᵉ)
      ( comp-hom-Set-Magmoidᵉ Mᵉ)

  is-associative-prop-Set-Magmoidᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-associative-prop-Set-Magmoidᵉ =
    is-associative-prop-composition-operation-binary-family-Setᵉ
      ( hom-set-Set-Magmoidᵉ Mᵉ)
      ( comp-hom-Set-Magmoidᵉ Mᵉ)
```

### The predicate on set-magmoids of being unital

**Proof:**ᵉ Toᵉ showᵉ thatᵉ unitalityᵉ isᵉ aᵉ proposition,ᵉ supposeᵉ
`eᵉ e'ᵉ : (xᵉ : Aᵉ) → hom-setᵉ xᵉ x`ᵉ areᵉ bothᵉ rightᵉ andᵉ leftᵉ unitsᵉ with regardᵉ to
composition.ᵉ Itᵉ isᵉ enoughᵉ to showᵉ thatᵉ `eᵉ ＝ᵉ e'`ᵉ sinceᵉ theᵉ rightᵉ andᵉ leftᵉ unitᵉ
lawsᵉ areᵉ propositionsᵉ (becauseᵉ allᵉ hom-typesᵉ areᵉ sets).ᵉ Byᵉ functionᵉ
extensionality,ᵉ itᵉ isᵉ enoughᵉ to showᵉ thatᵉ `eᵉ xᵉ ＝ᵉ e'ᵉ x`ᵉ forᵉ allᵉ `xᵉ : A`.ᵉ Butᵉ byᵉ
theᵉ unitᵉ lawsᵉ weᵉ haveᵉ theᵉ followingᵉ chainᵉ ofᵉ equalitiesᵉ:
`eᵉ xᵉ ＝ᵉ (e'ᵉ xᵉ) ∘ᵉ (eᵉ xᵉ) ＝ᵉ e'ᵉ x.`ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ)
  where

  is-unital-Set-Magmoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-unital-Set-Magmoidᵉ =
    is-unital-composition-operation-binary-family-Setᵉ
      ( hom-set-Set-Magmoidᵉ Mᵉ)
      ( comp-hom-Set-Magmoidᵉ Mᵉ)

  is-prop-is-unital-Set-Magmoidᵉ :
    is-propᵉ
      ( is-unital-composition-operation-binary-family-Setᵉ
        ( hom-set-Set-Magmoidᵉ Mᵉ)
        ( comp-hom-Set-Magmoidᵉ Mᵉ))
  is-prop-is-unital-Set-Magmoidᵉ =
    is-prop-is-unital-composition-operation-binary-family-Setᵉ
      ( hom-set-Set-Magmoidᵉ Mᵉ)
      ( comp-hom-Set-Magmoidᵉ Mᵉ)

  is-unital-prop-Set-Magmoidᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-unital-prop-Set-Magmoidᵉ =
    is-unital-prop-composition-operation-binary-family-Setᵉ
      ( hom-set-Set-Magmoidᵉ Mᵉ)
      ( comp-hom-Set-Magmoidᵉ Mᵉ)
```

## Properties

### If the objects of a set-magmoid are `k`-truncated for nonnegative `k`, the total hom-type is `k`-truncated

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} (Mᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ)
  where

  is-trunc-total-hom-is-trunc-obj-Set-Magmoidᵉ :
    is-truncᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) (obj-Set-Magmoidᵉ Mᵉ) →
    is-truncᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) (total-hom-Set-Magmoidᵉ Mᵉ)
  is-trunc-total-hom-is-trunc-obj-Set-Magmoidᵉ is-trunc-obj-Mᵉ =
    is-trunc-Σᵉ
      ( is-trunc-obj-Mᵉ)
      ( λ xᵉ →
        is-trunc-Σᵉ
          ( is-trunc-obj-Mᵉ)
          ( λ yᵉ → is-trunc-is-setᵉ kᵉ (is-set-hom-Set-Magmoidᵉ Mᵉ xᵉ yᵉ)))

  total-hom-truncated-type-is-trunc-obj-Set-Magmoidᵉ :
    is-truncᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) (obj-Set-Magmoidᵉ Mᵉ) →
    Truncated-Typeᵉ (l1ᵉ ⊔ l2ᵉ) (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ))
  pr1ᵉ (total-hom-truncated-type-is-trunc-obj-Set-Magmoidᵉ is-trunc-obj-Mᵉ) =
    total-hom-Set-Magmoidᵉ Mᵉ
  pr2ᵉ (total-hom-truncated-type-is-trunc-obj-Set-Magmoidᵉ is-trunc-obj-Mᵉ) =
    is-trunc-total-hom-is-trunc-obj-Set-Magmoidᵉ is-trunc-obj-Mᵉ
```

## See also

-ᵉ [Nonunitalᵉ precategories](category-theory.nonunital-precategories.mdᵉ) areᵉ
  associativeᵉ set-magmoids.ᵉ
-ᵉ [Precategories](category-theory.precategories.mdᵉ) areᵉ associativeᵉ andᵉ unitalᵉ
  set-magmoids.ᵉ
-ᵉ [Categories](category-theory.categories.mdᵉ) areᵉ univalent,ᵉ associativeᵉ andᵉ
  unitalᵉ set-magmoids.ᵉ
-ᵉ [Strictᵉ categories](category-theory.categories.mdᵉ) areᵉ associativeᵉ andᵉ unitalᵉ
  set-magmoidsᵉ whoseᵉ objectsᵉ formᵉ aᵉ set.ᵉ

## External links

-ᵉ [magmoid](https://ncatlab.org/nlab/show/magmoidᵉ) atᵉ $n$Labᵉ

Aᵉ wikidataᵉ identifierᵉ wasᵉ notᵉ availableᵉ forᵉ thisᵉ concept.ᵉ