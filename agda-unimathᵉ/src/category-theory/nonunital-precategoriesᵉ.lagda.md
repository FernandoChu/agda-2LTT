# Nonunital precategories

```agda
module category-theory.nonunital-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.set-magmoidsᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
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

Aᵉ {{#conceptᵉ "nonunitalᵉ precategory"ᵉ Agda=Nonunital-Precategoryᵉ}} isᵉ aᵉ
[precategory](category-theory.precategories.mdᵉ) thatᵉ mayᵉ notᵉ haveᵉ identityᵉ
morphisms.ᵉ Inᵉ otherᵉ words,ᵉ itᵉ isᵉ anᵉ associativeᵉ
[compositionᵉ operationᵉ onᵉ binaryᵉ familiesᵉ ofᵉ sets](category-theory.composition-operations-on-binary-families-of-sets.md).ᵉ
Suchᵉ aᵉ structureᵉ mayᵉ alsoᵉ beᵉ referredᵉ to asᵉ aᵉ _semiprecategory_.ᵉ

Perhapsᵉ surprisingly,ᵉ thereᵉ isᵉ [atᵉ mostᵉ one](foundation.subterminal-types.mdᵉ)
wayᵉ to equipᵉ nonunitalᵉ precategoriesᵉ with identityᵉ morphisms,ᵉ soᵉ precategoriesᵉ
formᵉ aᵉ [subtype](foundation-core.subtypes.mdᵉ) ofᵉ nonunitalᵉ precategories.ᵉ

## Definition

### The type of nonunital precategories

```agda
Nonunital-Precategoryᵉ :
  (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Nonunital-Precategoryᵉ l1ᵉ l2ᵉ =
  Σᵉ ( UUᵉ l1ᵉ)
    ( λ Aᵉ →
      Σᵉ ( Aᵉ → Aᵉ → Setᵉ l2ᵉ)
        ( associative-composition-operation-binary-family-Setᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Nonunital-Precategoryᵉ l1ᵉ l2ᵉ)
  where

  obj-Nonunital-Precategoryᵉ : UUᵉ l1ᵉ
  obj-Nonunital-Precategoryᵉ = pr1ᵉ Cᵉ

  hom-set-Nonunital-Precategoryᵉ : (xᵉ yᵉ : obj-Nonunital-Precategoryᵉ) → Setᵉ l2ᵉ
  hom-set-Nonunital-Precategoryᵉ = pr1ᵉ (pr2ᵉ Cᵉ)

  hom-Nonunital-Precategoryᵉ : (xᵉ yᵉ : obj-Nonunital-Precategoryᵉ) → UUᵉ l2ᵉ
  hom-Nonunital-Precategoryᵉ xᵉ yᵉ = type-Setᵉ (hom-set-Nonunital-Precategoryᵉ xᵉ yᵉ)

  is-set-hom-Nonunital-Precategoryᵉ :
    (xᵉ yᵉ : obj-Nonunital-Precategoryᵉ) → is-setᵉ (hom-Nonunital-Precategoryᵉ xᵉ yᵉ)
  is-set-hom-Nonunital-Precategoryᵉ xᵉ yᵉ =
    is-set-type-Setᵉ (hom-set-Nonunital-Precategoryᵉ xᵉ yᵉ)

  associative-composition-operation-Nonunital-Precategoryᵉ :
    associative-composition-operation-binary-family-Setᵉ
      hom-set-Nonunital-Precategoryᵉ
  associative-composition-operation-Nonunital-Precategoryᵉ = pr2ᵉ (pr2ᵉ Cᵉ)

  comp-hom-Nonunital-Precategoryᵉ :
    {xᵉ yᵉ zᵉ : obj-Nonunital-Precategoryᵉ} →
    hom-Nonunital-Precategoryᵉ yᵉ zᵉ →
    hom-Nonunital-Precategoryᵉ xᵉ yᵉ →
    hom-Nonunital-Precategoryᵉ xᵉ zᵉ
  comp-hom-Nonunital-Precategoryᵉ =
    comp-hom-associative-composition-operation-binary-family-Setᵉ
      ( hom-set-Nonunital-Precategoryᵉ)
      ( associative-composition-operation-Nonunital-Precategoryᵉ)

  comp-hom-Nonunital-Precategory'ᵉ :
    {xᵉ yᵉ zᵉ : obj-Nonunital-Precategoryᵉ} →
    hom-Nonunital-Precategoryᵉ xᵉ yᵉ →
    hom-Nonunital-Precategoryᵉ yᵉ zᵉ →
    hom-Nonunital-Precategoryᵉ xᵉ zᵉ
  comp-hom-Nonunital-Precategory'ᵉ fᵉ gᵉ = comp-hom-Nonunital-Precategoryᵉ gᵉ fᵉ

  associative-comp-hom-Nonunital-Precategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Nonunital-Precategoryᵉ}
    (hᵉ : hom-Nonunital-Precategoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Nonunital-Precategoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Nonunital-Precategoryᵉ xᵉ yᵉ) →
    comp-hom-Nonunital-Precategoryᵉ (comp-hom-Nonunital-Precategoryᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Nonunital-Precategoryᵉ hᵉ (comp-hom-Nonunital-Precategoryᵉ gᵉ fᵉ)
  associative-comp-hom-Nonunital-Precategoryᵉ =
    witness-associative-composition-operation-binary-family-Setᵉ
      ( hom-set-Nonunital-Precategoryᵉ)
      ( associative-composition-operation-Nonunital-Precategoryᵉ)

  involutive-eq-associative-comp-hom-Nonunital-Precategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Nonunital-Precategoryᵉ}
    (hᵉ : hom-Nonunital-Precategoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Nonunital-Precategoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Nonunital-Precategoryᵉ xᵉ yᵉ) →
    comp-hom-Nonunital-Precategoryᵉ (comp-hom-Nonunital-Precategoryᵉ hᵉ gᵉ) fᵉ ＝ⁱᵉ
    comp-hom-Nonunital-Precategoryᵉ hᵉ (comp-hom-Nonunital-Precategoryᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Nonunital-Precategoryᵉ =
    involutive-eq-associative-composition-operation-binary-family-Setᵉ
      ( hom-set-Nonunital-Precategoryᵉ)
      ( associative-composition-operation-Nonunital-Precategoryᵉ)
```

### The underlying set-magmoid of a nonunital precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Nonunital-Precategoryᵉ l1ᵉ l2ᵉ)
  where

  set-magmoid-Nonunital-Precategoryᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ
  pr1ᵉ set-magmoid-Nonunital-Precategoryᵉ = obj-Nonunital-Precategoryᵉ Cᵉ
  pr1ᵉ (pr2ᵉ set-magmoid-Nonunital-Precategoryᵉ) = hom-set-Nonunital-Precategoryᵉ Cᵉ
  pr2ᵉ (pr2ᵉ set-magmoid-Nonunital-Precategoryᵉ) = comp-hom-Nonunital-Precategoryᵉ Cᵉ
```

### The total hom-type of a nonunital precategory

```agda
total-hom-Nonunital-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Nonunital-Precategoryᵉ l1ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
total-hom-Nonunital-Precategoryᵉ Cᵉ =
  Σᵉ ( obj-Nonunital-Precategoryᵉ Cᵉ)
    ( λ xᵉ → Σᵉ (obj-Nonunital-Precategoryᵉ Cᵉ) (hom-Nonunital-Precategoryᵉ Cᵉ xᵉ))

obj-total-hom-Nonunital-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Nonunital-Precategoryᵉ l1ᵉ l2ᵉ) →
  total-hom-Nonunital-Precategoryᵉ Cᵉ →
  obj-Nonunital-Precategoryᵉ Cᵉ ×ᵉ obj-Nonunital-Precategoryᵉ Cᵉ
pr1ᵉ (obj-total-hom-Nonunital-Precategoryᵉ Cᵉ (xᵉ ,ᵉ yᵉ ,ᵉ fᵉ)) = xᵉ
pr2ᵉ (obj-total-hom-Nonunital-Precategoryᵉ Cᵉ (xᵉ ,ᵉ yᵉ ,ᵉ fᵉ)) = yᵉ
```

### Pre- and postcomposition by a morphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Nonunital-Precategoryᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ : obj-Nonunital-Precategoryᵉ Cᵉ}
  (fᵉ : hom-Nonunital-Precategoryᵉ Cᵉ xᵉ yᵉ)
  (zᵉ : obj-Nonunital-Precategoryᵉ Cᵉ)
  where

  precomp-hom-Nonunital-Precategoryᵉ :
    hom-Nonunital-Precategoryᵉ Cᵉ yᵉ zᵉ → hom-Nonunital-Precategoryᵉ Cᵉ xᵉ zᵉ
  precomp-hom-Nonunital-Precategoryᵉ gᵉ = comp-hom-Nonunital-Precategoryᵉ Cᵉ gᵉ fᵉ

  postcomp-hom-Nonunital-Precategoryᵉ :
    hom-Nonunital-Precategoryᵉ Cᵉ zᵉ xᵉ → hom-Nonunital-Precategoryᵉ Cᵉ zᵉ yᵉ
  postcomp-hom-Nonunital-Precategoryᵉ = comp-hom-Nonunital-Precategoryᵉ Cᵉ fᵉ
```

### The predicate on nonunital precategories of being unital

**Proof:**ᵉ Toᵉ showᵉ thatᵉ unitalityᵉ isᵉ aᵉ proposition,ᵉ supposeᵉ
`eᵉ e'ᵉ : (xᵉ : Aᵉ) → hom-setᵉ xᵉ x`ᵉ areᵉ bothᵉ rightᵉ andᵉ leftᵉ unitsᵉ with regardᵉ to
composition.ᵉ Itᵉ isᵉ enoughᵉ to showᵉ thatᵉ `eᵉ ＝ᵉ e'`ᵉ sinceᵉ theᵉ rightᵉ andᵉ leftᵉ unitᵉ
lawsᵉ areᵉ propositionsᵉ (becauseᵉ allᵉ hom-typesᵉ areᵉ sets).ᵉ Byᵉ functionᵉ
extensionality,ᵉ itᵉ isᵉ enoughᵉ to showᵉ thatᵉ `eᵉ xᵉ ＝ᵉ e'ᵉ x`ᵉ forᵉ allᵉ `xᵉ : A`.ᵉ Butᵉ byᵉ
theᵉ unitᵉ lawsᵉ weᵉ haveᵉ theᵉ followingᵉ chainᵉ ofᵉ equalitiesᵉ:
`eᵉ xᵉ ＝ᵉ (e'ᵉ xᵉ) ∘ᵉ (eᵉ xᵉ) ＝ᵉ e'ᵉ x.`ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Nonunital-Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-unital-Nonunital-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-unital-Nonunital-Precategoryᵉ =
    is-unital-composition-operation-binary-family-Setᵉ
      ( hom-set-Nonunital-Precategoryᵉ Cᵉ)
      ( comp-hom-Nonunital-Precategoryᵉ Cᵉ)

  is-prop-is-unital-Nonunital-Precategoryᵉ :
    is-propᵉ
      ( is-unital-composition-operation-binary-family-Setᵉ
        ( hom-set-Nonunital-Precategoryᵉ Cᵉ)
        ( comp-hom-Nonunital-Precategoryᵉ Cᵉ))
  is-prop-is-unital-Nonunital-Precategoryᵉ =
    is-prop-is-unital-composition-operation-binary-family-Setᵉ
      ( hom-set-Nonunital-Precategoryᵉ Cᵉ)
      ( comp-hom-Nonunital-Precategoryᵉ Cᵉ)

  is-unital-prop-Nonunital-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-unital-prop-Nonunital-Precategoryᵉ =
    is-unital-prop-composition-operation-binary-family-Setᵉ
      ( hom-set-Nonunital-Precategoryᵉ Cᵉ)
      ( comp-hom-Nonunital-Precategoryᵉ Cᵉ)
```

## Properties

### If the objects of a nonunital precategory are `k`-truncated for nonnegative `k`, the total hom-type is `k`-truncated

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} (Cᵉ : Nonunital-Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-trunc-total-hom-is-trunc-obj-Nonunital-Precategoryᵉ :
    is-truncᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) (obj-Nonunital-Precategoryᵉ Cᵉ) →
    is-truncᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) (total-hom-Nonunital-Precategoryᵉ Cᵉ)
  is-trunc-total-hom-is-trunc-obj-Nonunital-Precategoryᵉ =
    is-trunc-total-hom-is-trunc-obj-Set-Magmoidᵉ
      ( set-magmoid-Nonunital-Precategoryᵉ Cᵉ)

  total-hom-truncated-type-is-trunc-obj-Nonunital-Precategoryᵉ :
    is-truncᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) (obj-Nonunital-Precategoryᵉ Cᵉ) →
    Truncated-Typeᵉ (l1ᵉ ⊔ l2ᵉ) (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ))
  total-hom-truncated-type-is-trunc-obj-Nonunital-Precategoryᵉ =
    total-hom-truncated-type-is-trunc-obj-Set-Magmoidᵉ
      ( set-magmoid-Nonunital-Precategoryᵉ Cᵉ)
```

## Comments

Asᵉ discussedᵉ in [Semicategories](https://ncatlab.org/nlab/show/semicategoryᵉ) atᵉ
$n$Lab,ᵉ itᵉ seemsᵉ thatᵉ aᵉ nonunitalᵉ precategoryᵉ shouldᵉ beᵉ theᵉ underlyingᵉ nonunitalᵉ
precategoryᵉ ofᵉ aᵉ [category](category-theory.categories.mdᵉ) ifᵉ andᵉ onlyᵉ ifᵉ theᵉ
projectionᵉ mapᵉ

```text
  pr1ᵉ : (Σᵉ (aᵉ : Aᵉ) Σᵉ (fᵉ : homᵉ aᵉ aᵉ) (is-neutralᵉ fᵉ)) → Aᵉ
```

isᵉ anᵉ [equivalence](foundation-core.equivalences.md).ᵉ

Weᵉ canᵉ alsoᵉ defineᵉ oneᵉ notionᵉ ofᵉ "isomorphism"ᵉ asᵉ thoseᵉ morphismsᵉ thatᵉ induceᵉ
equivalencesᵉ ofᵉ hom-[sets](foundation-core.sets.mdᵉ) byᵉ pre-ᵉ andᵉ postcomposition.ᵉ

## External links

-ᵉ [Semicategories](https://ncatlab.org/nlab/show/semicategoryᵉ) atᵉ $n$Labᵉ
-ᵉ [Semigroupoid](https://en.wikipedia.org/wiki/Semigroupoidᵉ) atᵉ Wikipediaᵉ
-ᵉ [semigroupoid](https://www.wikidata.org/wiki/Q4164581ᵉ) atᵉ Wikidataᵉ