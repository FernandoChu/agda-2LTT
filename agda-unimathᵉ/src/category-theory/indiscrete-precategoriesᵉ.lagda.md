# Indiscrete precategories

```agda
module category-theory.indiscrete-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.pregroupoidsᵉ
open import category-theory.preunivalent-categoriesᵉ
open import category-theory.strict-categoriesᵉ
open import category-theory.subterminal-precategoriesᵉ

open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ typeᵉ `X`,ᵉ weᵉ canᵉ defineᵉ itsᵉ associatedᵉ **indiscreteᵉ precategory**ᵉ asᵉ theᵉ
[precategory](category-theory.precategories.mdᵉ) whoseᵉ
hom-[sets](foundation-core.sets.mdᵉ) areᵉ
[contractible](foundation-core.contractible-types.mdᵉ) everywhere.ᵉ

Thisᵉ constructionᵉ demonstratesᵉ oneᵉ essentialᵉ aspectᵉ aboutᵉ precategoriesᵉ: Whileᵉ
itᵉ displaysᵉ `obj-Precategory`ᵉ asᵉ aᵉ [retraction](foundation-core.retractions.md),ᵉ
everyᵉ indiscreteᵉ precategoryᵉ isᵉ
[subterminal](category-theory.subterminal-precategories.md).ᵉ

## Definitions

### The indiscrete precategory associated to a type

#### The objects and hom-sets of the indiscrete precategory associated to a type

```agda
module _
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ)
  where

  obj-indiscrete-Precategoryᵉ : UUᵉ lᵉ
  obj-indiscrete-Precategoryᵉ = Xᵉ

  hom-set-indiscrete-Precategoryᵉ :
    obj-indiscrete-Precategoryᵉ → obj-indiscrete-Precategoryᵉ → Setᵉ lzero
  hom-set-indiscrete-Precategoryᵉ _ _ = unit-Setᵉ

  hom-indiscrete-Precategoryᵉ :
    obj-indiscrete-Precategoryᵉ → obj-indiscrete-Precategoryᵉ → UUᵉ lzero
  hom-indiscrete-Precategoryᵉ xᵉ yᵉ = type-Setᵉ (hom-set-indiscrete-Precategoryᵉ xᵉ yᵉ)
```

#### The precategory structure of the indiscrete precategory associated to a type

```agda
module _
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ)
  where

  comp-hom-indiscrete-Precategoryᵉ :
    {xᵉ yᵉ zᵉ : obj-indiscrete-Precategoryᵉ Xᵉ} →
    hom-indiscrete-Precategoryᵉ Xᵉ yᵉ zᵉ →
    hom-indiscrete-Precategoryᵉ Xᵉ xᵉ yᵉ →
    hom-indiscrete-Precategoryᵉ Xᵉ xᵉ zᵉ
  comp-hom-indiscrete-Precategoryᵉ _ _ = starᵉ

  associative-comp-hom-indiscrete-Precategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-indiscrete-Precategoryᵉ Xᵉ} →
    (hᵉ : hom-indiscrete-Precategoryᵉ Xᵉ zᵉ wᵉ)
    (gᵉ : hom-indiscrete-Precategoryᵉ Xᵉ yᵉ zᵉ)
    (fᵉ : hom-indiscrete-Precategoryᵉ Xᵉ xᵉ yᵉ) →
    comp-hom-indiscrete-Precategoryᵉ {xᵉ} {yᵉ} {wᵉ}
      ( comp-hom-indiscrete-Precategoryᵉ {yᵉ} {zᵉ} {wᵉ} hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-hom-indiscrete-Precategoryᵉ {xᵉ} {zᵉ} {wᵉ}
      ( hᵉ)
      ( comp-hom-indiscrete-Precategoryᵉ {xᵉ} {yᵉ} {zᵉ} gᵉ fᵉ)
  associative-comp-hom-indiscrete-Precategoryᵉ hᵉ gᵉ fᵉ = reflᵉ

  id-hom-indiscrete-Precategoryᵉ :
    {xᵉ : obj-indiscrete-Precategoryᵉ Xᵉ} → hom-indiscrete-Precategoryᵉ Xᵉ xᵉ xᵉ
  id-hom-indiscrete-Precategoryᵉ = starᵉ

  left-unit-law-comp-hom-indiscrete-Precategoryᵉ :
    {xᵉ yᵉ : obj-indiscrete-Precategoryᵉ Xᵉ} →
    (fᵉ : hom-indiscrete-Precategoryᵉ Xᵉ xᵉ yᵉ) →
    comp-hom-indiscrete-Precategoryᵉ {xᵉ} {yᵉ} {yᵉ}
      ( id-hom-indiscrete-Precategoryᵉ {yᵉ})
      ( fᵉ) ＝ᵉ
    fᵉ
  left-unit-law-comp-hom-indiscrete-Precategoryᵉ fᵉ = reflᵉ

  right-unit-law-comp-hom-indiscrete-Precategoryᵉ :
    {xᵉ yᵉ : obj-indiscrete-Precategoryᵉ Xᵉ} →
    (fᵉ : hom-indiscrete-Precategoryᵉ Xᵉ xᵉ yᵉ) →
    comp-hom-indiscrete-Precategoryᵉ {xᵉ} {xᵉ} {yᵉ}
      ( fᵉ)
      ( id-hom-indiscrete-Precategoryᵉ {xᵉ}) ＝ᵉ
    fᵉ
  right-unit-law-comp-hom-indiscrete-Precategoryᵉ fᵉ = reflᵉ

  indiscrete-Precategoryᵉ : Precategoryᵉ lᵉ lzero
  indiscrete-Precategoryᵉ =
    make-Precategoryᵉ
      ( obj-indiscrete-Precategoryᵉ Xᵉ)
      ( hom-set-indiscrete-Precategoryᵉ Xᵉ)
      ( λ {xᵉ} {yᵉ} {zᵉ} → comp-hom-indiscrete-Precategoryᵉ {xᵉ} {yᵉ} {zᵉ})
      ( λ xᵉ → id-hom-indiscrete-Precategoryᵉ {xᵉ})
      ( λ {xᵉ} {yᵉ} {zᵉ} {wᵉ} →
        associative-comp-hom-indiscrete-Precategoryᵉ {xᵉ} {yᵉ} {zᵉ} {wᵉ})
      ( λ {xᵉ} {yᵉ} → left-unit-law-comp-hom-indiscrete-Precategoryᵉ {xᵉ} {yᵉ})
      ( λ {xᵉ} {yᵉ} → right-unit-law-comp-hom-indiscrete-Precategoryᵉ {xᵉ} {yᵉ})
```

#### The pregroupoid structure of the indiscrete precategory associated to a type

```agda
module _
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ)
  where

  is-iso-hom-indiscrete-Precategoryᵉ :
    {xᵉ yᵉ : obj-indiscrete-Precategoryᵉ Xᵉ}
    (fᵉ : hom-indiscrete-Precategoryᵉ Xᵉ xᵉ yᵉ) →
    is-iso-Precategoryᵉ (indiscrete-Precategoryᵉ Xᵉ) {xᵉ} {yᵉ} fᵉ
  pr1ᵉ (is-iso-hom-indiscrete-Precategoryᵉ _) = starᵉ
  pr1ᵉ (pr2ᵉ (is-iso-hom-indiscrete-Precategoryᵉ _)) = reflᵉ
  pr2ᵉ (pr2ᵉ (is-iso-hom-indiscrete-Precategoryᵉ _)) = reflᵉ

  iso-obj-indiscrete-Precategoryᵉ :
    (xᵉ yᵉ : obj-indiscrete-Precategoryᵉ Xᵉ) →
    iso-Precategoryᵉ (indiscrete-Precategoryᵉ Xᵉ) xᵉ yᵉ
  pr1ᵉ (iso-obj-indiscrete-Precategoryᵉ xᵉ yᵉ) = starᵉ
  pr2ᵉ (iso-obj-indiscrete-Precategoryᵉ xᵉ yᵉ) =
    is-iso-hom-indiscrete-Precategoryᵉ {xᵉ} {yᵉ} starᵉ

  is-pregroupoid-indiscrete-Precategoryᵉ :
    is-pregroupoid-Precategoryᵉ (indiscrete-Precategoryᵉ Xᵉ)
  is-pregroupoid-indiscrete-Precategoryᵉ xᵉ yᵉ =
    is-iso-hom-indiscrete-Precategoryᵉ {xᵉ} {yᵉ}

  indiscrete-Pregroupoidᵉ : Pregroupoidᵉ lᵉ lzero
  pr1ᵉ indiscrete-Pregroupoidᵉ = indiscrete-Precategoryᵉ Xᵉ
  pr2ᵉ indiscrete-Pregroupoidᵉ = is-pregroupoid-indiscrete-Precategoryᵉ
```

### The predicate on a precategory of being indiscrete

Forᵉ completeness,ᵉ weᵉ alsoᵉ record theᵉ predicateᵉ onᵉ aᵉ precategoryᵉ ofᵉ beingᵉ
indiscrete.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-indiscrete-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-indiscrete-Precategoryᵉ =
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) → is-contrᵉ (hom-Precategoryᵉ Cᵉ xᵉ yᵉ)

  is-prop-is-indiscrete-Precategoryᵉ : is-propᵉ is-indiscrete-Precategoryᵉ
  is-prop-is-indiscrete-Precategoryᵉ =
    is-prop-iterated-Πᵉ 2 (λ xᵉ yᵉ → is-property-is-contrᵉ)

  is-indiscrete-prop-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ is-indiscrete-prop-Precategoryᵉ = is-indiscrete-Precategoryᵉ
  pr2ᵉ is-indiscrete-prop-Precategoryᵉ = is-prop-is-indiscrete-Precategoryᵉ
```

#### The indiscrete precategory associated to a type is indiscrete

```agda
module _
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ)
  where

  is-indiscrete-indiscrete-Precategoryᵉ :
    is-indiscrete-Precategoryᵉ (indiscrete-Precategoryᵉ Xᵉ)
  is-indiscrete-indiscrete-Precategoryᵉ xᵉ yᵉ = is-contr-unitᵉ
```

## Properties

### If an indiscrete precategory is preunivalent then it is a strict category

**Proof:**ᵉ Ifᵉ anᵉ indiscreteᵉ precategoryᵉ isᵉ preunivalent,ᵉ thatᵉ meansᵉ everyᵉ
identityᵉ typeᵉ ofᵉ theᵉ objectsᵉ embedsᵉ intoᵉ theᵉ unitᵉ type,ᵉ henceᵉ theᵉ objectsᵉ formᵉ aᵉ
set.ᵉ

```agda
module _
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ)
  where

  is-strict-category-is-preunivalent-indiscrete-Precategoryᵉ :
    is-preunivalent-Precategoryᵉ (indiscrete-Precategoryᵉ Xᵉ) →
    is-strict-category-Precategoryᵉ (indiscrete-Precategoryᵉ Xᵉ)
  is-strict-category-is-preunivalent-indiscrete-Precategoryᵉ Hᵉ xᵉ yᵉ =
    is-prop-is-embᵉ
      ( iso-eq-Precategoryᵉ (indiscrete-Precategoryᵉ Xᵉ) xᵉ yᵉ)
      ( Hᵉ xᵉ yᵉ)
      ( is-prop-Σᵉ
        ( is-prop-unitᵉ)
        ( is-prop-is-iso-Precategoryᵉ (indiscrete-Precategoryᵉ Xᵉ) {xᵉ} {yᵉ}))
```

### The construction of `indiscrete-Precategory` is a section of `obj-Precategory`

```agda
is-section-indiscrete-Precategoryᵉ :
  {lᵉ : Level} → obj-Precategoryᵉ ∘ᵉ indiscrete-Precategoryᵉ {lᵉ} ~ᵉ idᵉ
is-section-indiscrete-Precategoryᵉ Xᵉ = reflᵉ
```

### Indiscrete precategories are subterminal

```agda
module _
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ)
  where

  is-subterminal-indiscrete-Precategoryᵉ :
    is-subterminal-Precategoryᵉ (indiscrete-Precategoryᵉ Xᵉ)
  is-subterminal-indiscrete-Precategoryᵉ xᵉ yᵉ = is-equiv-idᵉ
```

## External links

-ᵉ [indiscreteᵉ category](https://ncatlab.org/nlab/show/indiscrete+categoryᵉ) atᵉ
  $n$Labᵉ
-ᵉ [Indiscreteᵉ category](https://en.wikipedia.org/wiki/Indiscrete_categoryᵉ) atᵉ
  Wikipediaᵉ

Aᵉ wikidataᵉ identifierᵉ wasᵉ notᵉ availableᵉ forᵉ thisᵉ concept.ᵉ