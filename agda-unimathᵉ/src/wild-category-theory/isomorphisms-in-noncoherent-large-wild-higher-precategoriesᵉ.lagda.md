# Isomorphisms in noncoherent large wild higher precategories

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module wild-category-theory.isomorphisms-in-noncoherent-large-wild-higher-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import wild-category-theory.isomorphisms-in-noncoherent-wild-higher-precategoriesᵉ
open import wild-category-theory.noncoherent-large-wild-higher-precategoriesᵉ
```

</details>

## Idea

Considerᵉ aᵉ
[noncoherentᵉ largeᵉ wildᵉ higherᵉ precategory](wild-category-theory.noncoherent-large-wild-higher-precategories.mdᵉ)
`𝒞`.ᵉ Anᵉ
{{#conceptᵉ "isomorphism"ᵉ Disambiguation="inᵉ noncoherentᵉ largeᵉ wildᵉ higherᵉ precategories"ᵉ Agda=is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ}}
in `𝒞`ᵉ isᵉ aᵉ morphismᵉ `fᵉ : xᵉ → y`ᵉ in `𝒞`ᵉ [equipped](foundation.structure.mdᵉ) with

-ᵉ aᵉ morphismᵉ `sᵉ : yᵉ → x`ᵉ
-ᵉ aᵉ $2$-morphismᵉ `is-split-epiᵉ : fᵉ ∘ᵉ sᵉ → id`,ᵉ where `∘`ᵉ andᵉ `id`ᵉ denoteᵉ
  compositionᵉ ofᵉ morphismsᵉ andᵉ theᵉ identityᵉ morphismᵉ givenᵉ byᵉ theᵉ transitiveᵉ andᵉ
  reflexiveᵉ structureᵉ onᵉ theᵉ underlyingᵉ
  [globularᵉ type](structured-types.globular-types.md),ᵉ respectivelyᵉ
-ᵉ aᵉ proofᵉ `is-iso-is-split-epiᵉ : is-isoᵉ is-split-epi`,ᵉ whichᵉ showsᵉ thatᵉ theᵉ
  aboveᵉ $2$-morphismᵉ isᵉ itselfᵉ anᵉ isomorphismᵉ
-ᵉ aᵉ morphismᵉ `rᵉ : yᵉ → x`ᵉ
-ᵉ aᵉ $2$-morphismᵉ `is-split-monoᵉ : rᵉ ∘ᵉ fᵉ → id`ᵉ
-ᵉ aᵉ proofᵉ `is-iso-is-split-monoᵉ : is-isoᵉ is-split-mono`.ᵉ

Thisᵉ definitionᵉ ofᵉ anᵉ isomorphismᵉ mirrorsᵉ theᵉ definitionᵉ ofᵉ
[biinvertibleᵉ maps](foundation-core.equivalences.mdᵉ) betweenᵉ types.ᵉ

Itᵉ wouldᵉ beᵉ in theᵉ spiritᵉ ofᵉ theᵉ libraryᵉ to firstᵉ defineᵉ whatᵉ splitᵉ epimorphismsᵉ
andᵉ splitᵉ monomorphismsᵉ are,ᵉ andᵉ thenᵉ defineᵉ isomorphismsᵉ asᵉ thoseᵉ morphismsᵉ
whichᵉ areᵉ both.ᵉ Whenᵉ attemptingᵉ thatᵉ definition,ᵉ oneᵉ runsᵉ intoᵉ theᵉ problemᵉ thatᵉ
theᵉ $2$-morphismsᵉ in theᵉ definitionsᵉ shouldᵉ stillᵉ beᵉ isomorphisms.ᵉ

Noteᵉ thatᵉ aᵉ noncoherentᵉ largeᵉ wildᵉ higherᵉ precategoryᵉ isᵉ theᵉ mostᵉ generalᵉ
settingᵉ thatᵉ allowsᵉ usᵉ to _defineᵉ_ isomorphismsᵉ in largeᵉ wildᵉ categories,ᵉ butᵉ
becauseᵉ ofᵉ theᵉ missingᵉ coherences,ᵉ weᵉ cannotᵉ showᵉ anyᵉ ofᵉ theᵉ expectedᵉ
properties.ᵉ Forᵉ exampleᵉ weᵉ cannotᵉ showᵉ thatᵉ allᵉ identitiesᵉ areᵉ isomorphisms,ᵉ orᵉ
thatᵉ isomorphismsᵉ compose.ᵉ

## Definitions

### The predicate on morphisms of being an isomorphism

```agda
record
  is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (𝒞ᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ αᵉ βᵉ)
  {l1ᵉ : Level} {xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ l1ᵉ}
  {l2ᵉ : Level} {yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ l2ᵉ}
  (fᵉ : hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ xᵉ yᵉ)
  : UUᵉ (βᵉ l1ᵉ l1ᵉ ⊔ βᵉ l2ᵉ l1ᵉ ⊔ βᵉ l2ᵉ l2ᵉ)
  where
  field
    hom-section-is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
      hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ yᵉ xᵉ
    is-split-epi-is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
      2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ
        ( comp-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ
          ( fᵉ)
          ( hom-section-is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ))
        ( id-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ)
    is-iso-is-split-epi-is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
      is-iso-Noncoherent-Wild-Higher-Precategoryᵉ
        ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategoryᵉ
          ( 𝒞ᵉ)
          ( yᵉ)
          ( yᵉ))
        ( is-split-epi-is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

    hom-retraction-is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
      hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ yᵉ xᵉ
    is-split-mono-is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
      2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ
        ( comp-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ
          ( hom-retraction-is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ)
          ( fᵉ))
        ( id-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ)
    is-iso-is-split-mono-is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
      is-iso-Noncoherent-Wild-Higher-Precategoryᵉ
        ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategoryᵉ
          ( 𝒞ᵉ)
          ( xᵉ)
          ( xᵉ))
        ( is-split-mono-is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

open is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ public
```

### Isomorphisms in a noncoherent large wild higher precategory

```agda
iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (𝒞ᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ αᵉ βᵉ)
  {l1ᵉ : Level} (xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ l1ᵉ)
  {l2ᵉ : Level} (yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ l2ᵉ) →
  UUᵉ (βᵉ l1ᵉ l1ᵉ ⊔ βᵉ l1ᵉ l2ᵉ ⊔ βᵉ l2ᵉ l1ᵉ ⊔ βᵉ l2ᵉ l2ᵉ)
iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ xᵉ yᵉ =
  Σᵉ ( hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ xᵉ yᵉ)
    ( is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ)
```

### Components of an isomorphism in a noncoherent large wild higher precategory

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {𝒞ᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ αᵉ βᵉ}
  {l1ᵉ : Level} {xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ l1ᵉ}
  {l2ᵉ : Level} {yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ l2ᵉ}
  (fᵉ : iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ xᵉ yᵉ)
  where

  hom-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ xᵉ yᵉ
  hom-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ = pr1ᵉ fᵉ

  is-iso-hom-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ
      ( hom-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ)
  is-iso-hom-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ = pr2ᵉ fᵉ

  hom-section-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ yᵉ xᵉ
  hom-section-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    hom-section-is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      ( is-iso-hom-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ
      ( comp-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ
        ( hom-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ)
        ( hom-section-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ))
      ( id-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ)
  is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    is-split-epi-is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      ( is-iso-hom-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  is-iso-is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    is-iso-Noncoherent-Wild-Higher-Precategoryᵉ
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategoryᵉ
        ( 𝒞ᵉ)
        ( yᵉ)
        ( yᵉ))
      ( is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ)
  is-iso-is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    is-iso-is-split-epi-is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      ( is-iso-hom-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  iso-is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    iso-Noncoherent-Wild-Higher-Precategoryᵉ
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategoryᵉ
        ( 𝒞ᵉ)
        ( yᵉ)
        ( yᵉ))
      ( comp-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ
        ( hom-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ)
        ( hom-section-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ))
      ( id-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ)
  pr1ᵉ iso-is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ
  pr2ᵉ iso-is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    is-iso-is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ

  hom-retraction-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ yᵉ xᵉ
  hom-retraction-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    hom-retraction-is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      ( is-iso-hom-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ
      ( comp-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ
        ( hom-retraction-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ)
        ( hom-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ))
      ( id-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ)
  is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    is-split-mono-is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      ( is-iso-hom-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  is-iso-is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    is-iso-Noncoherent-Wild-Higher-Precategoryᵉ
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategoryᵉ
        ( 𝒞ᵉ)
        ( xᵉ)
        ( xᵉ))
      ( is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ)
  is-iso-is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    is-iso-is-split-mono-is-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      ( is-iso-hom-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  iso-is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    iso-Noncoherent-Wild-Higher-Precategoryᵉ
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategoryᵉ
        ( 𝒞ᵉ)
        ( xᵉ)
        ( xᵉ))
      ( comp-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ
        ( hom-retraction-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ)
        ( hom-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ))
      ( id-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ)
  pr1ᵉ iso-is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ
  pr2ᵉ iso-is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    is-iso-is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategoryᵉ
```

## See also

-ᵉ [Isomorphismsᵉ in noncoherentᵉ wildᵉ higherᵉ precategories](wild-category-theory.isomorphisms-in-noncoherent-wild-higher-precategories.mdᵉ)