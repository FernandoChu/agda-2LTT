# Morphisms of directed graphs

```agda
module graph-theory.morphisms-directed-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-transportᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ
```

</details>

## Idea

Aᵉ **morphismᵉ ofᵉ directedᵉ graphs**ᵉ fromᵉ `G`ᵉ to `H`ᵉ consistsᵉ ofᵉ aᵉ mapᵉ `f`ᵉ fromᵉ theᵉ
verticesᵉ ofᵉ `G`ᵉ to theᵉ verticesᵉ ofᵉ `H`,ᵉ andᵉ aᵉ familyᵉ ofᵉ mapsᵉ fromᵉ theᵉ edgesᵉ
`E_Gᵉ xᵉ y`ᵉ in `G`ᵉ to theᵉ edgesᵉ `E_Hᵉ (fᵉ xᵉ) (fᵉ y)`ᵉ in `H`.ᵉ

## Definitions

### Morphisms of directed graphs

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Directed-Graphᵉ l3ᵉ l4ᵉ)
  where

  hom-Directed-Graphᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-Directed-Graphᵉ =
    Σᵉ ( vertex-Directed-Graphᵉ Gᵉ → vertex-Directed-Graphᵉ Hᵉ)
      ( λ αᵉ →
        (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
        edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ → edge-Directed-Graphᵉ Hᵉ (αᵉ xᵉ) (αᵉ yᵉ))

  module _
    (fᵉ : hom-Directed-Graphᵉ)
    where

    vertex-hom-Directed-Graphᵉ :
      vertex-Directed-Graphᵉ Gᵉ → vertex-Directed-Graphᵉ Hᵉ
    vertex-hom-Directed-Graphᵉ = pr1ᵉ fᵉ

    edge-hom-Directed-Graphᵉ :
      {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} (eᵉ : edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ) →
      edge-Directed-Graphᵉ Hᵉ
        ( vertex-hom-Directed-Graphᵉ xᵉ)
        ( vertex-hom-Directed-Graphᵉ yᵉ)
    edge-hom-Directed-Graphᵉ {xᵉ} {yᵉ} eᵉ = pr2ᵉ fᵉ xᵉ yᵉ eᵉ

    direct-predecessor-hom-Directed-Graphᵉ :
      (xᵉ : vertex-Directed-Graphᵉ Gᵉ) →
      direct-predecessor-Directed-Graphᵉ Gᵉ xᵉ →
      direct-predecessor-Directed-Graphᵉ Hᵉ (vertex-hom-Directed-Graphᵉ xᵉ)
    direct-predecessor-hom-Directed-Graphᵉ xᵉ =
      map-Σᵉ
        ( λ yᵉ → edge-Directed-Graphᵉ Hᵉ yᵉ (vertex-hom-Directed-Graphᵉ xᵉ))
        ( vertex-hom-Directed-Graphᵉ)
        ( λ yᵉ → edge-hom-Directed-Graphᵉ)

    direct-successor-hom-Directed-Graphᵉ :
      (xᵉ : vertex-Directed-Graphᵉ Gᵉ) →
      direct-successor-Directed-Graphᵉ Gᵉ xᵉ →
      direct-successor-Directed-Graphᵉ Hᵉ (vertex-hom-Directed-Graphᵉ xᵉ)
    direct-successor-hom-Directed-Graphᵉ xᵉ =
      map-Σᵉ
        ( edge-Directed-Graphᵉ Hᵉ (vertex-hom-Directed-Graphᵉ xᵉ))
        ( vertex-hom-Directed-Graphᵉ)
        ( λ yᵉ → edge-hom-Directed-Graphᵉ)
```

### Composition of morphisms graphs

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Directed-Graphᵉ l3ᵉ l4ᵉ)
  (Kᵉ : Directed-Graphᵉ l5ᵉ l6ᵉ)
  where

  vertex-comp-hom-Directed-Graphᵉ :
    hom-Directed-Graphᵉ Hᵉ Kᵉ → hom-Directed-Graphᵉ Gᵉ Hᵉ →
    vertex-Directed-Graphᵉ Gᵉ → vertex-Directed-Graphᵉ Kᵉ
  vertex-comp-hom-Directed-Graphᵉ gᵉ fᵉ =
    (vertex-hom-Directed-Graphᵉ Hᵉ Kᵉ gᵉ) ∘ᵉ (vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ)

  edge-comp-hom-Directed-Graphᵉ :
    (gᵉ : hom-Directed-Graphᵉ Hᵉ Kᵉ) (fᵉ : hom-Directed-Graphᵉ Gᵉ Hᵉ)
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ →
    edge-Directed-Graphᵉ Kᵉ
      ( vertex-comp-hom-Directed-Graphᵉ gᵉ fᵉ xᵉ)
      ( vertex-comp-hom-Directed-Graphᵉ gᵉ fᵉ yᵉ)
  edge-comp-hom-Directed-Graphᵉ gᵉ fᵉ xᵉ yᵉ eᵉ =
    edge-hom-Directed-Graphᵉ Hᵉ Kᵉ gᵉ (edge-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ eᵉ)

  comp-hom-Directed-Graphᵉ :
    hom-Directed-Graphᵉ Hᵉ Kᵉ → hom-Directed-Graphᵉ Gᵉ Hᵉ →
    hom-Directed-Graphᵉ Gᵉ Kᵉ
  pr1ᵉ (comp-hom-Directed-Graphᵉ gᵉ fᵉ) = vertex-comp-hom-Directed-Graphᵉ gᵉ fᵉ
  pr2ᵉ (comp-hom-Directed-Graphᵉ gᵉ fᵉ) = edge-comp-hom-Directed-Graphᵉ gᵉ fᵉ
```

### Identity morphisms graphs

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  id-hom-Directed-Graphᵉ : hom-Directed-Graphᵉ Gᵉ Gᵉ
  pr1ᵉ id-hom-Directed-Graphᵉ = idᵉ
  pr2ᵉ id-hom-Directed-Graphᵉ _ _ = idᵉ
```

## Properties

### Characterizing the identity type of morphisms graphs

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Directed-Graphᵉ l3ᵉ l4ᵉ)
  where

  htpy-hom-Directed-Graphᵉ :
    (fᵉ gᵉ : hom-Directed-Graphᵉ Gᵉ Hᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-hom-Directed-Graphᵉ fᵉ gᵉ =
    Σᵉ ( vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ ~ᵉ vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ gᵉ)
      ( λ αᵉ →
        ( xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) (eᵉ : edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ) →
        binary-trᵉ
          ( edge-Directed-Graphᵉ Hᵉ)
          ( αᵉ xᵉ)
          ( αᵉ yᵉ)
          ( edge-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ eᵉ) ＝ᵉ
        edge-hom-Directed-Graphᵉ Gᵉ Hᵉ gᵉ eᵉ)

  module _
    (fᵉ gᵉ : hom-Directed-Graphᵉ Gᵉ Hᵉ) (αᵉ : htpy-hom-Directed-Graphᵉ fᵉ gᵉ)
    where

    vertex-htpy-hom-Directed-Graphᵉ :
      vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ ~ᵉ vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ gᵉ
    vertex-htpy-hom-Directed-Graphᵉ = pr1ᵉ αᵉ

    edge-htpy-hom-Directed-Graphᵉ :
      (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) (eᵉ : edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ) →
      binary-trᵉ
        ( edge-Directed-Graphᵉ Hᵉ)
        ( vertex-htpy-hom-Directed-Graphᵉ xᵉ)
        ( vertex-htpy-hom-Directed-Graphᵉ yᵉ)
        ( edge-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ eᵉ) ＝ᵉ
      edge-hom-Directed-Graphᵉ Gᵉ Hᵉ gᵉ eᵉ
    edge-htpy-hom-Directed-Graphᵉ = pr2ᵉ αᵉ

  refl-htpy-hom-Directed-Graphᵉ :
    (fᵉ : hom-Directed-Graphᵉ Gᵉ Hᵉ) → htpy-hom-Directed-Graphᵉ fᵉ fᵉ
  pr1ᵉ (refl-htpy-hom-Directed-Graphᵉ fᵉ) = refl-htpyᵉ
  pr2ᵉ (refl-htpy-hom-Directed-Graphᵉ fᵉ) xᵉ yᵉ eᵉ = reflᵉ

  htpy-eq-hom-Directed-Graphᵉ :
    (fᵉ gᵉ : hom-Directed-Graphᵉ Gᵉ Hᵉ) → fᵉ ＝ᵉ gᵉ → htpy-hom-Directed-Graphᵉ fᵉ gᵉ
  htpy-eq-hom-Directed-Graphᵉ fᵉ .fᵉ reflᵉ = refl-htpy-hom-Directed-Graphᵉ fᵉ

  is-torsorial-htpy-hom-Directed-Graphᵉ :
    (fᵉ : hom-Directed-Graphᵉ Gᵉ Hᵉ) →
    is-torsorialᵉ (htpy-hom-Directed-Graphᵉ fᵉ)
  is-torsorial-htpy-hom-Directed-Graphᵉ fᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ))
      ( pairᵉ
        ( vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ)
        ( refl-htpyᵉ))
      ( is-torsorial-Eq-Πᵉ
        ( λ xᵉ →
          is-torsorial-Eq-Πᵉ
            ( λ yᵉ → is-torsorial-htpyᵉ (edge-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ))))

  is-equiv-htpy-eq-hom-Directed-Graphᵉ :
    (fᵉ gᵉ : hom-Directed-Graphᵉ Gᵉ Hᵉ) → is-equivᵉ (htpy-eq-hom-Directed-Graphᵉ fᵉ gᵉ)
  is-equiv-htpy-eq-hom-Directed-Graphᵉ fᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-hom-Directed-Graphᵉ fᵉ)
      ( htpy-eq-hom-Directed-Graphᵉ fᵉ)

  extensionality-hom-Directed-Graphᵉ :
    (fᵉ gᵉ : hom-Directed-Graphᵉ Gᵉ Hᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-Directed-Graphᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-hom-Directed-Graphᵉ fᵉ gᵉ) = htpy-eq-hom-Directed-Graphᵉ fᵉ gᵉ
  pr2ᵉ (extensionality-hom-Directed-Graphᵉ fᵉ gᵉ) =
    is-equiv-htpy-eq-hom-Directed-Graphᵉ fᵉ gᵉ

  eq-htpy-hom-Directed-Graphᵉ :
    (fᵉ gᵉ : hom-Directed-Graphᵉ Gᵉ Hᵉ) → htpy-hom-Directed-Graphᵉ fᵉ gᵉ → (fᵉ ＝ᵉ gᵉ)
  eq-htpy-hom-Directed-Graphᵉ fᵉ gᵉ =
    map-inv-equivᵉ (extensionality-hom-Directed-Graphᵉ fᵉ gᵉ)
```

## External links

-ᵉ [Graphᵉ homomorphism](https://www.wikidata.org/entity/Q3385162ᵉ) onᵉ Wikidataᵉ
-ᵉ [Graphᵉ homomorphism](https://en.wikipedia.org/wiki/Graph_homomorphismᵉ) atᵉ
  Wikipediaᵉ