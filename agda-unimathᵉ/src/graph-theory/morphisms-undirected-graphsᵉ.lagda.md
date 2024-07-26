# Morphisms of undirected graphs

```agda
module graph-theory.morphisms-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import graph-theory.undirected-graphsᵉ
```

</details>

## Definitions

### Morphisms of undirected graphs

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Undirected-Graphᵉ l3ᵉ l4ᵉ)
  where

  hom-Undirected-Graphᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-Undirected-Graphᵉ =
    Σᵉ ( vertex-Undirected-Graphᵉ Gᵉ → vertex-Undirected-Graphᵉ Hᵉ)
      ( λ fᵉ →
        ( pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
        edge-Undirected-Graphᵉ Gᵉ pᵉ →
        edge-Undirected-Graphᵉ Hᵉ (map-unordered-pairᵉ fᵉ pᵉ))

  vertex-hom-Undirected-Graphᵉ :
    hom-Undirected-Graphᵉ → vertex-Undirected-Graphᵉ Gᵉ → vertex-Undirected-Graphᵉ Hᵉ
  vertex-hom-Undirected-Graphᵉ fᵉ = pr1ᵉ fᵉ

  unordered-pair-vertices-hom-Undirected-Graphᵉ :
    hom-Undirected-Graphᵉ →
    unordered-pair-vertices-Undirected-Graphᵉ Gᵉ →
    unordered-pair-vertices-Undirected-Graphᵉ Hᵉ
  unordered-pair-vertices-hom-Undirected-Graphᵉ fᵉ =
    map-unordered-pairᵉ (vertex-hom-Undirected-Graphᵉ fᵉ)

  edge-hom-Undirected-Graphᵉ :
    (fᵉ : hom-Undirected-Graphᵉ)
    (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
    edge-Undirected-Graphᵉ Gᵉ pᵉ →
    edge-Undirected-Graphᵉ Hᵉ
      ( unordered-pair-vertices-hom-Undirected-Graphᵉ fᵉ pᵉ)
  edge-hom-Undirected-Graphᵉ fᵉ = pr2ᵉ fᵉ
```

### Composition of morphisms of undirected graphs

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Undirected-Graphᵉ l3ᵉ l4ᵉ)
  (Kᵉ : Undirected-Graphᵉ l5ᵉ l6ᵉ)
  where

  comp-hom-Undirected-Graphᵉ :
    hom-Undirected-Graphᵉ Hᵉ Kᵉ → hom-Undirected-Graphᵉ Gᵉ Hᵉ →
    hom-Undirected-Graphᵉ Gᵉ Kᵉ
  pr1ᵉ (comp-hom-Undirected-Graphᵉ (pairᵉ gVᵉ gEᵉ) (pairᵉ fVᵉ fEᵉ)) = gVᵉ ∘ᵉ fVᵉ
  pr2ᵉ (comp-hom-Undirected-Graphᵉ (pairᵉ gVᵉ gEᵉ) (pairᵉ fVᵉ fEᵉ)) pᵉ eᵉ =
    gEᵉ (map-unordered-pairᵉ fVᵉ pᵉ) (fEᵉ pᵉ eᵉ)
```

### Identity morphisms of undirected graphs

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  where

  id-hom-Undirected-Graphᵉ : hom-Undirected-Graphᵉ Gᵉ Gᵉ
  pr1ᵉ id-hom-Undirected-Graphᵉ = idᵉ
  pr2ᵉ id-hom-Undirected-Graphᵉ pᵉ = idᵉ
```

## Properties

### Characterizing the identity type of morphisms of undirected graphs

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Undirected-Graphᵉ l3ᵉ l4ᵉ)
  where

  htpy-hom-Undirected-Graphᵉ :
    (fᵉ gᵉ : hom-Undirected-Graphᵉ Gᵉ Hᵉ) → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-hom-Undirected-Graphᵉ fᵉ gᵉ =
    Σᵉ ( vertex-hom-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ ~ᵉ vertex-hom-Undirected-Graphᵉ Gᵉ Hᵉ gᵉ)
      ( λ αᵉ →
        ( pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
        ( eᵉ : edge-Undirected-Graphᵉ Gᵉ pᵉ) →
        Idᵉ
          ( trᵉ
            ( edge-Undirected-Graphᵉ Hᵉ)
            ( htpy-unordered-pairᵉ αᵉ pᵉ)
            ( edge-hom-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ pᵉ eᵉ))
          ( edge-hom-Undirected-Graphᵉ Gᵉ Hᵉ gᵉ pᵉ eᵉ))

  refl-htpy-hom-Undirected-Graphᵉ :
    (fᵉ : hom-Undirected-Graphᵉ Gᵉ Hᵉ) → htpy-hom-Undirected-Graphᵉ fᵉ fᵉ
  pr1ᵉ (refl-htpy-hom-Undirected-Graphᵉ fᵉ) = refl-htpyᵉ
  pr2ᵉ (refl-htpy-hom-Undirected-Graphᵉ fᵉ) pᵉ eᵉ =
    apᵉ
      ( λ tᵉ →
        trᵉ (edge-Undirected-Graphᵉ Hᵉ) tᵉ (edge-hom-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ pᵉ eᵉ))
      ( preserves-refl-htpy-unordered-pairᵉ
        ( vertex-hom-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ) pᵉ)

  htpy-eq-hom-Undirected-Graphᵉ :
    (fᵉ gᵉ : hom-Undirected-Graphᵉ Gᵉ Hᵉ) → Idᵉ fᵉ gᵉ → htpy-hom-Undirected-Graphᵉ fᵉ gᵉ
  htpy-eq-hom-Undirected-Graphᵉ fᵉ .fᵉ reflᵉ = refl-htpy-hom-Undirected-Graphᵉ fᵉ

  abstract
    is-torsorial-htpy-hom-Undirected-Graphᵉ :
      (fᵉ : hom-Undirected-Graphᵉ Gᵉ Hᵉ) →
      is-torsorialᵉ (htpy-hom-Undirected-Graphᵉ fᵉ)
    is-torsorial-htpy-hom-Undirected-Graphᵉ fᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpyᵉ (vertex-hom-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ))
        ( pairᵉ (vertex-hom-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ) refl-htpyᵉ)
        ( is-contr-equiv'ᵉ
          ( Σᵉ ( (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
                edge-Undirected-Graphᵉ Gᵉ pᵉ →
                edge-Undirected-Graphᵉ Hᵉ
                  ( unordered-pair-vertices-hom-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ pᵉ))
              ( λ gEᵉ →
                (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
                (eᵉ : edge-Undirected-Graphᵉ Gᵉ pᵉ) →
                Idᵉ (edge-hom-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ pᵉ eᵉ) (gEᵉ pᵉ eᵉ)))
          ( equiv-totᵉ
            ( λ gEᵉ →
              equiv-Π-equiv-familyᵉ
                ( λ pᵉ →
                  equiv-Π-equiv-familyᵉ
                    ( λ eᵉ →
                      equiv-concatᵉ
                        ( pr2ᵉ (refl-htpy-hom-Undirected-Graphᵉ fᵉ) pᵉ eᵉ)
                        ( gEᵉ pᵉ eᵉ)))))
          ( is-torsorial-Eq-Πᵉ
            ( λ pᵉ → is-torsorial-htpyᵉ (edge-hom-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ pᵉ))))

  is-equiv-htpy-eq-hom-Undirected-Graphᵉ :
    (fᵉ gᵉ : hom-Undirected-Graphᵉ Gᵉ Hᵉ) →
    is-equivᵉ (htpy-eq-hom-Undirected-Graphᵉ fᵉ gᵉ)
  is-equiv-htpy-eq-hom-Undirected-Graphᵉ fᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-hom-Undirected-Graphᵉ fᵉ)
      ( htpy-eq-hom-Undirected-Graphᵉ fᵉ)

  extensionality-hom-Undirected-Graphᵉ :
    (fᵉ gᵉ : hom-Undirected-Graphᵉ Gᵉ Hᵉ) → Idᵉ fᵉ gᵉ ≃ᵉ htpy-hom-Undirected-Graphᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-hom-Undirected-Graphᵉ fᵉ gᵉ) =
    htpy-eq-hom-Undirected-Graphᵉ fᵉ gᵉ
  pr2ᵉ (extensionality-hom-Undirected-Graphᵉ fᵉ gᵉ) =
    is-equiv-htpy-eq-hom-Undirected-Graphᵉ fᵉ gᵉ

  eq-htpy-hom-Undirected-Graphᵉ :
    (fᵉ gᵉ : hom-Undirected-Graphᵉ Gᵉ Hᵉ) → htpy-hom-Undirected-Graphᵉ fᵉ gᵉ → Idᵉ fᵉ gᵉ
  eq-htpy-hom-Undirected-Graphᵉ fᵉ gᵉ =
    map-inv-is-equivᵉ (is-equiv-htpy-eq-hom-Undirected-Graphᵉ fᵉ gᵉ)
```

## External links

-ᵉ [Graphᵉ homomorphism](https://www.wikidata.org/entity/Q3385162ᵉ) onᵉ Wikidataᵉ
-ᵉ [Graphᵉ homomorphism](https://en.wikipedia.org/wiki/Graph_homomorphismᵉ) atᵉ
  Wikipediaᵉ