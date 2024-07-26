# Equivalences of undirected graphs

```agda
module graph-theory.equivalences-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import graph-theory.morphisms-undirected-graphsᵉ
open import graph-theory.undirected-graphsᵉ
```

</details>

## Idea

Anᵉ **equivalenceᵉ ofᵉ undirectedᵉ graphs**ᵉ isᵉ aᵉ
[morphism](graph-theory.morphisms-undirected-graphs.mdᵉ) ofᵉ
[undirectedᵉ graphs](graph-theory.undirected-graphs.mdᵉ) thatᵉ inducesᵉ anᵉ
[equivalence](foundation-core.equivalences.mdᵉ) onᵉ verticesᵉ andᵉ equivalencesᵉ onᵉ
edges.ᵉ

## Definitions

### Equivalences of undirected graphs

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Undirected-Graphᵉ l3ᵉ l4ᵉ)
  where

  equiv-Undirected-Graphᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  equiv-Undirected-Graphᵉ =
    Σᵉ ( vertex-Undirected-Graphᵉ Gᵉ ≃ᵉ vertex-Undirected-Graphᵉ Hᵉ)
      ( λ fᵉ →
        ( pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
        edge-Undirected-Graphᵉ Gᵉ pᵉ ≃ᵉ
        edge-Undirected-Graphᵉ Hᵉ (map-equiv-unordered-pairᵉ fᵉ pᵉ))

  equiv-vertex-equiv-Undirected-Graphᵉ :
    equiv-Undirected-Graphᵉ →
    vertex-Undirected-Graphᵉ Gᵉ ≃ᵉ vertex-Undirected-Graphᵉ Hᵉ
  equiv-vertex-equiv-Undirected-Graphᵉ fᵉ = pr1ᵉ fᵉ

  vertex-equiv-Undirected-Graphᵉ :
    equiv-Undirected-Graphᵉ →
    vertex-Undirected-Graphᵉ Gᵉ → vertex-Undirected-Graphᵉ Hᵉ
  vertex-equiv-Undirected-Graphᵉ fᵉ =
    map-equivᵉ (equiv-vertex-equiv-Undirected-Graphᵉ fᵉ)

  equiv-unordered-pair-vertices-equiv-Undirected-Graphᵉ :
    equiv-Undirected-Graphᵉ →
    unordered-pair-vertices-Undirected-Graphᵉ Gᵉ ≃ᵉ
    unordered-pair-vertices-Undirected-Graphᵉ Hᵉ
  equiv-unordered-pair-vertices-equiv-Undirected-Graphᵉ fᵉ =
    equiv-unordered-pairᵉ (equiv-vertex-equiv-Undirected-Graphᵉ fᵉ)

  unordered-pair-vertices-equiv-Undirected-Graphᵉ :
    equiv-Undirected-Graphᵉ →
    unordered-pair-vertices-Undirected-Graphᵉ Gᵉ →
    unordered-pair-vertices-Undirected-Graphᵉ Hᵉ
  unordered-pair-vertices-equiv-Undirected-Graphᵉ fᵉ =
    map-equiv-unordered-pairᵉ (equiv-vertex-equiv-Undirected-Graphᵉ fᵉ)

  standard-unordered-pair-vertices-equiv-Undirected-Graphᵉ :
    (eᵉ : equiv-Undirected-Graphᵉ) (xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ) →
    unordered-pair-vertices-equiv-Undirected-Graphᵉ
      ( eᵉ)
      ( standard-unordered-pairᵉ xᵉ yᵉ) ＝ᵉ
    standard-unordered-pairᵉ
      ( vertex-equiv-Undirected-Graphᵉ eᵉ xᵉ)
      ( vertex-equiv-Undirected-Graphᵉ eᵉ yᵉ)
  standard-unordered-pair-vertices-equiv-Undirected-Graphᵉ eᵉ =
    equiv-standard-unordered-pairᵉ (equiv-vertex-equiv-Undirected-Graphᵉ eᵉ)

  equiv-edge-equiv-Undirected-Graphᵉ :
    (fᵉ : equiv-Undirected-Graphᵉ)
    (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
    edge-Undirected-Graphᵉ Gᵉ pᵉ ≃ᵉ
    edge-Undirected-Graphᵉ Hᵉ
      ( unordered-pair-vertices-equiv-Undirected-Graphᵉ fᵉ pᵉ)
  equiv-edge-equiv-Undirected-Graphᵉ fᵉ = pr2ᵉ fᵉ

  edge-equiv-Undirected-Graphᵉ :
    (fᵉ : equiv-Undirected-Graphᵉ)
    (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
    edge-Undirected-Graphᵉ Gᵉ pᵉ →
    edge-Undirected-Graphᵉ Hᵉ
      ( unordered-pair-vertices-equiv-Undirected-Graphᵉ fᵉ pᵉ)
  edge-equiv-Undirected-Graphᵉ fᵉ pᵉ =
    map-equivᵉ (equiv-edge-equiv-Undirected-Graphᵉ fᵉ pᵉ)

  equiv-edge-standard-unordered-pair-vertices-equiv-Undirected-Graphᵉ :
    (eᵉ : equiv-Undirected-Graphᵉ) (xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ) →
    edge-Undirected-Graphᵉ Gᵉ (standard-unordered-pairᵉ xᵉ yᵉ) ≃ᵉ
    edge-Undirected-Graphᵉ Hᵉ
      ( standard-unordered-pairᵉ
        ( vertex-equiv-Undirected-Graphᵉ eᵉ xᵉ)
        ( vertex-equiv-Undirected-Graphᵉ eᵉ yᵉ))
  equiv-edge-standard-unordered-pair-vertices-equiv-Undirected-Graphᵉ eᵉ xᵉ yᵉ =
    ( equiv-trᵉ
      ( edge-Undirected-Graphᵉ Hᵉ)
      ( standard-unordered-pair-vertices-equiv-Undirected-Graphᵉ eᵉ xᵉ yᵉ)) ∘eᵉ
    ( equiv-edge-equiv-Undirected-Graphᵉ eᵉ (standard-unordered-pairᵉ xᵉ yᵉ))

  edge-standard-unordered-pair-vertices-equiv-Undirected-Graphᵉ :
    (eᵉ : equiv-Undirected-Graphᵉ) (xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ) →
    edge-Undirected-Graphᵉ Gᵉ (standard-unordered-pairᵉ xᵉ yᵉ) →
    edge-Undirected-Graphᵉ Hᵉ
      ( standard-unordered-pairᵉ
        ( vertex-equiv-Undirected-Graphᵉ eᵉ xᵉ)
        ( vertex-equiv-Undirected-Graphᵉ eᵉ yᵉ))
  edge-standard-unordered-pair-vertices-equiv-Undirected-Graphᵉ eᵉ xᵉ yᵉ =
    map-equivᵉ
      ( equiv-edge-standard-unordered-pair-vertices-equiv-Undirected-Graphᵉ
          eᵉ xᵉ yᵉ)

  hom-equiv-Undirected-Graphᵉ :
    equiv-Undirected-Graphᵉ → hom-Undirected-Graphᵉ Gᵉ Hᵉ
  pr1ᵉ (hom-equiv-Undirected-Graphᵉ fᵉ) = vertex-equiv-Undirected-Graphᵉ fᵉ
  pr2ᵉ (hom-equiv-Undirected-Graphᵉ fᵉ) = edge-equiv-Undirected-Graphᵉ fᵉ
```

### The identity equivalence of unordered graphs

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  where

  id-equiv-Undirected-Graphᵉ : equiv-Undirected-Graphᵉ Gᵉ Gᵉ
  pr1ᵉ id-equiv-Undirected-Graphᵉ = id-equivᵉ
  pr2ᵉ id-equiv-Undirected-Graphᵉ pᵉ = id-equivᵉ

  edge-standard-unordered-pair-vertices-id-equiv-Undirected-Graphᵉ :
    (xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ) →
    ( edge-standard-unordered-pair-vertices-equiv-Undirected-Graphᵉ Gᵉ Gᵉ
      ( id-equiv-Undirected-Graphᵉ) xᵉ yᵉ) ~ᵉ
    ( idᵉ)
  edge-standard-unordered-pair-vertices-id-equiv-Undirected-Graphᵉ xᵉ yᵉ eᵉ =
    apᵉ
      ( λ tᵉ → trᵉ (edge-Undirected-Graphᵉ Gᵉ) tᵉ eᵉ)
      ( id-equiv-standard-unordered-pairᵉ xᵉ yᵉ)
```

## Properties

### Characterizing the identity type of equivalences of unordered graphs

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Undirected-Graphᵉ l3ᵉ l4ᵉ)
  where

  htpy-equiv-Undirected-Graphᵉ :
    (fᵉ gᵉ : equiv-Undirected-Graphᵉ Gᵉ Hᵉ) → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-equiv-Undirected-Graphᵉ fᵉ gᵉ =
    htpy-hom-Undirected-Graphᵉ Gᵉ Hᵉ
      ( hom-equiv-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ)
      ( hom-equiv-Undirected-Graphᵉ Gᵉ Hᵉ gᵉ)

  refl-htpy-equiv-Undirected-Graphᵉ :
    (fᵉ : equiv-Undirected-Graphᵉ Gᵉ Hᵉ) → htpy-equiv-Undirected-Graphᵉ fᵉ fᵉ
  refl-htpy-equiv-Undirected-Graphᵉ fᵉ =
    refl-htpy-hom-Undirected-Graphᵉ Gᵉ Hᵉ (hom-equiv-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ)

  htpy-eq-equiv-Undirected-Graphᵉ :
    (fᵉ gᵉ : equiv-Undirected-Graphᵉ Gᵉ Hᵉ) → Idᵉ fᵉ gᵉ →
    htpy-equiv-Undirected-Graphᵉ fᵉ gᵉ
  htpy-eq-equiv-Undirected-Graphᵉ fᵉ .fᵉ reflᵉ = refl-htpy-equiv-Undirected-Graphᵉ fᵉ

  is-torsorial-htpy-equiv-Undirected-Graphᵉ :
    (fᵉ : equiv-Undirected-Graphᵉ Gᵉ Hᵉ) →
    is-torsorialᵉ (htpy-equiv-Undirected-Graphᵉ fᵉ)
  is-torsorial-htpy-equiv-Undirected-Graphᵉ fᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpy-equivᵉ (equiv-vertex-equiv-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ))
      ( pairᵉ (equiv-vertex-equiv-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ) refl-htpyᵉ)
      ( is-contr-equiv'ᵉ
        ( Σᵉ ( (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
              edge-Undirected-Graphᵉ Gᵉ pᵉ ≃ᵉ
              edge-Undirected-Graphᵉ Hᵉ
                ( unordered-pair-vertices-equiv-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ pᵉ))
            ( λ gEᵉ →
              (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
              (eᵉ : edge-Undirected-Graphᵉ Gᵉ pᵉ) →
              Idᵉ (edge-equiv-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ pᵉ eᵉ) (map-equivᵉ (gEᵉ pᵉ) eᵉ)))
        ( equiv-totᵉ
          ( λ gEᵉ →
            equiv-Π-equiv-familyᵉ
              ( λ pᵉ →
                equiv-Π-equiv-familyᵉ
                  ( λ eᵉ →
                    equiv-concatᵉ
                      ( pr2ᵉ (refl-htpy-equiv-Undirected-Graphᵉ fᵉ) pᵉ eᵉ)
                      ( map-equivᵉ (gEᵉ pᵉ) eᵉ)))))
        ( is-torsorial-Eq-Πᵉ
          ( λ pᵉ →
            is-torsorial-htpy-equivᵉ
              ( equiv-edge-equiv-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ pᵉ))))

  is-equiv-htpy-eq-equiv-Undirected-Graphᵉ :
    (fᵉ gᵉ : equiv-Undirected-Graphᵉ Gᵉ Hᵉ) →
    is-equivᵉ (htpy-eq-equiv-Undirected-Graphᵉ fᵉ gᵉ)
  is-equiv-htpy-eq-equiv-Undirected-Graphᵉ fᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-equiv-Undirected-Graphᵉ fᵉ)
      ( htpy-eq-equiv-Undirected-Graphᵉ fᵉ)

  extensionality-equiv-Undirected-Graphᵉ :
    (fᵉ gᵉ : equiv-Undirected-Graphᵉ Gᵉ Hᵉ) →
    Idᵉ fᵉ gᵉ ≃ᵉ htpy-equiv-Undirected-Graphᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-equiv-Undirected-Graphᵉ fᵉ gᵉ) =
    htpy-eq-equiv-Undirected-Graphᵉ fᵉ gᵉ
  pr2ᵉ (extensionality-equiv-Undirected-Graphᵉ fᵉ gᵉ) =
    is-equiv-htpy-eq-equiv-Undirected-Graphᵉ fᵉ gᵉ

  eq-htpy-equiv-Undirected-Graphᵉ :
    (fᵉ gᵉ : equiv-Undirected-Graphᵉ Gᵉ Hᵉ) →
    htpy-equiv-Undirected-Graphᵉ fᵉ gᵉ → Idᵉ fᵉ gᵉ
  eq-htpy-equiv-Undirected-Graphᵉ fᵉ gᵉ =
    map-inv-is-equivᵉ (is-equiv-htpy-eq-equiv-Undirected-Graphᵉ fᵉ gᵉ)
```

### Univalence for unordered graphs

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  where

  equiv-eq-Undirected-Graphᵉ :
    (Hᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) → Idᵉ Gᵉ Hᵉ → equiv-Undirected-Graphᵉ Gᵉ Hᵉ
  equiv-eq-Undirected-Graphᵉ .Gᵉ reflᵉ = id-equiv-Undirected-Graphᵉ Gᵉ

  is-torsorial-equiv-Undirected-Graphᵉ :
    is-torsorialᵉ (equiv-Undirected-Graphᵉ Gᵉ)
  is-torsorial-equiv-Undirected-Graphᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equivᵉ (vertex-Undirected-Graphᵉ Gᵉ))
      ( pairᵉ (vertex-Undirected-Graphᵉ Gᵉ) id-equivᵉ)
      ( is-torsorial-Eq-Πᵉ
        ( λ pᵉ → is-torsorial-equivᵉ (edge-Undirected-Graphᵉ Gᵉ pᵉ)))

  is-equiv-equiv-eq-Undirected-Graphᵉ :
    (Hᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) → is-equivᵉ (equiv-eq-Undirected-Graphᵉ Hᵉ)
  is-equiv-equiv-eq-Undirected-Graphᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-equiv-Undirected-Graphᵉ)
      ( equiv-eq-Undirected-Graphᵉ)

  extensionality-Undirected-Graphᵉ :
    (Hᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) → Idᵉ Gᵉ Hᵉ ≃ᵉ equiv-Undirected-Graphᵉ Gᵉ Hᵉ
  pr1ᵉ (extensionality-Undirected-Graphᵉ Hᵉ) = equiv-eq-Undirected-Graphᵉ Hᵉ
  pr2ᵉ (extensionality-Undirected-Graphᵉ Hᵉ) = is-equiv-equiv-eq-Undirected-Graphᵉ Hᵉ

  eq-equiv-Undirected-Graphᵉ :
    (Hᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) → equiv-Undirected-Graphᵉ Gᵉ Hᵉ → Idᵉ Gᵉ Hᵉ
  eq-equiv-Undirected-Graphᵉ Hᵉ =
    map-inv-is-equivᵉ (is-equiv-equiv-eq-Undirected-Graphᵉ Hᵉ)
```

## External links

-ᵉ [Graphᵉ isomoprhism](https://www.wikidata.org/entity/Q303100ᵉ) atᵉ Wikidataᵉ
-ᵉ [Graphᵉ isomorphism](https://en.wikipedia.org/wiki/Graph_isomorphismᵉ) atᵉ
  Wikipediaᵉ
-ᵉ [Graphᵉ isomorphism](https://mathworld.wolfram.com/GraphIsomorphism.htmlᵉ) atᵉ
  Wolframᵉ Mathworldᵉ
-ᵉ [Isomorphism](https://ncatlab.org/nlab/show/isomorphismᵉ) atᵉ $n$Labᵉ