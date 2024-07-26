# Equivalences of enriched directed trees

```agda
module trees.equivalences-enriched-directed-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import trees.enriched-directed-treesᵉ
open import trees.equivalences-directed-treesᵉ
open import trees.morphisms-directed-treesᵉ
open import trees.morphisms-enriched-directed-treesᵉ
open import trees.rooted-morphisms-enriched-directed-treesᵉ
```

</details>

## Idea

Anᵉ **equivalenceᵉ ofᵉ `(A,B)`-enrichedᵉ directedᵉ trees**ᵉ fromᵉ `S`ᵉ to `T`ᵉ isᵉ aᵉ
shape-preservingᵉ equivalenceᵉ betweenᵉ theirᵉ underlyingᵉ trees,ᵉ whichᵉ alsoᵉ
preservesᵉ theᵉ enrichmentᵉ equivalences.ᵉ

## Definition

### The condition of being an equivalence of enriched directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Sᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  (Tᵉ : Enriched-Directed-Treeᵉ l5ᵉ l6ᵉ Aᵉ Bᵉ)
  where

  is-equiv-hom-Enriched-Directed-Treeᵉ :
    hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ → UUᵉ (l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  is-equiv-hom-Enriched-Directed-Treeᵉ fᵉ =
    is-equiv-hom-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( directed-tree-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ)

  preserves-root-is-equiv-node-hom-Enriched-Directed-Treeᵉ :
    ( fᵉ : hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ) →
    is-equivᵉ
      ( node-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ) →
    preserves-root-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ
  preserves-root-is-equiv-node-hom-Enriched-Directed-Treeᵉ fᵉ =
    preserves-root-is-equiv-node-hom-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( directed-tree-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ)
```

### Equivalences of enriched directed trees

```agda
equiv-Enriched-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) →
  Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ → Enriched-Directed-Treeᵉ l5ᵉ l6ᵉ Aᵉ Bᵉ →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ =
  Σᵉ ( equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ))
    ( λ eᵉ →
      Σᵉ ( coherence-triangle-mapsᵉ
          ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
          ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
          ( node-equiv-Directed-Treeᵉ
            ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
            ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
            ( eᵉ)))
        ( λ Hᵉ →
          (xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ) →
          htpy-equivᵉ
            ( ( equiv-direct-predecessor-equiv-Directed-Treeᵉ
                ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
                ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
                ( eᵉ)
                ( xᵉ)) ∘eᵉ
              ( enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ xᵉ))
            ( ( enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
                ( node-equiv-Directed-Treeᵉ
                  ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
                  ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
                  ( eᵉ)
                  ( xᵉ))) ∘eᵉ
              ( equiv-trᵉ Bᵉ (Hᵉ xᵉ)))))

equiv-is-equiv-hom-Enriched-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Sᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  (Tᵉ : Enriched-Directed-Treeᵉ l5ᵉ l6ᵉ Aᵉ Bᵉ) →
  (fᵉ : hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ) →
  is-equiv-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ →
  equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ
equiv-is-equiv-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ Hᵉ =
  map-Σ-map-baseᵉ
    ( equiv-is-equiv-hom-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( directed-tree-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ))
    ( _)
    ( Hᵉ ,ᵉ
      shape-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ ,ᵉ
      enrichment-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Sᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ) (Tᵉ : Enriched-Directed-Treeᵉ l5ᵉ l6ᵉ Aᵉ Bᵉ)
  (eᵉ : equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ)
  where

  equiv-directed-tree-equiv-Enriched-Directed-Treeᵉ :
    equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
  equiv-directed-tree-equiv-Enriched-Directed-Treeᵉ = pr1ᵉ eᵉ

  equiv-node-equiv-Enriched-Directed-Treeᵉ :
    node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ ≃ᵉ node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
  equiv-node-equiv-Enriched-Directed-Treeᵉ =
    equiv-node-equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( equiv-directed-tree-equiv-Enriched-Directed-Treeᵉ)

  node-equiv-Enriched-Directed-Treeᵉ :
    node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ → node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
  node-equiv-Enriched-Directed-Treeᵉ =
    node-equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( equiv-directed-tree-equiv-Enriched-Directed-Treeᵉ)

  equiv-edge-equiv-Enriched-Directed-Treeᵉ :
    (xᵉ yᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ) →
    edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ xᵉ yᵉ ≃ᵉ
    edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( node-equiv-Enriched-Directed-Treeᵉ xᵉ)
      ( node-equiv-Enriched-Directed-Treeᵉ yᵉ)
  equiv-edge-equiv-Enriched-Directed-Treeᵉ =
    equiv-edge-equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( equiv-directed-tree-equiv-Enriched-Directed-Treeᵉ)

  edge-equiv-Enriched-Directed-Treeᵉ :
    (xᵉ yᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ) →
    edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ xᵉ yᵉ →
    edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( node-equiv-Enriched-Directed-Treeᵉ xᵉ)
      ( node-equiv-Enriched-Directed-Treeᵉ yᵉ)
  edge-equiv-Enriched-Directed-Treeᵉ =
    edge-equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( equiv-directed-tree-equiv-Enriched-Directed-Treeᵉ)

  hom-directed-tree-equiv-Enriched-Directed-Treeᵉ :
    hom-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
  hom-directed-tree-equiv-Enriched-Directed-Treeᵉ =
    hom-equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( equiv-directed-tree-equiv-Enriched-Directed-Treeᵉ)

  equiv-direct-predecessor-equiv-Enriched-Directed-Treeᵉ :
    ( xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ) →
    Σᵉ ( node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( λ yᵉ → edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ yᵉ xᵉ) ≃ᵉ
    Σᵉ ( node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( λ yᵉ →
        edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ yᵉ
          ( node-equiv-Enriched-Directed-Treeᵉ xᵉ))
  equiv-direct-predecessor-equiv-Enriched-Directed-Treeᵉ =
    equiv-direct-predecessor-equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( equiv-directed-tree-equiv-Enriched-Directed-Treeᵉ)

  direct-predecessor-equiv-Enriched-Directed-Treeᵉ :
    ( xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ) →
    Σᵉ ( node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( λ yᵉ → edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ yᵉ xᵉ) →
    Σᵉ ( node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( λ yᵉ →
        edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ yᵉ
          ( node-equiv-Enriched-Directed-Treeᵉ xᵉ))
  direct-predecessor-equiv-Enriched-Directed-Treeᵉ =
    direct-predecessor-equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( equiv-directed-tree-equiv-Enriched-Directed-Treeᵉ)

  shape-equiv-Enriched-Directed-Treeᵉ :
    ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ) ~ᵉ
    ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ ∘ᵉ node-equiv-Enriched-Directed-Treeᵉ)
  shape-equiv-Enriched-Directed-Treeᵉ = pr1ᵉ (pr2ᵉ eᵉ)

  enrichment-equiv-Enriched-Directed-Treeᵉ :
    ( xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ) →
    ( ( direct-predecessor-equiv-Enriched-Directed-Treeᵉ xᵉ) ∘ᵉ
      ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ xᵉ)) ~ᵉ
    ( ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
        ( node-equiv-Directed-Treeᵉ
          ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
          ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
          ( equiv-directed-tree-equiv-Enriched-Directed-Treeᵉ)
          ( xᵉ))) ∘ᵉ
        ( trᵉ Bᵉ (shape-equiv-Enriched-Directed-Treeᵉ xᵉ)))
  enrichment-equiv-Enriched-Directed-Treeᵉ = pr2ᵉ (pr2ᵉ eᵉ)

  hom-equiv-Enriched-Directed-Treeᵉ :
    hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ
  pr1ᵉ hom-equiv-Enriched-Directed-Treeᵉ =
    hom-directed-tree-equiv-Enriched-Directed-Treeᵉ
  pr1ᵉ (pr2ᵉ hom-equiv-Enriched-Directed-Treeᵉ) =
    shape-equiv-Enriched-Directed-Treeᵉ
  pr2ᵉ (pr2ᵉ hom-equiv-Enriched-Directed-Treeᵉ) =
    enrichment-equiv-Enriched-Directed-Treeᵉ

  preserves-root-equiv-Enriched-Directed-Treeᵉ :
    preserves-root-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ
      hom-equiv-Enriched-Directed-Treeᵉ
  preserves-root-equiv-Enriched-Directed-Treeᵉ =
    preserves-root-equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( equiv-directed-tree-equiv-Enriched-Directed-Treeᵉ)

  rooted-hom-equiv-Enriched-Directed-Treeᵉ :
    rooted-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ
  pr1ᵉ rooted-hom-equiv-Enriched-Directed-Treeᵉ =
    hom-equiv-Enriched-Directed-Treeᵉ
  pr2ᵉ rooted-hom-equiv-Enriched-Directed-Treeᵉ =
    preserves-root-equiv-Enriched-Directed-Treeᵉ
```

### The identity equivalence of enriched directed trees

```agda
id-equiv-Enriched-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) →
  (Tᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ) →
  equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ Tᵉ
pr1ᵉ (id-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ) =
  id-equiv-Directed-Treeᵉ (directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
pr1ᵉ (pr2ᵉ (id-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)) = refl-htpyᵉ
pr2ᵉ (pr2ᵉ (id-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)) xᵉ = refl-htpyᵉ
```

### Composition of equivalences of enriched directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Rᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  (Sᵉ : Enriched-Directed-Treeᵉ l5ᵉ l6ᵉ Aᵉ Bᵉ)
  (Tᵉ : Enriched-Directed-Treeᵉ l7ᵉ l8ᵉ Aᵉ Bᵉ)
  (gᵉ : equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ)
  (fᵉ : equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ Sᵉ)
  where

  equiv-directed-tree-comp-equiv-Enriched-Directed-Treeᵉ :
    equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
  equiv-directed-tree-comp-equiv-Enriched-Directed-Treeᵉ =
    comp-equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( equiv-directed-tree-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ gᵉ)
      ( equiv-directed-tree-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ Sᵉ fᵉ)

  equiv-node-comp-equiv-Enriched-Directed-Treeᵉ :
    node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ ≃ᵉ
    node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
  equiv-node-comp-equiv-Enriched-Directed-Treeᵉ =
    equiv-node-equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( equiv-directed-tree-comp-equiv-Enriched-Directed-Treeᵉ)

  node-comp-equiv-Enriched-Directed-Treeᵉ :
    node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ →
    node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
  node-comp-equiv-Enriched-Directed-Treeᵉ =
    node-equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( equiv-directed-tree-comp-equiv-Enriched-Directed-Treeᵉ)

  equiv-edge-comp-equiv-Enriched-Directed-Treeᵉ :
    (xᵉ yᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ) →
    edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ xᵉ yᵉ ≃ᵉ
    edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( node-comp-equiv-Enriched-Directed-Treeᵉ xᵉ)
      ( node-comp-equiv-Enriched-Directed-Treeᵉ yᵉ)
  equiv-edge-comp-equiv-Enriched-Directed-Treeᵉ =
    equiv-edge-equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( equiv-directed-tree-comp-equiv-Enriched-Directed-Treeᵉ)

  edge-comp-equiv-Enriched-Directed-Treeᵉ :
    (xᵉ yᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ) →
    edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ xᵉ yᵉ →
    edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( node-comp-equiv-Enriched-Directed-Treeᵉ xᵉ)
      ( node-comp-equiv-Enriched-Directed-Treeᵉ yᵉ)
  edge-comp-equiv-Enriched-Directed-Treeᵉ =
    edge-equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( equiv-directed-tree-comp-equiv-Enriched-Directed-Treeᵉ)

  equiv-direct-predecessor-comp-equiv-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ) →
    direct-predecessor-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ xᵉ ≃ᵉ
    direct-predecessor-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( node-comp-equiv-Enriched-Directed-Treeᵉ xᵉ)
  equiv-direct-predecessor-comp-equiv-Enriched-Directed-Treeᵉ =
    equiv-direct-predecessor-equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( equiv-directed-tree-comp-equiv-Enriched-Directed-Treeᵉ)

  direct-predecessor-comp-equiv-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ) →
    direct-predecessor-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ xᵉ →
    direct-predecessor-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( node-comp-equiv-Enriched-Directed-Treeᵉ xᵉ)
  direct-predecessor-comp-equiv-Enriched-Directed-Treeᵉ =
    direct-predecessor-equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( equiv-directed-tree-comp-equiv-Enriched-Directed-Treeᵉ)

  shape-comp-equiv-Enriched-Directed-Treeᵉ :
    ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ) ~ᵉ
    ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ ∘ᵉ
      node-comp-equiv-Enriched-Directed-Treeᵉ)
  shape-comp-equiv-Enriched-Directed-Treeᵉ =
    concat-coherence-triangle-mapsᵉ
      ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ)
      ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( node-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ Sᵉ fᵉ)
      ( node-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ gᵉ)
      ( shape-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ Sᵉ fᵉ)
      ( shape-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ gᵉ)

  enrichment-comp-equiv-Enriched-Directed-Treeᵉ :
    ( xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ) →
    coherence-square-mapsᵉ
      ( trᵉ Bᵉ (shape-comp-equiv-Enriched-Directed-Treeᵉ xᵉ))
      ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ xᵉ)
      ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
        ( node-comp-equiv-Enriched-Directed-Treeᵉ xᵉ))
      ( direct-predecessor-comp-equiv-Enriched-Directed-Treeᵉ xᵉ)
  enrichment-comp-equiv-Enriched-Directed-Treeᵉ xᵉ =
    pasting-horizontal-up-to-htpy-coherence-square-mapsᵉ
      ( trᵉ Bᵉ (shape-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ Sᵉ fᵉ xᵉ))
      ( trᵉ Bᵉ
        ( shape-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ gᵉ
          ( node-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ Sᵉ fᵉ xᵉ)))
      ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ xᵉ)
      ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ
        ( node-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ Sᵉ fᵉ xᵉ))
      ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
        ( node-comp-equiv-Enriched-Directed-Treeᵉ xᵉ))
      ( direct-predecessor-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ Sᵉ fᵉ xᵉ)
      ( direct-predecessor-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ gᵉ
        ( node-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ Sᵉ fᵉ xᵉ))
      ( tr-concatᵉ
        ( shape-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ Sᵉ fᵉ xᵉ)
        ( shape-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ gᵉ
          ( node-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ Sᵉ fᵉ xᵉ)))
      ( refl-htpyᵉ)
      ( enrichment-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ Sᵉ fᵉ xᵉ)
      ( enrichment-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ gᵉ
        ( node-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ Sᵉ fᵉ xᵉ))

  comp-equiv-Enriched-Directed-Treeᵉ :
    equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Rᵉ Tᵉ
  pr1ᵉ comp-equiv-Enriched-Directed-Treeᵉ =
    equiv-directed-tree-comp-equiv-Enriched-Directed-Treeᵉ
  pr1ᵉ (pr2ᵉ comp-equiv-Enriched-Directed-Treeᵉ) =
    shape-comp-equiv-Enriched-Directed-Treeᵉ
  pr2ᵉ (pr2ᵉ comp-equiv-Enriched-Directed-Treeᵉ) =
    enrichment-comp-equiv-Enriched-Directed-Treeᵉ
```

### Homotopies of equivalences of enriched directed trees

```agda
htpy-equiv-Enriched-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) →
  (Sᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ) (Tᵉ : Enriched-Directed-Treeᵉ l5ᵉ l6ᵉ Aᵉ Bᵉ)
  (eᵉ fᵉ : equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
htpy-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ eᵉ fᵉ =
  htpy-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ
    ( hom-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ eᵉ)
    ( hom-equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ)
```

## Properties

### Equivalences characterize identifications of enriched directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Tᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  where

  extensionality-Enriched-Directed-Treeᵉ :
    (Sᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ) →
    (Tᵉ ＝ᵉ Sᵉ) ≃ᵉ equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ Sᵉ
  extensionality-Enriched-Directed-Treeᵉ =
    extensionality-Σᵉ
      ( λ {Sᵉ} (shᵉ ,ᵉ enrᵉ) eᵉ →
        Σᵉ ( ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ) ~ᵉ
            ( ( shᵉ) ∘ᵉ
              ( node-equiv-Directed-Treeᵉ
                ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
                ( Sᵉ)
                ( eᵉ))))
          ( λ Hᵉ →
            ( xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ) →
            ( ( direct-predecessor-equiv-Directed-Treeᵉ
                ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
                ( Sᵉ)
                ( eᵉ)
                ( xᵉ)) ∘ᵉ
              ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ)) ~ᵉ
            ( ( map-equivᵉ
                ( enrᵉ
                  ( node-equiv-Directed-Treeᵉ
                    ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
                    ( Sᵉ)
                    ( eᵉ)
                    ( xᵉ)))) ∘ᵉ
              ( trᵉ Bᵉ (Hᵉ xᵉ)))))
      ( id-equiv-Directed-Treeᵉ (directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ))
      ( ( refl-htpyᵉ) ,ᵉ
        ( λ xᵉ → refl-htpyᵉ))
      ( extensionality-Directed-Treeᵉ
        ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ))
      ( extensionality-Σᵉ
        ( λ {shᵉ} enrᵉ Hᵉ →
          ( xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ) →
          ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ) ~ᵉ
          ( map-equivᵉ (enrᵉ xᵉ) ∘ᵉ trᵉ Bᵉ (Hᵉ xᵉ)))
        ( refl-htpyᵉ)
        ( λ xᵉ → refl-htpyᵉ)
        ( λ shᵉ → equiv-funextᵉ)
        ( extensionality-Πᵉ
          ( enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
          ( λ xᵉ eᵉ →
            ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ) ~ᵉ
            ( map-equivᵉ eᵉ))
          ( λ xᵉ →
            extensionality-equivᵉ
            ( enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ xᵉ))))

  equiv-eq-Enriched-Directed-Treeᵉ :
    (Sᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ) →
    (Tᵉ ＝ᵉ Sᵉ) → equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ Sᵉ
  equiv-eq-Enriched-Directed-Treeᵉ Sᵉ =
    map-equivᵉ (extensionality-Enriched-Directed-Treeᵉ Sᵉ)

  eq-equiv-Enriched-Directed-Treeᵉ :
    (Sᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ) →
    equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ Sᵉ → Tᵉ ＝ᵉ Sᵉ
  eq-equiv-Enriched-Directed-Treeᵉ Sᵉ =
    map-inv-equivᵉ (extensionality-Enriched-Directed-Treeᵉ Sᵉ)

  is-torsorial-equiv-Enriched-Directed-Treeᵉ :
    is-torsorialᵉ (equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
  is-torsorial-equiv-Enriched-Directed-Treeᵉ =
    is-contr-equiv'ᵉ
      ( Σᵉ (Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ) (λ Sᵉ → Tᵉ ＝ᵉ Sᵉ))
      ( equiv-totᵉ extensionality-Enriched-Directed-Treeᵉ)
      ( is-torsorial-Idᵉ Tᵉ)
```

### A morphism of enriched directed trees is an equivalence if it is an equivalence on the nodes

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Sᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  (Tᵉ : Enriched-Directed-Treeᵉ l5ᵉ l6ᵉ Aᵉ Bᵉ)
  (fᵉ : hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ)
  where

  is-equiv-is-equiv-node-hom-Enriched-Directed-Treeᵉ :
    is-equivᵉ (node-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ) →
    is-equiv-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ
  is-equiv-is-equiv-node-hom-Enriched-Directed-Treeᵉ =
    is-equiv-is-equiv-node-hom-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( directed-tree-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ)
```