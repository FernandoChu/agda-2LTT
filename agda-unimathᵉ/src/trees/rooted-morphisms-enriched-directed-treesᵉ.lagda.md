# Rooted morphisms of enriched directed trees

```agda
module trees.rooted-morphisms-enriched-directed-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import trees.enriched-directed-treesᵉ
open import trees.morphisms-enriched-directed-treesᵉ
open import trees.rooted-morphisms-directed-treesᵉ
```

</details>

## Idea

**Rootedᵉ morphismsᵉ ofᵉ enrichedᵉ directedᵉ trees**ᵉ areᵉ rootᵉ preservingᵉ morphismsᵉ ofᵉ
enrichedᵉ directedᵉ trees.ᵉ

## Definitions

### Rooted morphisms of directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Sᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  (Tᵉ : Enriched-Directed-Treeᵉ l5ᵉ l6ᵉ Aᵉ Bᵉ)
  where

  preserves-root-hom-enriched-directed-tree-Propᵉ :
    hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ → Propᵉ l5ᵉ
  preserves-root-hom-enriched-directed-tree-Propᵉ fᵉ =
    preserves-root-hom-directed-tree-Propᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( directed-tree-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ)

  preserves-root-hom-Enriched-Directed-Treeᵉ :
    hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ → UUᵉ l5ᵉ
  preserves-root-hom-Enriched-Directed-Treeᵉ fᵉ =
    preserves-root-hom-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( directed-tree-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ)

  is-prop-preserves-root-hom-Enriched-Directed-Treeᵉ :
    (fᵉ : hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ) →
    is-propᵉ (preserves-root-hom-Enriched-Directed-Treeᵉ fᵉ)
  is-prop-preserves-root-hom-Enriched-Directed-Treeᵉ fᵉ =
    is-prop-preserves-root-hom-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( directed-tree-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ)

  rooted-hom-Enriched-Directed-Treeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  rooted-hom-Enriched-Directed-Treeᵉ =
    Σᵉ ( hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ)
      ( preserves-root-hom-Enriched-Directed-Treeᵉ)

  module _
    (fᵉ : rooted-hom-Enriched-Directed-Treeᵉ)
    where

    hom-rooted-hom-Enriched-Directed-Treeᵉ : hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ
    hom-rooted-hom-Enriched-Directed-Treeᵉ = pr1ᵉ fᵉ

    node-rooted-hom-Enriched-Directed-Treeᵉ :
      node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ → node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
    node-rooted-hom-Enriched-Directed-Treeᵉ =
      node-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ
        ( hom-rooted-hom-Enriched-Directed-Treeᵉ)

    edge-rooted-hom-Enriched-Directed-Treeᵉ :
      {xᵉ yᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ} →
      edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ xᵉ yᵉ →
      edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
        ( node-rooted-hom-Enriched-Directed-Treeᵉ xᵉ)
        ( node-rooted-hom-Enriched-Directed-Treeᵉ yᵉ)
    edge-rooted-hom-Enriched-Directed-Treeᵉ =
      edge-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ
        ( hom-rooted-hom-Enriched-Directed-Treeᵉ)

    direct-predecessor-rooted-hom-Enriched-Directed-Treeᵉ :
      (xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ) →
      Σᵉ ( node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
        ( λ yᵉ → edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ yᵉ xᵉ) →
      Σᵉ ( node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
        ( λ yᵉ →
          edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ yᵉ
            ( node-rooted-hom-Enriched-Directed-Treeᵉ xᵉ))
    direct-predecessor-rooted-hom-Enriched-Directed-Treeᵉ =
      direct-predecessor-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ
        ( hom-rooted-hom-Enriched-Directed-Treeᵉ)

    shape-rooted-hom-Enriched-Directed-Treeᵉ :
      ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ) ~ᵉ
      ( ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ) ∘ᵉ
        ( node-rooted-hom-Enriched-Directed-Treeᵉ))
    shape-rooted-hom-Enriched-Directed-Treeᵉ =
      shape-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ
        ( hom-rooted-hom-Enriched-Directed-Treeᵉ)

    enrichment-rooted-hom-Enriched-Directed-Treeᵉ :
      ( xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ) →
      ( ( direct-predecessor-rooted-hom-Enriched-Directed-Treeᵉ xᵉ) ∘ᵉ
        ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ xᵉ)) ~ᵉ
      ( ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
          ( node-rooted-hom-Enriched-Directed-Treeᵉ xᵉ)) ∘ᵉ
          ( trᵉ Bᵉ (shape-rooted-hom-Enriched-Directed-Treeᵉ xᵉ)))
    enrichment-rooted-hom-Enriched-Directed-Treeᵉ =
      enrichment-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ
        ( hom-rooted-hom-Enriched-Directed-Treeᵉ)

    preserves-root-rooted-hom-Enriched-Directed-Treeᵉ :
      preserves-root-hom-Enriched-Directed-Treeᵉ
        hom-rooted-hom-Enriched-Directed-Treeᵉ
    preserves-root-rooted-hom-Enriched-Directed-Treeᵉ = pr2ᵉ fᵉ
```

### The identity rooted morphism of directed trees

```agda
id-rooted-hom-Enriched-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Tᵉ : Enriched-Directed-Treeᵉ l1ᵉ l2ᵉ Aᵉ Bᵉ) →
  rooted-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ Tᵉ
pr1ᵉ (id-rooted-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ) =
  id-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
pr2ᵉ (id-rooted-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ) = reflᵉ
```