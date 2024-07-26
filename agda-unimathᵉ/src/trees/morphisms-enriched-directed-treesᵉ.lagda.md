# Morphisms of enriched directed trees

```agda
module trees.morphisms-enriched-directed-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import trees.enriched-directed-treesᵉ
open import trees.morphisms-directed-treesᵉ
```

</details>

## Idea

Aᵉ **morphismᵉ ofᵉ enrichedᵉ directedᵉ trees**ᵉ isᵉ aᵉ morphismᵉ ofᵉ directedᵉ treesᵉ thatᵉ
preservesᵉ theᵉ enrichmentᵉ structure.ᵉ

## Definitions

### Morphisms of enriched directed trees

```agda
hom-Enriched-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) →
  Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ → Enriched-Directed-Treeᵉ l5ᵉ l6ᵉ Aᵉ Bᵉ →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ =
  Σᵉ ( hom-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ))
    ( λ fᵉ →
      Σᵉ ( coherence-triangle-mapsᵉ
          ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
          ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
          ( node-hom-Directed-Treeᵉ
            ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
            ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
            ( fᵉ)))
        ( λ Hᵉ →
          ( xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ) →
          coherence-square-mapsᵉ
            ( trᵉ Bᵉ (Hᵉ xᵉ))
            ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ xᵉ)
            ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
              ( node-hom-Directed-Treeᵉ
                ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
                ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
                ( fᵉ)
                ( xᵉ)))
            ( direct-predecessor-hom-Directed-Treeᵉ
              ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
              ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
              ( fᵉ)
              ( xᵉ))))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Sᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ) (Tᵉ : Enriched-Directed-Treeᵉ l5ᵉ l6ᵉ Aᵉ Bᵉ)
  (fᵉ : hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ)
  where

  directed-tree-hom-Enriched-Directed-Treeᵉ :
    hom-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
  directed-tree-hom-Enriched-Directed-Treeᵉ = pr1ᵉ fᵉ

  node-hom-Enriched-Directed-Treeᵉ :
    node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ → node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
  node-hom-Enriched-Directed-Treeᵉ =
    node-hom-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( directed-tree-hom-Enriched-Directed-Treeᵉ)

  edge-hom-Enriched-Directed-Treeᵉ :
    {xᵉ yᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ} →
    edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ xᵉ yᵉ →
    edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( node-hom-Enriched-Directed-Treeᵉ xᵉ)
      ( node-hom-Enriched-Directed-Treeᵉ yᵉ)
  edge-hom-Enriched-Directed-Treeᵉ =
    edge-hom-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( directed-tree-hom-Enriched-Directed-Treeᵉ)

  direct-predecessor-hom-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ) →
    Σᵉ ( node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( λ yᵉ → edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ yᵉ xᵉ) →
    Σᵉ ( node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( λ yᵉ →
        edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ yᵉ
          ( node-hom-Enriched-Directed-Treeᵉ xᵉ))
  direct-predecessor-hom-Enriched-Directed-Treeᵉ =
    direct-predecessor-hom-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( directed-tree-hom-Enriched-Directed-Treeᵉ)

  shape-hom-Enriched-Directed-Treeᵉ :
    coherence-triangle-mapsᵉ
      ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
      ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( node-hom-Enriched-Directed-Treeᵉ)
  shape-hom-Enriched-Directed-Treeᵉ = pr1ᵉ (pr2ᵉ fᵉ)

  enrichment-hom-Enriched-Directed-Treeᵉ :
    ( xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ) →
    coherence-square-mapsᵉ
      ( trᵉ Bᵉ (shape-hom-Enriched-Directed-Treeᵉ xᵉ))
      ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ xᵉ)
      ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
        ( node-hom-Directed-Treeᵉ
          ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
          ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
          ( directed-tree-hom-Enriched-Directed-Treeᵉ)
          ( xᵉ)))
      ( direct-predecessor-hom-Enriched-Directed-Treeᵉ xᵉ)
  enrichment-hom-Enriched-Directed-Treeᵉ = pr2ᵉ (pr2ᵉ fᵉ)
```

### Homotopies of morphisms of enriched directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Sᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ) (Tᵉ : Enriched-Directed-Treeᵉ l5ᵉ l6ᵉ Aᵉ Bᵉ)
  (fᵉ gᵉ : hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ)
  where

  htpy-hom-Enriched-Directed-Treeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  htpy-hom-Enriched-Directed-Treeᵉ =
    Σᵉ ( htpy-hom-Directed-Treeᵉ
        ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
        ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
        ( directed-tree-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ)
        ( directed-tree-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ gᵉ))
      ( λ Hᵉ →
        Σᵉ ( ( ( shape-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ) ∙hᵉ
              ( ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ) ·lᵉ
                ( node-htpy-hom-Directed-Treeᵉ
                  ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
                  ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
                  ( directed-tree-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ)
                  ( directed-tree-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ gᵉ)
                  ( Hᵉ)))) ~ᵉ
            ( shape-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ gᵉ))
          ( λ Kᵉ →
            ( xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ) →
            ( ( ( totᵉ
                  ( λ yᵉ →
                    trᵉ
                      ( edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ yᵉ)
                      ( node-htpy-hom-Directed-Treeᵉ
                        ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
                        ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
                        ( directed-tree-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ)
                        ( directed-tree-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ gᵉ)
                        ( Hᵉ)
                        ( xᵉ)))) ·lᵉ
                ( enrichment-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ xᵉ)) ∙hᵉ
              ( ( ( coherence-square-map-enrichment-Enriched-Directed-Treeᵉ
                    Aᵉ Bᵉ Tᵉ (pr1ᵉ Hᵉ xᵉ)) ·rᵉ
                  ( trᵉ Bᵉ (shape-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ xᵉ))) ∙hᵉ
                ( λ bᵉ →
                  apᵉ
                    ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
                      ( node-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ gᵉ xᵉ))
                    ( ( invᵉ
                        ( tr-concatᵉ
                          ( shape-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ xᵉ)
                          ( apᵉ
                            ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
                            ( pr1ᵉ Hᵉ xᵉ))
                          ( bᵉ))) ∙ᵉ
                      ( apᵉ (λ qᵉ → trᵉ Bᵉ qᵉ bᵉ) (Kᵉ xᵉ)))))) ~ᵉ
            ( ( ( direct-predecessor-htpy-hom-Directed-Treeᵉ
                  ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ)
                  ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
                  ( directed-tree-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ fᵉ)
                  ( directed-tree-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ gᵉ)
                  ( Hᵉ)
                  ( xᵉ)) ·rᵉ
                ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ xᵉ)) ∙hᵉ
              ( enrichment-hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Sᵉ Tᵉ gᵉ xᵉ))))
```

### Identity morphisms of enriched directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Tᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  where

  id-hom-Enriched-Directed-Treeᵉ :
    hom-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ Tᵉ
  pr1ᵉ id-hom-Enriched-Directed-Treeᵉ =
    id-hom-Directed-Treeᵉ (directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
  pr1ᵉ (pr2ᵉ id-hom-Enriched-Directed-Treeᵉ) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ id-hom-Enriched-Directed-Treeᵉ) xᵉ = refl-htpyᵉ
```