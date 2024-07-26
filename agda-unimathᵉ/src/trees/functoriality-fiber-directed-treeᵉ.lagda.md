# Functoriality of the fiber operation on directed trees

```agda
module trees.functoriality-fiber-directed-treeᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.walks-directed-graphsᵉ

open import trees.directed-treesᵉ
open import trees.equivalences-directed-treesᵉ
open import trees.fibers-directed-treesᵉ
open import trees.morphisms-directed-treesᵉ
```

</details>

## Idea

Anyᵉ morphismᵉ `fᵉ : Sᵉ → T`ᵉ ofᵉ directedᵉ treesᵉ inducesᵉ forᵉ anyᵉ nodeᵉ `xᵉ ∈ᵉ S`ᵉ aᵉ
morphismᵉ ofᵉ fibersᵉ ofᵉ directedᵉ trees.ᵉ

## Definitions

### The action on fibers of morphisms of directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ)
  (fᵉ : hom-Directed-Treeᵉ Sᵉ Tᵉ) (xᵉ : node-Directed-Treeᵉ Sᵉ)
  where

  node-fiber-hom-Directed-Treeᵉ :
    node-fiber-Directed-Treeᵉ Sᵉ xᵉ →
    node-fiber-Directed-Treeᵉ Tᵉ (node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ)
  node-fiber-hom-Directed-Treeᵉ =
    map-Σᵉ
      ( λ yᵉ → walk-Directed-Treeᵉ Tᵉ yᵉ (node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ))
      ( node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
      ( λ yᵉ → walk-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ {yᵉ} {xᵉ})

  edge-fiber-hom-Directed-Treeᵉ :
    (yᵉ zᵉ : node-fiber-Directed-Treeᵉ Sᵉ xᵉ) →
    edge-fiber-Directed-Treeᵉ Sᵉ xᵉ yᵉ zᵉ →
    edge-fiber-Directed-Treeᵉ Tᵉ
      ( node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ)
      ( node-fiber-hom-Directed-Treeᵉ yᵉ)
      ( node-fiber-hom-Directed-Treeᵉ zᵉ)
  edge-fiber-hom-Directed-Treeᵉ (yᵉ ,ᵉ vᵉ) (zᵉ ,ᵉ wᵉ) =
    map-Σᵉ
      ( λ eᵉ →
        walk-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ vᵉ ＝ᵉ
        cons-walk-Directed-Graphᵉ eᵉ (walk-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ wᵉ))
      ( edge-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
      ( λ eᵉ → apᵉ (walk-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ))

  fiber-hom-Directed-Treeᵉ :
    hom-Directed-Treeᵉ
      ( fiber-Directed-Treeᵉ Sᵉ xᵉ)
      ( fiber-Directed-Treeᵉ Tᵉ (node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ))
  pr1ᵉ fiber-hom-Directed-Treeᵉ = node-fiber-hom-Directed-Treeᵉ
  pr2ᵉ fiber-hom-Directed-Treeᵉ = edge-fiber-hom-Directed-Treeᵉ
```

### The action on fibers of equivalences of directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ)
  (fᵉ : equiv-Directed-Treeᵉ Sᵉ Tᵉ) (xᵉ : node-Directed-Treeᵉ Sᵉ)
  where

  equiv-node-fiber-equiv-Directed-Treeᵉ :
    node-fiber-Directed-Treeᵉ Sᵉ xᵉ ≃ᵉ
    node-fiber-Directed-Treeᵉ Tᵉ (node-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ)
  equiv-node-fiber-equiv-Directed-Treeᵉ =
    equiv-Σᵉ
      ( λ yᵉ → walk-Directed-Treeᵉ Tᵉ yᵉ (node-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ))
      ( equiv-node-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
      ( λ yᵉ → equiv-walk-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ {yᵉ} {xᵉ})

  node-fiber-equiv-Directed-Treeᵉ :
    node-fiber-Directed-Treeᵉ Sᵉ xᵉ →
    node-fiber-Directed-Treeᵉ Tᵉ (node-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ)
  node-fiber-equiv-Directed-Treeᵉ =
    map-equivᵉ equiv-node-fiber-equiv-Directed-Treeᵉ

  equiv-edge-fiber-equiv-Directed-Treeᵉ :
    (yᵉ zᵉ : node-fiber-Directed-Treeᵉ Sᵉ xᵉ) →
    edge-fiber-Directed-Treeᵉ Sᵉ xᵉ yᵉ zᵉ ≃ᵉ
    edge-fiber-Directed-Treeᵉ Tᵉ
      ( node-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ)
      ( node-fiber-equiv-Directed-Treeᵉ yᵉ)
      ( node-fiber-equiv-Directed-Treeᵉ zᵉ)
  equiv-edge-fiber-equiv-Directed-Treeᵉ (yᵉ ,ᵉ vᵉ) (zᵉ ,ᵉ wᵉ) =
    equiv-Σᵉ
      ( λ eᵉ →
        walk-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ vᵉ ＝ᵉ
        cons-walk-Directed-Graphᵉ eᵉ (walk-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ wᵉ))
      ( equiv-edge-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ yᵉ zᵉ)
      ( λ eᵉ →
        equiv-apᵉ
          ( equiv-walk-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
          ( vᵉ)
          ( cons-walk-Directed-Graphᵉ eᵉ wᵉ))

  edge-fiber-equiv-Directed-Treeᵉ :
    (yᵉ zᵉ : node-fiber-Directed-Treeᵉ Sᵉ xᵉ) →
    edge-fiber-Directed-Treeᵉ Sᵉ xᵉ yᵉ zᵉ →
    edge-fiber-Directed-Treeᵉ Tᵉ
      ( node-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ)
      ( node-fiber-equiv-Directed-Treeᵉ yᵉ)
      ( node-fiber-equiv-Directed-Treeᵉ zᵉ)
  edge-fiber-equiv-Directed-Treeᵉ yᵉ zᵉ =
    map-equivᵉ (equiv-edge-fiber-equiv-Directed-Treeᵉ yᵉ zᵉ)

  fiber-equiv-Directed-Treeᵉ :
    equiv-Directed-Treeᵉ
      ( fiber-Directed-Treeᵉ Sᵉ xᵉ)
      ( fiber-Directed-Treeᵉ Tᵉ (node-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ))
  pr1ᵉ fiber-equiv-Directed-Treeᵉ =
    equiv-node-fiber-equiv-Directed-Treeᵉ
  pr2ᵉ fiber-equiv-Directed-Treeᵉ =
    equiv-edge-fiber-equiv-Directed-Treeᵉ
```