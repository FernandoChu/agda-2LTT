# The underlying trees of elements of W-types

```agda
module trees.underlying-trees-of-elements-of-w-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.isolated-elementsᵉ
open import foundation.negated-equalityᵉ
open import foundation.propositionsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ
open import graph-theory.morphisms-directed-graphsᵉ
open import graph-theory.walks-directed-graphsᵉ

open import trees.combinator-directed-treesᵉ
open import trees.combinator-enriched-directed-treesᵉ
open import trees.directed-treesᵉ
open import trees.elementhood-relation-w-typesᵉ
open import trees.enriched-directed-treesᵉ
open import trees.equivalences-directed-treesᵉ
open import trees.equivalences-enriched-directed-treesᵉ
open import trees.underlying-trees-elements-coalgebras-polynomial-endofunctorsᵉ
open import trees.w-typesᵉ
```

</details>

## Idea

Theᵉ **underlyingᵉ (enrichedᵉ) directedᵉ tree**ᵉ ofᵉ anᵉ elementᵉ ofᵉ aᵉ W-typeᵉ isᵉ theᵉ
underlyingᵉ (enrichedᵉ) directedᵉ treeᵉ ofᵉ thatᵉ elementᵉ obtainedᵉ viaᵉ theᵉ coalgebraᵉ
structureᵉ ofᵉ `𝕎ᵉ Aᵉ B`.ᵉ

## Definitions

### The underlying enriched directed tree of an element of a W-type

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  enriched-directed-tree-element-𝕎ᵉ :
    𝕎ᵉ Aᵉ Bᵉ → Enriched-Directed-Treeᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l2ᵉ) Aᵉ Bᵉ
  enriched-directed-tree-element-𝕎ᵉ =
    enriched-directed-tree-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)
```

#### The underlying graph of an element of a W-type

```agda
  graph-element-𝕎ᵉ : 𝕎ᵉ Aᵉ Bᵉ → Directed-Graphᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
  graph-element-𝕎ᵉ = graph-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  external-graph-element-𝕎ᵉ : 𝕎ᵉ Aᵉ Bᵉ → Directed-Graphᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
  external-graph-element-𝕎ᵉ = external-graph-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  node-external-graph-element-𝕎ᵉ : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  node-external-graph-element-𝕎ᵉ =
    node-external-graph-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  edge-external-graph-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (xᵉ yᵉ : node-external-graph-element-𝕎ᵉ wᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  edge-external-graph-element-𝕎ᵉ =
    edge-external-graph-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  inclusion-graph-element-𝕎ᵉ :
    {uᵉ vᵉ : 𝕎ᵉ Aᵉ Bᵉ} → uᵉ ∈-𝕎ᵉ vᵉ →
    hom-Directed-Graphᵉ (graph-element-𝕎ᵉ uᵉ) (graph-element-𝕎ᵉ vᵉ)
  inclusion-graph-element-𝕎ᵉ = inclusion-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)
```

#### Nodes of the underlying directed tree of an element of a W-type

```agda
  node-element-𝕎ᵉ : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  node-element-𝕎ᵉ = node-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  node-inclusion-element-𝕎ᵉ :
    {uᵉ vᵉ : 𝕎ᵉ Aᵉ Bᵉ} → (uᵉ ∈-𝕎ᵉ vᵉ) → node-element-𝕎ᵉ uᵉ → node-element-𝕎ᵉ vᵉ
  node-inclusion-element-𝕎ᵉ = node-inclusion-element-coalgebraᵉ
```

#### The root of the underlying directed tree of an element of a W-type

```agda
  root-𝕎ᵉ : (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) → node-element-𝕎ᵉ wᵉ
  root-𝕎ᵉ = root-coalgebraᵉ

  is-root-node-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (xᵉ : node-element-𝕎ᵉ wᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-root-node-element-𝕎ᵉ = is-root-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  is-isolated-root-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) → is-isolatedᵉ (root-𝕎ᵉ wᵉ)
  is-isolated-root-element-𝕎ᵉ =
    is-isolated-root-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  is-contr-loop-space-root-graph-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) → is-contrᵉ (root-𝕎ᵉ wᵉ ＝ᵉ root-𝕎ᵉ wᵉ)
  is-contr-loop-space-root-graph-element-𝕎ᵉ =
    is-contr-loop-space-root-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)
```

#### The edges of the underlying directed tree of an element of a W-type

```agda
  edge-element-𝕎ᵉ : (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (xᵉ yᵉ : node-element-𝕎ᵉ wᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  edge-element-𝕎ᵉ = edge-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  edge-to-root-element-𝕎ᵉ :
    {uᵉ vᵉ : 𝕎ᵉ Aᵉ Bᵉ} (Hᵉ : uᵉ ∈-𝕎ᵉ vᵉ) →
    edge-element-𝕎ᵉ vᵉ
      ( node-inclusion-element-𝕎ᵉ Hᵉ (root-𝕎ᵉ uᵉ))
      ( root-𝕎ᵉ vᵉ)
  edge-to-root-element-𝕎ᵉ = edge-to-root-element-coalgebraᵉ

  edge-inclusion-element-𝕎ᵉ :
    {uᵉ vᵉ : 𝕎ᵉ Aᵉ Bᵉ} (Hᵉ : uᵉ ∈-𝕎ᵉ vᵉ) →
    {xᵉ yᵉ : node-element-𝕎ᵉ uᵉ} (eᵉ : edge-element-𝕎ᵉ uᵉ xᵉ yᵉ) →
    edge-element-𝕎ᵉ vᵉ
      ( node-inclusion-element-𝕎ᵉ Hᵉ xᵉ)
      ( node-inclusion-element-𝕎ᵉ Hᵉ yᵉ)
  edge-inclusion-element-𝕎ᵉ = edge-inclusion-element-coalgebraᵉ

  is-contr-edge-to-root-element-𝕎ᵉ :
    {uᵉ vᵉ : 𝕎ᵉ Aᵉ Bᵉ} (Hᵉ : uᵉ ∈-𝕎ᵉ vᵉ) →
    is-contrᵉ
      ( edge-element-𝕎ᵉ vᵉ
        ( node-inclusion-element-𝕎ᵉ Hᵉ (root-𝕎ᵉ uᵉ))
        ( root-𝕎ᵉ vᵉ))
  is-contr-edge-to-root-element-𝕎ᵉ =
    is-contr-edge-to-root-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  is-proof-irrelevant-edge-to-root-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (xᵉ : node-element-𝕎ᵉ wᵉ) →
    is-proof-irrelevantᵉ (edge-element-𝕎ᵉ wᵉ xᵉ (root-𝕎ᵉ wᵉ))
  is-proof-irrelevant-edge-to-root-element-𝕎ᵉ =
    is-proof-irrelevant-edge-to-root-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  is-prop-edge-to-root-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (xᵉ : node-element-𝕎ᵉ wᵉ) →
    is-propᵉ (edge-element-𝕎ᵉ wᵉ xᵉ (root-𝕎ᵉ wᵉ))
  is-prop-edge-to-root-element-𝕎ᵉ =
    is-prop-edge-to-root-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  no-edge-from-root-graph-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) →
    is-emptyᵉ (Σᵉ (node-element-𝕎ᵉ wᵉ) (edge-element-𝕎ᵉ wᵉ (root-𝕎ᵉ wᵉ)))
  no-edge-from-root-graph-element-𝕎ᵉ =
    no-edge-from-root-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  is-empty-eq-root-node-inclusion-element-𝕎ᵉ :
    {vᵉ wᵉ : 𝕎ᵉ Aᵉ Bᵉ} (Hᵉ : vᵉ ∈-𝕎ᵉ wᵉ) (xᵉ : node-element-𝕎ᵉ vᵉ) →
    root-𝕎ᵉ wᵉ ≠ᵉ node-inclusion-element-𝕎ᵉ Hᵉ xᵉ
  is-empty-eq-root-node-inclusion-element-𝕎ᵉ =
    is-empty-eq-root-node-inclusion-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)
```

#### The underlying directed tree of an element of a W-type

```agda
  directed-tree-element-𝕎ᵉ :
    𝕎ᵉ Aᵉ Bᵉ → Directed-Treeᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
  directed-tree-element-𝕎ᵉ =
    directed-tree-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  has-unique-predecessor-node-inclusion-element-𝕎ᵉ :
    {vᵉ wᵉ : 𝕎ᵉ Aᵉ Bᵉ} (Hᵉ : vᵉ ∈-𝕎ᵉ wᵉ) (xᵉ : node-element-𝕎ᵉ vᵉ) →
    is-contrᵉ
      ( Σᵉ ( node-element-𝕎ᵉ wᵉ)
          ( edge-element-𝕎ᵉ wᵉ (node-inclusion-element-𝕎ᵉ Hᵉ xᵉ)))
  has-unique-predecessor-node-inclusion-element-𝕎ᵉ =
    has-unique-predecessor-node-inclusion-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  has-unique-predecessor-graph-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (xᵉ : node-element-𝕎ᵉ wᵉ) →
    is-contrᵉ
      ((root-𝕎ᵉ wᵉ ＝ᵉ xᵉ) +ᵉ Σᵉ (node-element-𝕎ᵉ wᵉ) (edge-element-𝕎ᵉ wᵉ xᵉ))
  has-unique-predecessor-graph-element-𝕎ᵉ =
    has-unique-predecessor-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  walk-to-root-graph-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (xᵉ : node-element-𝕎ᵉ wᵉ) →
    walk-Directed-Graphᵉ (graph-element-𝕎ᵉ wᵉ) xᵉ (root-𝕎ᵉ wᵉ)
  walk-to-root-graph-element-𝕎ᵉ =
    walk-to-root-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  unique-walk-to-root-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) → is-tree-Directed-Graph'ᵉ (graph-element-𝕎ᵉ wᵉ) (root-𝕎ᵉ wᵉ)
  unique-walk-to-root-element-𝕎ᵉ =
    unique-walk-to-root-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)
```

#### The underlying directed tree of an element of a W-type is enriched

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  shape-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) → node-element-𝕎ᵉ wᵉ → Aᵉ
  shape-element-𝕎ᵉ =
    shape-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  map-enrichment-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (xᵉ : node-element-𝕎ᵉ wᵉ) →
    Bᵉ (shape-element-𝕎ᵉ wᵉ xᵉ) →
    Σᵉ (node-element-𝕎ᵉ wᵉ) (λ yᵉ → edge-element-𝕎ᵉ wᵉ yᵉ xᵉ)
  map-enrichment-element-𝕎ᵉ =
    map-enrichment-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  map-inv-enrichment-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (xᵉ : node-element-𝕎ᵉ wᵉ) →
    Σᵉ (node-element-𝕎ᵉ wᵉ) (λ yᵉ → edge-element-𝕎ᵉ wᵉ yᵉ xᵉ) →
    Bᵉ (shape-element-𝕎ᵉ wᵉ xᵉ)
  map-inv-enrichment-element-𝕎ᵉ =
    map-inv-enrichment-directed-tree-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  is-section-map-inv-enrichment-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (xᵉ : node-element-𝕎ᵉ wᵉ) →
    ( map-enrichment-element-𝕎ᵉ wᵉ xᵉ ∘ᵉ
      map-inv-enrichment-element-𝕎ᵉ wᵉ xᵉ) ~ᵉ idᵉ
  is-section-map-inv-enrichment-element-𝕎ᵉ =
    is-section-map-inv-enrichment-directed-tree-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  is-retraction-map-inv-enrichment-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (xᵉ : node-element-𝕎ᵉ wᵉ) →
    ( map-inv-enrichment-element-𝕎ᵉ wᵉ xᵉ ∘ᵉ
      map-enrichment-element-𝕎ᵉ wᵉ xᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-enrichment-element-𝕎ᵉ =
    is-retraction-map-inv-enrichment-directed-tree-element-coalgebraᵉ
      ( 𝕎-Coalgᵉ Aᵉ Bᵉ)

  is-equiv-map-enrichment-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (xᵉ : node-element-𝕎ᵉ wᵉ) →
    is-equivᵉ (map-enrichment-element-𝕎ᵉ wᵉ xᵉ)
  is-equiv-map-enrichment-element-𝕎ᵉ =
    is-equiv-map-enrichment-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  enrichment-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (xᵉ : node-element-𝕎ᵉ wᵉ) →
    Bᵉ (shape-element-𝕎ᵉ wᵉ xᵉ) ≃ᵉ
    Σᵉ (node-element-𝕎ᵉ wᵉ) (λ yᵉ → edge-element-𝕎ᵉ wᵉ yᵉ xᵉ)
  enrichment-element-𝕎ᵉ =
    enrichment-directed-tree-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)
```

## Properties

### Characterization of equality of the type of nodes of the underlying graph of an element of `𝕎 A B`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  Eq-node-element-𝕎ᵉ : (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (xᵉ yᵉ : node-element-𝕎ᵉ wᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  Eq-node-element-𝕎ᵉ = Eq-node-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  root-refl-Eq-node-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) → Eq-node-element-𝕎ᵉ wᵉ (root-𝕎ᵉ wᵉ) (root-𝕎ᵉ wᵉ)
  root-refl-Eq-node-element-𝕎ᵉ wᵉ = root-refl-Eq-node-element-coalgebraᵉ

  node-inclusion-Eq-node-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) {uᵉ : 𝕎ᵉ Aᵉ Bᵉ} (Hᵉ : uᵉ ∈-𝕎ᵉ wᵉ) {xᵉ yᵉ : node-element-𝕎ᵉ uᵉ} →
    Eq-node-element-𝕎ᵉ uᵉ xᵉ yᵉ →
    Eq-node-element-𝕎ᵉ wᵉ
      ( node-inclusion-element-𝕎ᵉ Hᵉ xᵉ)
      ( node-inclusion-element-𝕎ᵉ Hᵉ yᵉ)
  node-inclusion-Eq-node-element-𝕎ᵉ wᵉ =
    node-inclusion-Eq-node-element-coalgebraᵉ

  refl-Eq-node-element-𝕎ᵉ :
    {wᵉ : 𝕎ᵉ Aᵉ Bᵉ} (xᵉ : node-element-𝕎ᵉ wᵉ) →
    Eq-node-element-𝕎ᵉ wᵉ xᵉ xᵉ
  refl-Eq-node-element-𝕎ᵉ = refl-Eq-node-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  is-torsorial-Eq-node-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (xᵉ : node-element-𝕎ᵉ wᵉ) →
    is-torsorialᵉ (Eq-node-element-𝕎ᵉ wᵉ xᵉ)
  is-torsorial-Eq-node-element-𝕎ᵉ =
    is-torsorial-Eq-node-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  Eq-eq-node-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) {xᵉ yᵉ : node-element-𝕎ᵉ wᵉ} →
    xᵉ ＝ᵉ yᵉ → Eq-node-element-𝕎ᵉ wᵉ xᵉ yᵉ
  Eq-eq-node-element-𝕎ᵉ = Eq-eq-node-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  is-equiv-Eq-eq-node-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (xᵉ yᵉ : node-element-𝕎ᵉ wᵉ) →
    is-equivᵉ (Eq-eq-node-element-𝕎ᵉ wᵉ {xᵉ} {yᵉ})
  is-equiv-Eq-eq-node-element-𝕎ᵉ =
    is-equiv-Eq-eq-node-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  extensionality-node-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (xᵉ yᵉ : node-element-𝕎ᵉ wᵉ) →
    (xᵉ ＝ᵉ yᵉ) ≃ᵉ Eq-node-element-𝕎ᵉ wᵉ xᵉ yᵉ
  extensionality-node-element-𝕎ᵉ =
    extensionality-node-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)

  eq-Eq-node-element-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (xᵉ yᵉ : node-element-𝕎ᵉ wᵉ) →
    Eq-node-element-𝕎ᵉ wᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  eq-Eq-node-element-𝕎ᵉ =
    eq-Eq-node-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ)
```

### The underlying tree of `tree-𝕎 a α` is the combinator tree of the underlying trees of `α b` indexed by `b : B a`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (wᵉ : 𝕎ᵉ Aᵉ Bᵉ)
  where

  node-compute-directed-tree-element-𝕎ᵉ :
    node-element-𝕎ᵉ wᵉ →
    node-combinator-Directed-Treeᵉ
      ( λ bᵉ → directed-tree-element-𝕎ᵉ (component-𝕎ᵉ wᵉ bᵉ))
  node-compute-directed-tree-element-𝕎ᵉ =
    node-compute-directed-tree-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ) wᵉ

  map-inv-node-compute-directed-tree-element-𝕎ᵉ :
    node-combinator-Directed-Treeᵉ
      ( λ bᵉ → directed-tree-element-𝕎ᵉ (component-𝕎ᵉ wᵉ bᵉ)) →
    node-element-𝕎ᵉ wᵉ
  map-inv-node-compute-directed-tree-element-𝕎ᵉ =
    map-inv-node-compute-directed-tree-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ) wᵉ

  is-section-map-inv-node-compute-directed-tree-element-𝕎ᵉ :
    ( node-compute-directed-tree-element-𝕎ᵉ ∘ᵉ
      map-inv-node-compute-directed-tree-element-𝕎ᵉ) ~ᵉ idᵉ
  is-section-map-inv-node-compute-directed-tree-element-𝕎ᵉ =
    is-section-map-inv-node-compute-directed-tree-element-coalgebraᵉ
      ( 𝕎-Coalgᵉ Aᵉ Bᵉ)
      ( wᵉ)

  is-retraction-map-inv-node-compute-directed-tree-element-𝕎ᵉ :
    ( map-inv-node-compute-directed-tree-element-𝕎ᵉ ∘ᵉ
      node-compute-directed-tree-element-𝕎ᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-node-compute-directed-tree-element-𝕎ᵉ =
    is-retraction-map-inv-node-compute-directed-tree-element-coalgebraᵉ
      ( 𝕎-Coalgᵉ Aᵉ Bᵉ)
      ( wᵉ)

  is-equiv-node-compute-directed-tree-element-𝕎ᵉ :
    is-equivᵉ node-compute-directed-tree-element-𝕎ᵉ
  is-equiv-node-compute-directed-tree-element-𝕎ᵉ =
    is-equiv-node-compute-directed-tree-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ) wᵉ

  equiv-node-compute-directed-tree-element-𝕎ᵉ :
    node-element-𝕎ᵉ wᵉ ≃ᵉ
    node-combinator-Directed-Treeᵉ
      ( λ bᵉ → directed-tree-element-𝕎ᵉ (component-𝕎ᵉ wᵉ bᵉ))
  equiv-node-compute-directed-tree-element-𝕎ᵉ =
    equiv-node-compute-directed-tree-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ) wᵉ

  edge-compute-directed-tree-element-𝕎ᵉ :
    (xᵉ yᵉ : node-element-𝕎ᵉ wᵉ) →
    edge-element-𝕎ᵉ wᵉ xᵉ yᵉ →
    edge-combinator-Directed-Treeᵉ
      ( λ bᵉ → directed-tree-element-𝕎ᵉ (component-𝕎ᵉ wᵉ bᵉ))
      ( node-compute-directed-tree-element-𝕎ᵉ xᵉ)
      ( node-compute-directed-tree-element-𝕎ᵉ yᵉ)
  edge-compute-directed-tree-element-𝕎ᵉ =
    edge-compute-directed-tree-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ) wᵉ

  map-inv-edge-compute-directed-tree-element-𝕎ᵉ :
    ( xᵉ yᵉ : node-element-𝕎ᵉ wᵉ) →
    edge-combinator-Directed-Treeᵉ
      ( λ bᵉ → directed-tree-element-𝕎ᵉ (component-𝕎ᵉ wᵉ bᵉ))
      ( node-compute-directed-tree-element-𝕎ᵉ xᵉ)
      ( node-compute-directed-tree-element-𝕎ᵉ yᵉ) →
    edge-element-𝕎ᵉ wᵉ xᵉ yᵉ
  map-inv-edge-compute-directed-tree-element-𝕎ᵉ =
    map-inv-edge-compute-directed-tree-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ) wᵉ

  is-section-map-inv-edge-compute-directed-tree-element-𝕎ᵉ :
    (xᵉ yᵉ : node-element-𝕎ᵉ wᵉ) →
    ( eᵉ :
      edge-combinator-Directed-Treeᵉ
        ( λ bᵉ → directed-tree-element-𝕎ᵉ (component-𝕎ᵉ wᵉ bᵉ))
        ( node-compute-directed-tree-element-𝕎ᵉ xᵉ)
        ( node-compute-directed-tree-element-𝕎ᵉ yᵉ)) →
    edge-compute-directed-tree-element-𝕎ᵉ xᵉ yᵉ
      ( map-inv-edge-compute-directed-tree-element-𝕎ᵉ xᵉ yᵉ eᵉ) ＝ᵉ eᵉ
  is-section-map-inv-edge-compute-directed-tree-element-𝕎ᵉ =
    is-section-map-inv-edge-compute-directed-tree-element-coalgebraᵉ
      ( 𝕎-Coalgᵉ Aᵉ Bᵉ)
      ( wᵉ)

  is-retraction-map-inv-edge-compute-directed-tree-element-𝕎ᵉ :
    (xᵉ yᵉ : node-element-𝕎ᵉ wᵉ) (eᵉ : edge-element-𝕎ᵉ wᵉ xᵉ yᵉ) →
    map-inv-edge-compute-directed-tree-element-𝕎ᵉ xᵉ yᵉ
      ( edge-compute-directed-tree-element-𝕎ᵉ xᵉ yᵉ eᵉ) ＝ᵉ eᵉ
  is-retraction-map-inv-edge-compute-directed-tree-element-𝕎ᵉ =
    is-retraction-map-inv-edge-compute-directed-tree-element-coalgebraᵉ
      ( 𝕎-Coalgᵉ Aᵉ Bᵉ)
      ( wᵉ)

  is-equiv-edge-compute-directed-tree-element-𝕎ᵉ :
    (xᵉ yᵉ : node-element-𝕎ᵉ wᵉ) →
    is-equivᵉ (edge-compute-directed-tree-element-𝕎ᵉ xᵉ yᵉ)
  is-equiv-edge-compute-directed-tree-element-𝕎ᵉ =
    is-equiv-edge-compute-directed-tree-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ) wᵉ

  equiv-edge-compute-directed-tree-element-𝕎ᵉ :
    (xᵉ yᵉ : node-element-𝕎ᵉ wᵉ) →
    edge-element-𝕎ᵉ wᵉ xᵉ yᵉ ≃ᵉ
    edge-combinator-Directed-Treeᵉ
      ( λ bᵉ → directed-tree-element-𝕎ᵉ (component-𝕎ᵉ wᵉ bᵉ))
      ( node-compute-directed-tree-element-𝕎ᵉ xᵉ)
      ( node-compute-directed-tree-element-𝕎ᵉ yᵉ)
  equiv-edge-compute-directed-tree-element-𝕎ᵉ =
    equiv-edge-compute-directed-tree-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ) wᵉ

  compute-directed-tree-element-𝕎ᵉ :
    equiv-Directed-Treeᵉ
      ( directed-tree-element-𝕎ᵉ wᵉ)
      ( combinator-Directed-Treeᵉ
        ( λ bᵉ → directed-tree-element-𝕎ᵉ (component-𝕎ᵉ wᵉ bᵉ)))
  compute-directed-tree-element-𝕎ᵉ =
    compute-directed-tree-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ) wᵉ

  shape-compute-enriched-directed-tree-element-𝕎ᵉ :
    shape-element-𝕎ᵉ wᵉ ~ᵉ
    ( ( shape-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
        ( λ bᵉ → enriched-directed-tree-element-𝕎ᵉ (component-𝕎ᵉ wᵉ bᵉ))) ∘ᵉ
      ( node-compute-directed-tree-element-𝕎ᵉ))
  shape-compute-enriched-directed-tree-element-𝕎ᵉ =
    shape-compute-enriched-directed-tree-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ) wᵉ

  enrichment-compute-enriched-directed-tree-element-𝕎ᵉ :
    (xᵉ : node-element-𝕎ᵉ wᵉ) →
    htpy-equivᵉ
      ( ( equiv-direct-predecessor-equiv-Directed-Treeᵉ
          ( directed-tree-element-𝕎ᵉ wᵉ)
          ( combinator-Directed-Treeᵉ
            ( λ bᵉ → directed-tree-element-𝕎ᵉ (component-𝕎ᵉ wᵉ bᵉ)))
          ( compute-directed-tree-element-𝕎ᵉ)
          ( xᵉ)) ∘eᵉ
        ( enrichment-element-𝕎ᵉ wᵉ xᵉ))
      ( ( enrichment-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
          ( λ bᵉ → enriched-directed-tree-element-𝕎ᵉ (component-𝕎ᵉ wᵉ bᵉ))
          ( node-compute-directed-tree-element-𝕎ᵉ xᵉ)) ∘eᵉ
        ( equiv-trᵉ Bᵉ
          ( shape-compute-enriched-directed-tree-element-𝕎ᵉ xᵉ)))
  enrichment-compute-enriched-directed-tree-element-𝕎ᵉ =
    enrichment-compute-enriched-directed-tree-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ) wᵉ

  compute-enriched-directed-tree-element-𝕎ᵉ :
    equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
      ( enriched-directed-tree-element-𝕎ᵉ wᵉ)
      ( combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
        ( λ bᵉ → enriched-directed-tree-element-𝕎ᵉ (component-𝕎ᵉ wᵉ bᵉ)))
  compute-enriched-directed-tree-element-𝕎ᵉ =
    compute-enriched-directed-tree-element-coalgebraᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ) wᵉ
```