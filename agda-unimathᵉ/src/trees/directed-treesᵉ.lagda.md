# Directed trees

```agda
module trees.directed-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.isolated-elementsᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ
open import graph-theory.walks-directed-graphsᵉ
```

</details>

## Idea

Aᵉ **directedᵉ tree**ᵉ isᵉ aᵉ directedᵉ graphᵉ `G`ᵉ equippedᵉ with aᵉ roodᵉ `rᵉ : G`ᵉ suchᵉ
thatᵉ forᵉ everyᵉ vertexᵉ `xᵉ : G`ᵉ theᵉ typeᵉ ofᵉ walksᵉ fromᵉ `x`ᵉ to `r`ᵉ isᵉ contractible.ᵉ

## Definition

```agda
is-tree-Directed-Graph-Prop'ᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (rᵉ : vertex-Directed-Graphᵉ Gᵉ) →
  Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-tree-Directed-Graph-Prop'ᵉ Gᵉ rᵉ =
  Π-Propᵉ
    ( vertex-Directed-Graphᵉ Gᵉ)
    ( λ xᵉ → is-contr-Propᵉ (walk-Directed-Graphᵉ Gᵉ xᵉ rᵉ))

is-tree-Directed-Graph'ᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (rᵉ : vertex-Directed-Graphᵉ Gᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-tree-Directed-Graph'ᵉ Gᵉ rᵉ = type-Propᵉ (is-tree-Directed-Graph-Prop'ᵉ Gᵉ rᵉ)

is-prop-is-tree-Directed-Graph'ᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (rᵉ : vertex-Directed-Graphᵉ Gᵉ) →
  is-propᵉ (is-tree-Directed-Graph'ᵉ Gᵉ rᵉ)
is-prop-is-tree-Directed-Graph'ᵉ Gᵉ rᵉ =
  is-prop-type-Propᵉ (is-tree-Directed-Graph-Prop'ᵉ Gᵉ rᵉ)

is-tree-Directed-Graphᵉ :
  {l1ᵉ l2ᵉ : Level} → Directed-Graphᵉ l1ᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-tree-Directed-Graphᵉ Gᵉ =
  Σᵉ ( vertex-Directed-Graphᵉ Gᵉ)
    ( λ rᵉ → is-tree-Directed-Graph'ᵉ Gᵉ rᵉ)

Directed-Treeᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Directed-Treeᵉ l1ᵉ l2ᵉ =
  Σᵉ ( Directed-Graphᵉ l1ᵉ l2ᵉ) is-tree-Directed-Graphᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ)
  where

  graph-Directed-Treeᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ
  graph-Directed-Treeᵉ = pr1ᵉ Tᵉ

  node-Directed-Treeᵉ : UUᵉ l1ᵉ
  node-Directed-Treeᵉ = vertex-Directed-Graphᵉ graph-Directed-Treeᵉ

  edge-Directed-Treeᵉ : (xᵉ yᵉ : node-Directed-Treeᵉ) → UUᵉ l2ᵉ
  edge-Directed-Treeᵉ = edge-Directed-Graphᵉ graph-Directed-Treeᵉ

  direct-predecessor-Directed-Treeᵉ : node-Directed-Treeᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  direct-predecessor-Directed-Treeᵉ xᵉ =
    Σᵉ node-Directed-Treeᵉ (λ yᵉ → edge-Directed-Treeᵉ yᵉ xᵉ)

  node-direct-predecessor-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ) →
    direct-predecessor-Directed-Treeᵉ xᵉ → node-Directed-Treeᵉ
  node-direct-predecessor-Directed-Treeᵉ xᵉ = pr1ᵉ

  edge-direct-predecessor-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ) (yᵉ : direct-predecessor-Directed-Treeᵉ xᵉ) →
    edge-Directed-Treeᵉ (node-direct-predecessor-Directed-Treeᵉ xᵉ yᵉ) xᵉ
  edge-direct-predecessor-Directed-Treeᵉ xᵉ = pr2ᵉ

  walk-Directed-Treeᵉ : (xᵉ yᵉ : node-Directed-Treeᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  walk-Directed-Treeᵉ = walk-Directed-Graphᵉ graph-Directed-Treeᵉ

  walk-Directed-Tree'ᵉ : (xᵉ yᵉ : node-Directed-Treeᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  walk-Directed-Tree'ᵉ = walk-Directed-Graph'ᵉ graph-Directed-Treeᵉ

  compute-walk-Directed-Treeᵉ :
    (xᵉ yᵉ : node-Directed-Treeᵉ) →
    walk-Directed-Treeᵉ xᵉ yᵉ ≃ᵉ walk-Directed-Tree'ᵉ xᵉ yᵉ
  compute-walk-Directed-Treeᵉ =
    compute-walk-Directed-Graphᵉ graph-Directed-Treeᵉ

  refl-walk-Directed-Treeᵉ :
    {xᵉ : node-Directed-Treeᵉ} → walk-Directed-Treeᵉ xᵉ xᵉ
  refl-walk-Directed-Treeᵉ = refl-walk-Directed-Graphᵉ

  cons-walk-Directed-Treeᵉ :
    {xᵉ yᵉ zᵉ : node-Directed-Treeᵉ} (eᵉ : edge-Directed-Treeᵉ xᵉ yᵉ) →
    walk-Directed-Treeᵉ yᵉ zᵉ → walk-Directed-Treeᵉ xᵉ zᵉ
  cons-walk-Directed-Treeᵉ = cons-walk-Directed-Graphᵉ

  unit-walk-Directed-Treeᵉ :
    {xᵉ yᵉ : node-Directed-Treeᵉ} →
    edge-Directed-Treeᵉ xᵉ yᵉ → walk-Directed-Treeᵉ xᵉ yᵉ
  unit-walk-Directed-Treeᵉ = unit-walk-Directed-Graphᵉ graph-Directed-Treeᵉ

  length-walk-Directed-Treeᵉ :
    {xᵉ yᵉ : node-Directed-Treeᵉ} → walk-Directed-Treeᵉ xᵉ yᵉ → ℕᵉ
  length-walk-Directed-Treeᵉ =
    length-walk-Directed-Graphᵉ graph-Directed-Treeᵉ

  is-tree-Directed-Treeᵉ : is-tree-Directed-Graphᵉ graph-Directed-Treeᵉ
  is-tree-Directed-Treeᵉ = pr2ᵉ Tᵉ

  root-Directed-Treeᵉ : node-Directed-Treeᵉ
  root-Directed-Treeᵉ = pr1ᵉ is-tree-Directed-Treeᵉ

  is-root-Directed-Treeᵉ : node-Directed-Treeᵉ → UUᵉ l1ᵉ
  is-root-Directed-Treeᵉ xᵉ = root-Directed-Treeᵉ ＝ᵉ xᵉ

  unique-walk-to-root-Directed-Treeᵉ :
    is-tree-Directed-Graph'ᵉ graph-Directed-Treeᵉ root-Directed-Treeᵉ
  unique-walk-to-root-Directed-Treeᵉ = pr2ᵉ is-tree-Directed-Treeᵉ

  walk-to-root-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ) → walk-Directed-Treeᵉ xᵉ root-Directed-Treeᵉ
  walk-to-root-Directed-Treeᵉ xᵉ =
    centerᵉ (unique-walk-to-root-Directed-Treeᵉ xᵉ)

  unique-walk-to-root-Directed-Tree'ᵉ :
    (xᵉ : node-Directed-Treeᵉ) →
    is-contrᵉ (walk-Directed-Tree'ᵉ xᵉ root-Directed-Treeᵉ)
  unique-walk-to-root-Directed-Tree'ᵉ xᵉ =
    is-contr-equiv'ᵉ
      ( walk-Directed-Treeᵉ xᵉ root-Directed-Treeᵉ)
      ( compute-walk-Directed-Treeᵉ xᵉ root-Directed-Treeᵉ)
      ( unique-walk-to-root-Directed-Treeᵉ xᵉ)

  walk-to-root-Directed-Tree'ᵉ :
    (xᵉ : node-Directed-Treeᵉ) → walk-Directed-Tree'ᵉ xᵉ root-Directed-Treeᵉ
  walk-to-root-Directed-Tree'ᵉ xᵉ =
    centerᵉ (unique-walk-to-root-Directed-Tree'ᵉ xᵉ)
```

### Proper nodes of directed trees

Weᵉ defineᵉ **properᵉ nodes**ᵉ ofᵉ aᵉ directedᵉ treeᵉ to beᵉ nodesᵉ thatᵉ areᵉ distinctᵉ fromᵉ
theᵉ root.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ)
  where

  is-proper-node-Directed-Tree-Propᵉ : node-Directed-Treeᵉ Tᵉ → Propᵉ l1ᵉ
  is-proper-node-Directed-Tree-Propᵉ xᵉ =
    neg-type-Propᵉ (is-root-Directed-Treeᵉ Tᵉ xᵉ)

  is-proper-node-Directed-Treeᵉ : node-Directed-Treeᵉ Tᵉ → UUᵉ l1ᵉ
  is-proper-node-Directed-Treeᵉ xᵉ =
    type-Propᵉ (is-proper-node-Directed-Tree-Propᵉ xᵉ)

  is-prop-is-proper-node-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) → is-propᵉ (is-proper-node-Directed-Treeᵉ xᵉ)
  is-prop-is-proper-node-Directed-Treeᵉ xᵉ =
    is-prop-type-Propᵉ (is-proper-node-Directed-Tree-Propᵉ xᵉ)

  is-proof-irrelevant-is-proper-node-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) →
    is-proof-irrelevantᵉ (is-proper-node-Directed-Treeᵉ xᵉ)
  is-proof-irrelevant-is-proper-node-Directed-Treeᵉ xᵉ =
    is-proof-irrelevant-is-propᵉ (is-prop-is-proper-node-Directed-Treeᵉ xᵉ)

  proper-node-Directed-Treeᵉ : UUᵉ l1ᵉ
  proper-node-Directed-Treeᵉ =
    Σᵉ (node-Directed-Treeᵉ Tᵉ) is-proper-node-Directed-Treeᵉ

  node-proper-node-Directed-Treeᵉ :
    proper-node-Directed-Treeᵉ → node-Directed-Treeᵉ Tᵉ
  node-proper-node-Directed-Treeᵉ = pr1ᵉ

  is-proper-node-proper-node-Directed-Treeᵉ :
    (xᵉ : proper-node-Directed-Treeᵉ) →
    is-proper-node-Directed-Treeᵉ (node-proper-node-Directed-Treeᵉ xᵉ)
  is-proper-node-proper-node-Directed-Treeᵉ = pr2ᵉ
```

## Properties

### Being a tree is a proposition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  uniqueness-root-is-tree-Directed-Graphᵉ :
    (Hᵉ Kᵉ : is-tree-Directed-Graphᵉ Gᵉ) → pr1ᵉ Hᵉ ＝ᵉ pr1ᵉ Kᵉ
  uniqueness-root-is-tree-Directed-Graphᵉ (rᵉ ,ᵉ Hᵉ) (sᵉ ,ᵉ Kᵉ) =
    eq-is-refl-concat-walk-Directed-Graphᵉ Gᵉ
      ( centerᵉ (Kᵉ rᵉ))
      ( centerᵉ (Hᵉ sᵉ))
      ( eq-is-contrᵉ (Hᵉ rᵉ))

  is-prop-is-tree-Directed-Graphᵉ : is-propᵉ (is-tree-Directed-Graphᵉ Gᵉ)
  is-prop-is-tree-Directed-Graphᵉ =
    is-prop-all-elements-equalᵉ
      ( λ Hᵉ Kᵉ →
        eq-type-subtypeᵉ
          ( is-tree-Directed-Graph-Prop'ᵉ Gᵉ)
          ( uniqueness-root-is-tree-Directed-Graphᵉ Hᵉ Kᵉ))

  is-tree-directed-graph-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ is-tree-directed-graph-Propᵉ = is-tree-Directed-Graphᵉ Gᵉ
  pr2ᵉ is-tree-directed-graph-Propᵉ = is-prop-is-tree-Directed-Graphᵉ

uniqueness-root-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ)
  (Hᵉ : is-tree-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ)) →
  is-root-Directed-Treeᵉ Tᵉ (pr1ᵉ Hᵉ)
uniqueness-root-Directed-Treeᵉ Tᵉ =
  uniqueness-root-is-tree-Directed-Graphᵉ
    ( graph-Directed-Treeᵉ Tᵉ)
    ( is-tree-Directed-Treeᵉ Tᵉ)
```

### The root in a tree is an isolated element

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ)
  where

  abstract
    is-decidable-is-root-walk-Directed-Treeᵉ :
      (xᵉ : node-Directed-Treeᵉ Tᵉ)
      (wᵉ : walk-Directed-Treeᵉ Tᵉ xᵉ (root-Directed-Treeᵉ Tᵉ)) →
      is-decidableᵉ (is-root-Directed-Treeᵉ Tᵉ xᵉ)
    is-decidable-is-root-walk-Directed-Treeᵉ ._ refl-walk-Directed-Graphᵉ =
      inlᵉ reflᵉ
    is-decidable-is-root-walk-Directed-Treeᵉ xᵉ
      ( cons-walk-Directed-Graphᵉ {.xᵉ} {yᵉ} eᵉ wᵉ) =
      inrᵉ
        ( λ where
          reflᵉ →
            neq-cons-refl-walk-Directed-Graphᵉ
              ( graph-Directed-Treeᵉ Tᵉ)
              ( xᵉ)
              ( yᵉ)
              ( eᵉ)
              ( wᵉ)
              ( eq-is-contrᵉ (unique-walk-to-root-Directed-Treeᵉ Tᵉ xᵉ)))

  is-isolated-root-Directed-Treeᵉ : is-isolatedᵉ (root-Directed-Treeᵉ Tᵉ)
  is-isolated-root-Directed-Treeᵉ xᵉ =
    is-decidable-is-root-walk-Directed-Treeᵉ xᵉ (walk-to-root-Directed-Treeᵉ Tᵉ xᵉ)

  is-prop-is-root-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) → is-propᵉ (is-root-Directed-Treeᵉ Tᵉ xᵉ)
  is-prop-is-root-Directed-Treeᵉ =
    is-prop-eq-isolated-elementᵉ
      ( root-Directed-Treeᵉ Tᵉ)
      ( is-isolated-root-Directed-Treeᵉ)

  is-root-directed-tree-Propᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) → Propᵉ l1ᵉ
  pr1ᵉ (is-root-directed-tree-Propᵉ xᵉ) = is-root-Directed-Treeᵉ Tᵉ xᵉ
  pr2ᵉ (is-root-directed-tree-Propᵉ xᵉ) = is-prop-is-root-Directed-Treeᵉ xᵉ

  is-contr-loop-space-root-Directed-Treeᵉ :
    is-contrᵉ (root-Directed-Treeᵉ Tᵉ ＝ᵉ root-Directed-Treeᵉ Tᵉ)
  is-contr-loop-space-root-Directed-Treeᵉ =
    is-contr-loop-space-isolated-elementᵉ
      ( root-Directed-Treeᵉ Tᵉ)
      ( is-isolated-root-Directed-Treeᵉ)

  eq-refl-root-Directed-Treeᵉ :
    (pᵉ : root-Directed-Treeᵉ Tᵉ ＝ᵉ root-Directed-Treeᵉ Tᵉ) → pᵉ ＝ᵉ reflᵉ
  eq-refl-root-Directed-Treeᵉ pᵉ =
    eq-is-contrᵉ is-contr-loop-space-root-Directed-Treeᵉ

  eq-refl-root-Directed-Tree'ᵉ :
    (pᵉ : root-Directed-Treeᵉ Tᵉ ＝ᵉ root-Directed-Treeᵉ Tᵉ) → reflᵉ ＝ᵉ pᵉ
  eq-refl-root-Directed-Tree'ᵉ pᵉ =
    eq-is-contrᵉ is-contr-loop-space-root-Directed-Treeᵉ
```

### The root has no direct successors

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ)
  where

  no-direct-successor-root-Directed-Treeᵉ :
    ¬ᵉ (Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ (root-Directed-Treeᵉ Tᵉ)))
  no-direct-successor-root-Directed-Treeᵉ (xᵉ ,ᵉ eᵉ) =
    neq-cons-refl-walk-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Tᵉ)
      ( root-Directed-Treeᵉ Tᵉ)
      ( xᵉ)
      ( eᵉ)
      ( walk-to-root-Directed-Treeᵉ Tᵉ xᵉ)
      ( eq-is-contrᵉ
        ( unique-walk-to-root-Directed-Treeᵉ Tᵉ (root-Directed-Treeᵉ Tᵉ)))

  is-proper-node-direct-successor-Directed-Treeᵉ :
    {xᵉ yᵉ : node-Directed-Treeᵉ Tᵉ} (eᵉ : edge-Directed-Treeᵉ Tᵉ xᵉ yᵉ) →
    ¬ᵉ (is-root-Directed-Treeᵉ Tᵉ xᵉ)
  is-proper-node-direct-successor-Directed-Treeᵉ eᵉ reflᵉ =
    no-direct-successor-root-Directed-Treeᵉ (ᵉ_ ,ᵉ eᵉ)
```

### The type of edges to the root is a proposition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ)
  where

  is-proof-irrelevant-edge-to-root-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) →
    is-proof-irrelevantᵉ (edge-Directed-Treeᵉ Tᵉ xᵉ (root-Directed-Treeᵉ Tᵉ))
  pr1ᵉ (is-proof-irrelevant-edge-to-root-Directed-Treeᵉ xᵉ eᵉ) = eᵉ
  pr2ᵉ (is-proof-irrelevant-edge-to-root-Directed-Treeᵉ xᵉ eᵉ) e'ᵉ =
    is-injective-unit-walk-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eq-is-contrᵉ (unique-walk-to-root-Directed-Treeᵉ Tᵉ xᵉ))

  is-prop-edge-to-root-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) →
    is-propᵉ (edge-Directed-Treeᵉ Tᵉ xᵉ (root-Directed-Treeᵉ Tᵉ))
  is-prop-edge-to-root-Directed-Treeᵉ xᵉ =
    is-prop-is-proof-irrelevantᵉ
      ( is-proof-irrelevant-edge-to-root-Directed-Treeᵉ xᵉ)

  eq-edge-to-root-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ)
    (eᵉ e'ᵉ : edge-Directed-Treeᵉ Tᵉ xᵉ (root-Directed-Treeᵉ Tᵉ)) → eᵉ ＝ᵉ e'ᵉ
  eq-edge-to-root-Directed-Treeᵉ xᵉ eᵉ e'ᵉ =
    eq-is-propᵉ (is-prop-edge-to-root-Directed-Treeᵉ xᵉ)
```

### Graphs in which vertices have unique direct-successors are trees if for every vertex `x` there is a walk from `x` to the root

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (rᵉ : vertex-Directed-Graphᵉ Gᵉ)
  where

  unique-direct-successor-Directed-Graphᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  unique-direct-successor-Directed-Graphᵉ =
    (xᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    is-contrᵉ ((rᵉ ＝ᵉ xᵉ) +ᵉ Σᵉ (vertex-Directed-Graphᵉ Gᵉ) (edge-Directed-Graphᵉ Gᵉ xᵉ))

  no-direct-successor-root-unique-direct-successor-Directed-Graphᵉ :
    unique-direct-successor-Directed-Graphᵉ →
    is-emptyᵉ (Σᵉ (vertex-Directed-Graphᵉ Gᵉ) (edge-Directed-Graphᵉ Gᵉ rᵉ))
  no-direct-successor-root-unique-direct-successor-Directed-Graphᵉ Hᵉ =
    is-empty-right-summand-is-contr-coproductᵉ (Hᵉ rᵉ) reflᵉ

  is-isolated-root-unique-direct-successor-Directed-Graphᵉ :
    unique-direct-successor-Directed-Graphᵉ → is-isolatedᵉ rᵉ
  is-isolated-root-unique-direct-successor-Directed-Graphᵉ Hᵉ xᵉ =
    map-coproductᵉ
      ( idᵉ)
      ( is-empty-left-summand-is-contr-coproductᵉ (Hᵉ xᵉ))
      ( centerᵉ (Hᵉ xᵉ))

  is-torsorial-walk-from-root-unique-direct-successor-Directed-Graphᵉ :
    unique-direct-successor-Directed-Graphᵉ →
    is-torsorialᵉ (walk-Directed-Graphᵉ Gᵉ rᵉ)
  pr1ᵉ (is-torsorial-walk-from-root-unique-direct-successor-Directed-Graphᵉ Hᵉ) =
    ( rᵉ ,ᵉ refl-walk-Directed-Graphᵉ)
  pr2ᵉ
    ( is-torsorial-walk-from-root-unique-direct-successor-Directed-Graphᵉ Hᵉ)
    ( yᵉ ,ᵉ refl-walk-Directed-Graphᵉ) =
    reflᵉ
  pr2ᵉ
    ( is-torsorial-walk-from-root-unique-direct-successor-Directed-Graphᵉ Hᵉ)
    ( yᵉ ,ᵉ cons-walk-Directed-Graphᵉ eᵉ wᵉ) =
    ex-falsoᵉ
      ( no-direct-successor-root-unique-direct-successor-Directed-Graphᵉ Hᵉ
        ( _ ,ᵉ eᵉ))

  is-contr-loop-space-root-unique-direct-successor-Directed-Graphᵉ :
    unique-direct-successor-Directed-Graphᵉ → is-contrᵉ (rᵉ ＝ᵉ rᵉ)
  is-contr-loop-space-root-unique-direct-successor-Directed-Graphᵉ Hᵉ =
    is-contr-loop-space-isolated-elementᵉ rᵉ
      ( is-isolated-root-unique-direct-successor-Directed-Graphᵉ Hᵉ)

  is-not-root-has-unique-direct-successor-Directed-Graphᵉ :
    (xᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    is-contrᵉ
      ( (rᵉ ＝ᵉ xᵉ) +ᵉ Σᵉ (vertex-Directed-Graphᵉ Gᵉ) (edge-Directed-Graphᵉ Gᵉ xᵉ)) →
    Σᵉ (vertex-Directed-Graphᵉ Gᵉ) (edge-Directed-Graphᵉ Gᵉ xᵉ) → rᵉ ≠ᵉ xᵉ
  is-not-root-has-unique-direct-successor-Directed-Graphᵉ xᵉ Hᵉ (yᵉ ,ᵉ eᵉ) =
    is-empty-left-summand-is-contr-coproductᵉ Hᵉ (yᵉ ,ᵉ eᵉ)

  is-proof-irrelevant-direct-successor-has-unique-direct-successor-Directed-Graphᵉ :
    (xᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    is-contrᵉ
      ( (rᵉ ＝ᵉ xᵉ) +ᵉ Σᵉ (vertex-Directed-Graphᵉ Gᵉ) (edge-Directed-Graphᵉ Gᵉ xᵉ)) →
    is-proof-irrelevantᵉ (Σᵉ (vertex-Directed-Graphᵉ Gᵉ) (edge-Directed-Graphᵉ Gᵉ xᵉ))
  is-proof-irrelevant-direct-successor-has-unique-direct-successor-Directed-Graphᵉ
    xᵉ Hᵉ (yᵉ ,ᵉ eᵉ) =
    is-contr-right-summandᵉ Hᵉ (yᵉ ,ᵉ eᵉ)

  is-proof-irrelevant-walk-unique-direct-successor-Directed-Graphᵉ :
    unique-direct-successor-Directed-Graphᵉ → (xᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    is-proof-irrelevantᵉ (walk-Directed-Graphᵉ Gᵉ xᵉ rᵉ)
  pr1ᵉ
    ( is-proof-irrelevant-walk-unique-direct-successor-Directed-Graphᵉ Hᵉ xᵉ
      refl-walk-Directed-Graphᵉ) =
    refl-walk-Directed-Graphᵉ
  pr2ᵉ
    ( is-proof-irrelevant-walk-unique-direct-successor-Directed-Graphᵉ Hᵉ xᵉ
      refl-walk-Directed-Graphᵉ)
    ( wᵉ) =
    ( invᵉ
      ( apᵉ
        ( λ αᵉ → trᵉ (walk-Directed-Graphᵉ Gᵉ xᵉ) αᵉ refl-walk-Directed-Graphᵉ)
        ( eq-is-contrᵉ
          ( is-contr-loop-space-root-unique-direct-successor-Directed-Graphᵉ
            ( Hᵉ))))) ∙ᵉ
    ( pr2ᵉ
      ( pair-eq-Σᵉ
        ( eq-is-contrᵉ
          ( is-torsorial-walk-from-root-unique-direct-successor-Directed-Graphᵉ
            Hᵉ)
          { (rᵉ ,ᵉ refl-walk-Directed-Graphᵉ)}
          { (rᵉ ,ᵉ wᵉ)})))
  is-proof-irrelevant-walk-unique-direct-successor-Directed-Graphᵉ Hᵉ xᵉ
    ( cons-walk-Directed-Graphᵉ {.xᵉ} {yᵉ} eᵉ wᵉ) =
    is-contr-equivᵉ
      ( walk-Directed-Graphᵉ Gᵉ yᵉ rᵉ)
      ( equivalence-reasoningᵉ
        walk-Directed-Graphᵉ Gᵉ xᵉ rᵉ
        ≃ᵉ coproduct-walk-Directed-Graphᵉ Gᵉ xᵉ rᵉ
          byᵉ compute-coproduct-walk-Directed-Graphᵉ Gᵉ xᵉ rᵉ
        ≃ᵉ Σᵉ ( vertex-Directed-Graphᵉ Gᵉ)
            ( λ yᵉ → edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ ×ᵉ walk-Directed-Graphᵉ Gᵉ yᵉ rᵉ)
          byᵉ
          left-unit-law-coproduct-is-emptyᵉ
            ( rᵉ ＝ᵉ xᵉ)
            ( Σᵉ ( vertex-Directed-Graphᵉ Gᵉ)
                ( λ yᵉ →
                  edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ ×ᵉ walk-Directed-Graphᵉ Gᵉ yᵉ rᵉ))
            ( is-not-root-has-unique-direct-successor-Directed-Graphᵉ xᵉ
              ( Hᵉ xᵉ)
              ( yᵉ ,ᵉ eᵉ))
        ≃ᵉ Σᵉ ( Σᵉ (vertex-Directed-Graphᵉ Gᵉ) (edge-Directed-Graphᵉ Gᵉ xᵉ))
            ( λ pᵉ → walk-Directed-Graphᵉ Gᵉ (pr1ᵉ pᵉ) rᵉ)
          byᵉ
          inv-associative-Σᵉ
            ( vertex-Directed-Graphᵉ Gᵉ)
            ( edge-Directed-Graphᵉ Gᵉ xᵉ)
            ( λ pᵉ → walk-Directed-Graphᵉ Gᵉ (pr1ᵉ pᵉ) rᵉ)
        ≃ᵉ walk-Directed-Graphᵉ Gᵉ yᵉ rᵉ
          byᵉ
          left-unit-law-Σ-is-contrᵉ
            ( is-proof-irrelevant-direct-successor-has-unique-direct-successor-Directed-Graphᵉ
              ( xᵉ)
              ( Hᵉ xᵉ)
              ( yᵉ ,ᵉ eᵉ))
            (yᵉ ,ᵉ eᵉ))
      ( is-proof-irrelevant-walk-unique-direct-successor-Directed-Graphᵉ Hᵉ yᵉ wᵉ)

  is-tree-unique-direct-successor-Directed-Graph'ᵉ :
    unique-direct-successor-Directed-Graphᵉ →
    ((xᵉ : vertex-Directed-Graphᵉ Gᵉ) → walk-Directed-Graphᵉ Gᵉ xᵉ rᵉ) →
    is-tree-Directed-Graph'ᵉ Gᵉ rᵉ
  is-tree-unique-direct-successor-Directed-Graph'ᵉ Hᵉ wᵉ xᵉ =
    is-proof-irrelevant-walk-unique-direct-successor-Directed-Graphᵉ Hᵉ xᵉ (wᵉ xᵉ)

  is-tree-unique-direct-successor-Directed-Graphᵉ :
    unique-direct-successor-Directed-Graphᵉ →
    ((xᵉ : vertex-Directed-Graphᵉ Gᵉ) → walk-Directed-Graphᵉ Gᵉ xᵉ rᵉ) →
    is-tree-Directed-Graphᵉ Gᵉ
  pr1ᵉ (is-tree-unique-direct-successor-Directed-Graphᵉ Hᵉ wᵉ) = rᵉ
  pr2ᵉ (is-tree-unique-direct-successor-Directed-Graphᵉ Hᵉ wᵉ) =
    is-tree-unique-direct-successor-Directed-Graph'ᵉ Hᵉ wᵉ
```

### Nodes in trees have unique direct-successors

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ)
  where

  center-walk-unique-direct-successor-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ)
    (wᵉ : walk-Directed-Treeᵉ Tᵉ xᵉ (root-Directed-Treeᵉ Tᵉ)) →
    is-root-Directed-Treeᵉ Tᵉ xᵉ +ᵉ
    Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ xᵉ)
  center-walk-unique-direct-successor-Directed-Treeᵉ .(root-Directed-Treeᵉ Tᵉ)
    refl-walk-Directed-Graphᵉ =
    inlᵉ reflᵉ
  center-walk-unique-direct-successor-Directed-Treeᵉ xᵉ
    ( cons-walk-Directed-Graphᵉ {.xᵉ} {yᵉ} eᵉ wᵉ) =
    inrᵉ (yᵉ ,ᵉ eᵉ)

  center-unique-direct-successor-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) →
    is-root-Directed-Treeᵉ Tᵉ xᵉ +ᵉ
    Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ xᵉ)
  center-unique-direct-successor-Directed-Treeᵉ xᵉ =
    center-walk-unique-direct-successor-Directed-Treeᵉ xᵉ
      ( walk-to-root-Directed-Treeᵉ Tᵉ xᵉ)

  contraction-walk-unique-direct-successor-Directed-Treeᵉ :
    ( xᵉ : node-Directed-Treeᵉ Tᵉ)
    ( wᵉ : walk-Directed-Treeᵉ Tᵉ xᵉ (root-Directed-Treeᵉ Tᵉ)) →
    ( pᵉ :
      is-root-Directed-Treeᵉ Tᵉ xᵉ +ᵉ
      Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ xᵉ)) →
    center-walk-unique-direct-successor-Directed-Treeᵉ xᵉ wᵉ ＝ᵉ pᵉ
  contraction-walk-unique-direct-successor-Directed-Treeᵉ ._
    ( refl-walk-Directed-Graphᵉ)
    ( inlᵉ pᵉ) =
    apᵉ inlᵉ (eq-refl-root-Directed-Tree'ᵉ Tᵉ pᵉ)
  contraction-walk-unique-direct-successor-Directed-Treeᵉ ._
    ( refl-walk-Directed-Graphᵉ)
    ( inrᵉ (yᵉ ,ᵉ eᵉ)) =
    ex-falsoᵉ (no-direct-successor-root-Directed-Treeᵉ Tᵉ (yᵉ ,ᵉ eᵉ))
  contraction-walk-unique-direct-successor-Directed-Treeᵉ _
    ( cons-walk-Directed-Graphᵉ {.ᵉ_} {yᵉ} eᵉ wᵉ)
    ( inlᵉ reflᵉ) =
    ex-falsoᵉ (no-direct-successor-root-Directed-Treeᵉ Tᵉ (yᵉ ,ᵉ eᵉ))
  contraction-walk-unique-direct-successor-Directed-Treeᵉ _
    ( cons-walk-Directed-Graphᵉ {xᵉ} {yᵉ} eᵉ wᵉ)
    ( inrᵉ (zᵉ ,ᵉ fᵉ)) =
    apᵉ
      ( inrᵉ)
      ( eq-direct-successor-eq-cons-walk-Directed-Graphᵉ
        ( graph-Directed-Treeᵉ Tᵉ)
        ( xᵉ)
        ( eᵉ)
        ( fᵉ)
        ( walk-to-root-Directed-Treeᵉ Tᵉ yᵉ)
        ( walk-to-root-Directed-Treeᵉ Tᵉ zᵉ)
        ( eq-is-contrᵉ (unique-walk-to-root-Directed-Treeᵉ Tᵉ xᵉ)))

  contraction-unique-direct-successor-Directed-Treeᵉ :
    ( xᵉ : node-Directed-Treeᵉ Tᵉ) →
    ( pᵉ :
      is-root-Directed-Treeᵉ Tᵉ xᵉ +ᵉ
      Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ xᵉ)) →
    center-unique-direct-successor-Directed-Treeᵉ xᵉ ＝ᵉ pᵉ
  contraction-unique-direct-successor-Directed-Treeᵉ xᵉ =
    contraction-walk-unique-direct-successor-Directed-Treeᵉ xᵉ
      ( walk-to-root-Directed-Treeᵉ Tᵉ xᵉ)

  unique-direct-successor-Directed-Treeᵉ :
    unique-direct-successor-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Tᵉ)
      ( root-Directed-Treeᵉ Tᵉ)
  pr1ᵉ (unique-direct-successor-Directed-Treeᵉ xᵉ) =
    center-unique-direct-successor-Directed-Treeᵉ xᵉ
  pr2ᵉ (unique-direct-successor-Directed-Treeᵉ xᵉ) =
    contraction-unique-direct-successor-Directed-Treeᵉ xᵉ

  unique-direct-successor-is-proper-node-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) → is-proper-node-Directed-Treeᵉ Tᵉ xᵉ →
    is-contrᵉ (Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ xᵉ))
  unique-direct-successor-is-proper-node-Directed-Treeᵉ xᵉ fᵉ =
    is-contr-equiv'ᵉ
      ( ( is-root-Directed-Treeᵉ Tᵉ xᵉ) +ᵉ
        ( Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ xᵉ)))
      ( left-unit-law-coproduct-is-emptyᵉ
        ( is-root-Directed-Treeᵉ Tᵉ xᵉ)
        ( Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ xᵉ))
        ( fᵉ))
      ( unique-direct-successor-Directed-Treeᵉ xᵉ)

  abstract
    is-proof-irrelevant-direct-successor-Directed-Treeᵉ :
      (xᵉ : node-Directed-Treeᵉ Tᵉ) →
      is-proof-irrelevantᵉ (Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ xᵉ))
    is-proof-irrelevant-direct-successor-Directed-Treeᵉ xᵉ (yᵉ ,ᵉ eᵉ) =
      unique-direct-successor-is-proper-node-Directed-Treeᵉ xᵉ
        ( λ where reflᵉ → no-direct-successor-root-Directed-Treeᵉ Tᵉ (yᵉ ,ᵉ eᵉ))

  is-prop-direct-successor-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) →
    is-propᵉ (Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ xᵉ))
  is-prop-direct-successor-Directed-Treeᵉ xᵉ =
    is-prop-is-proof-irrelevantᵉ
      ( is-proof-irrelevant-direct-successor-Directed-Treeᵉ xᵉ)

  eq-direct-successor-Directed-Treeᵉ :
    {xᵉ : node-Directed-Treeᵉ Tᵉ}
    (uᵉ vᵉ : Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ xᵉ)) → uᵉ ＝ᵉ vᵉ
  eq-direct-successor-Directed-Treeᵉ {xᵉ} =
    eq-is-prop'ᵉ (is-prop-direct-successor-Directed-Treeᵉ xᵉ)

  direct-successor-is-proper-node-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) → is-proper-node-Directed-Treeᵉ Tᵉ xᵉ →
    Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ xᵉ)
  direct-successor-is-proper-node-Directed-Treeᵉ xᵉ fᵉ =
    centerᵉ (unique-direct-successor-is-proper-node-Directed-Treeᵉ xᵉ fᵉ)
```

### Transporting walks in directed trees

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ)
  where

  tr-walk-eq-direct-successor-Directed-Treeᵉ :
    {xᵉ yᵉ : node-Directed-Treeᵉ Tᵉ}
    (uᵉ vᵉ : Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ xᵉ)) →
    walk-Directed-Treeᵉ Tᵉ (pr1ᵉ uᵉ) yᵉ → walk-Directed-Treeᵉ Tᵉ (pr1ᵉ vᵉ) yᵉ
  tr-walk-eq-direct-successor-Directed-Treeᵉ {xᵉ} {yᵉ} uᵉ vᵉ =
    trᵉ
      ( λ rᵉ → walk-Directed-Treeᵉ Tᵉ (pr1ᵉ rᵉ) yᵉ)
      ( eq-direct-successor-Directed-Treeᵉ Tᵉ uᵉ vᵉ)

  eq-tr-walk-eq-direct-successor-Directed-Tree'ᵉ :
    {xᵉ yᵉ : node-Directed-Treeᵉ Tᵉ}
    (uᵉ vᵉ : Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ xᵉ)) →
    (wᵉ : walk-Directed-Treeᵉ Tᵉ (pr1ᵉ uᵉ) yᵉ) →
    (pᵉ : uᵉ ＝ᵉ vᵉ) →
    cons-walk-Directed-Graphᵉ
      ( pr2ᵉ vᵉ)
      ( trᵉ (λ rᵉ → walk-Directed-Treeᵉ Tᵉ (pr1ᵉ rᵉ) yᵉ) pᵉ wᵉ) ＝ᵉ
    cons-walk-Directed-Graphᵉ (pr2ᵉ uᵉ) wᵉ
  eq-tr-walk-eq-direct-successor-Directed-Tree'ᵉ uᵉ .uᵉ wᵉ reflᵉ = reflᵉ

  eq-tr-walk-eq-direct-successor-Directed-Treeᵉ :
    {xᵉ yᵉ : node-Directed-Treeᵉ Tᵉ}
    (uᵉ vᵉ : Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ xᵉ)) →
    (wᵉ : walk-Directed-Treeᵉ Tᵉ (pr1ᵉ uᵉ) yᵉ) →
    cons-walk-Directed-Graphᵉ
      ( pr2ᵉ vᵉ)
      ( tr-walk-eq-direct-successor-Directed-Treeᵉ uᵉ vᵉ wᵉ) ＝ᵉ
    cons-walk-Directed-Graphᵉ (pr2ᵉ uᵉ) wᵉ
  eq-tr-walk-eq-direct-successor-Directed-Treeᵉ uᵉ vᵉ wᵉ =
    eq-tr-walk-eq-direct-successor-Directed-Tree'ᵉ uᵉ vᵉ wᵉ
      ( eq-direct-successor-Directed-Treeᵉ Tᵉ uᵉ vᵉ)
```

## See also

Thereᵉ areᵉ manyᵉ variationsᵉ ofᵉ theᵉ notionᵉ ofᵉ trees,ᵉ allᵉ ofᵉ whichᵉ areᵉ subtlyᵉ
differentᵉ:

-ᵉ Undirectedᵉ treesᵉ canᵉ beᵉ foundᵉ in
  [`trees.undirected-trees`](trees.undirected-trees.md).ᵉ
-ᵉ Acyclicᵉ undirectedᵉ graphsᵉ canᵉ beᵉ foundᵉ in
  [`graph-theory.acyclic-undirected-graphs`](graph-theory.acyclic-undirected-graphs.md).ᵉ