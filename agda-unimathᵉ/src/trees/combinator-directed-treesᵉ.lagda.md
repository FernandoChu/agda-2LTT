# The combinator of directed trees

```agda
module trees.combinator-directed-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.isolated-elementsᵉ
open import foundation.maybeᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ
open import graph-theory.morphisms-directed-graphsᵉ
open import graph-theory.walks-directed-graphsᵉ

open import trees.bases-directed-treesᵉ
open import trees.directed-treesᵉ
open import trees.equivalences-directed-treesᵉ
open import trees.fibers-directed-treesᵉ
open import trees.morphisms-directed-treesᵉ
```

</details>

## Idea

Theᵉ **combinatorᵉ operation**ᵉ onᵉ directedᵉ treesᵉ combinesᵉ aᵉ familyᵉ ofᵉ directedᵉ
treesᵉ intoᵉ aᵉ singleᵉ directedᵉ treeᵉ with aᵉ newᵉ root.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (Tᵉ : Iᵉ → Directed-Treeᵉ l2ᵉ l3ᵉ)
  where

  data node-combinator-Directed-Treeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ) where
    root-combinator-Directed-Treeᵉ : node-combinator-Directed-Treeᵉ
    node-inclusion-combinator-Directed-Treeᵉ :
      (iᵉ : Iᵉ) → node-Directed-Treeᵉ (Tᵉ iᵉ) → node-combinator-Directed-Treeᵉ

  data
    edge-combinator-Directed-Treeᵉ :
      ( xᵉ yᵉ : node-combinator-Directed-Treeᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) where
    edge-to-root-combinator-Directed-Treeᵉ :
      (iᵉ : Iᵉ) →
      edge-combinator-Directed-Treeᵉ
        ( node-inclusion-combinator-Directed-Treeᵉ iᵉ (root-Directed-Treeᵉ (Tᵉ iᵉ)))
        ( root-combinator-Directed-Treeᵉ)
    edge-inclusion-combinator-Directed-Treeᵉ :
      (iᵉ : Iᵉ) (xᵉ yᵉ : node-Directed-Treeᵉ (Tᵉ iᵉ)) →
      edge-Directed-Treeᵉ (Tᵉ iᵉ) xᵉ yᵉ →
      edge-combinator-Directed-Treeᵉ
        ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ)
        ( node-inclusion-combinator-Directed-Treeᵉ iᵉ yᵉ)

  graph-combinator-Directed-Treeᵉ : Directed-Graphᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ graph-combinator-Directed-Treeᵉ = node-combinator-Directed-Treeᵉ
  pr2ᵉ graph-combinator-Directed-Treeᵉ = edge-combinator-Directed-Treeᵉ

  inclusion-combinator-Directed-Treeᵉ :
    (iᵉ : Iᵉ) →
    hom-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ (Tᵉ iᵉ))
      ( graph-combinator-Directed-Treeᵉ)
  pr1ᵉ (inclusion-combinator-Directed-Treeᵉ iᵉ) =
    node-inclusion-combinator-Directed-Treeᵉ iᵉ
  pr2ᵉ (inclusion-combinator-Directed-Treeᵉ iᵉ) =
    edge-inclusion-combinator-Directed-Treeᵉ iᵉ

  walk-combinator-Directed-Treeᵉ :
    ( xᵉ yᵉ : node-combinator-Directed-Treeᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  walk-combinator-Directed-Treeᵉ =
    walk-Directed-Graphᵉ graph-combinator-Directed-Treeᵉ

  walk-inclusion-combinator-Directed-Treeᵉ :
    (iᵉ : Iᵉ) (xᵉ yᵉ : node-Directed-Treeᵉ (Tᵉ iᵉ)) →
    walk-Directed-Graphᵉ (graph-Directed-Treeᵉ (Tᵉ iᵉ)) xᵉ yᵉ →
    walk-combinator-Directed-Treeᵉ
      ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ)
      ( node-inclusion-combinator-Directed-Treeᵉ iᵉ yᵉ)
  walk-inclusion-combinator-Directed-Treeᵉ aᵉ xᵉ yᵉ =
    walk-hom-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ (Tᵉ aᵉ))
      ( graph-combinator-Directed-Treeᵉ)
      ( inclusion-combinator-Directed-Treeᵉ aᵉ)

  walk-to-root-combinator-Directed-Treeᵉ :
    ( xᵉ : node-combinator-Directed-Treeᵉ) →
    walk-combinator-Directed-Treeᵉ xᵉ root-combinator-Directed-Treeᵉ
  walk-to-root-combinator-Directed-Treeᵉ root-combinator-Directed-Treeᵉ =
    refl-walk-Directed-Graphᵉ
  walk-to-root-combinator-Directed-Treeᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ) =
    snoc-walk-Directed-Graphᵉ
      ( graph-combinator-Directed-Treeᵉ)
      ( walk-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ
        ( root-Directed-Treeᵉ (Tᵉ iᵉ))
        ( walk-to-root-Directed-Treeᵉ (Tᵉ iᵉ) xᵉ))
      ( edge-to-root-combinator-Directed-Treeᵉ iᵉ)

  is-root-combinator-Directed-Treeᵉ :
    node-combinator-Directed-Treeᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-root-combinator-Directed-Treeᵉ xᵉ = root-combinator-Directed-Treeᵉ ＝ᵉ xᵉ

  is-isolated-root-combinator-Directed-Treeᵉ :
    is-isolatedᵉ root-combinator-Directed-Treeᵉ
  is-isolated-root-combinator-Directed-Treeᵉ root-combinator-Directed-Treeᵉ =
    inlᵉ reflᵉ
  is-isolated-root-combinator-Directed-Treeᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ) =
    inrᵉ (λ ())

  cases-center-unique-direct-successor-combinator-Directed-Tree'ᵉ :
    (iᵉ : Iᵉ) (xᵉ : node-Directed-Treeᵉ (Tᵉ iᵉ)) →
    is-decidableᵉ (is-root-Directed-Treeᵉ (Tᵉ iᵉ) xᵉ) →
    Σᵉ ( node-combinator-Directed-Treeᵉ)
      ( edge-combinator-Directed-Treeᵉ
        ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ))
  cases-center-unique-direct-successor-combinator-Directed-Tree'ᵉ aᵉ ._
    ( inlᵉ reflᵉ) =
    ( root-combinator-Directed-Treeᵉ ,ᵉ edge-to-root-combinator-Directed-Treeᵉ aᵉ)
  cases-center-unique-direct-successor-combinator-Directed-Tree'ᵉ iᵉ xᵉ (inrᵉ fᵉ) =
    map-Σᵉ
      ( edge-combinator-Directed-Treeᵉ
        ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ))
      ( node-inclusion-combinator-Directed-Treeᵉ iᵉ)
      ( edge-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ)
      ( direct-successor-is-proper-node-Directed-Treeᵉ (Tᵉ iᵉ) xᵉ fᵉ)

  center-unique-direct-successor-combinator-Directed-Tree'ᵉ :
    ( xᵉ : node-combinator-Directed-Treeᵉ) →
    ¬ᵉ (is-root-combinator-Directed-Treeᵉ xᵉ) →
    Σᵉ node-combinator-Directed-Treeᵉ (edge-combinator-Directed-Treeᵉ xᵉ)
  center-unique-direct-successor-combinator-Directed-Tree'ᵉ
    root-combinator-Directed-Treeᵉ fᵉ = ex-falsoᵉ (fᵉ reflᵉ)
  center-unique-direct-successor-combinator-Directed-Tree'ᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ) fᵉ =
    cases-center-unique-direct-successor-combinator-Directed-Tree'ᵉ iᵉ xᵉ
      ( is-isolated-root-Directed-Treeᵉ (Tᵉ iᵉ) xᵉ)

  cases-center-unique-direct-successor-combinator-Directed-Treeᵉ :
    (iᵉ : Iᵉ) (xᵉ : node-Directed-Treeᵉ (Tᵉ iᵉ)) →
    is-decidableᵉ (is-root-Directed-Treeᵉ (Tᵉ iᵉ) xᵉ) →
    Σᵉ ( node-combinator-Directed-Treeᵉ)
      ( edge-combinator-Directed-Treeᵉ
        ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ))
  cases-center-unique-direct-successor-combinator-Directed-Treeᵉ iᵉ ._
    ( inlᵉ reflᵉ) =
    root-combinator-Directed-Treeᵉ ,ᵉ
    edge-to-root-combinator-Directed-Treeᵉ iᵉ
  cases-center-unique-direct-successor-combinator-Directed-Treeᵉ iᵉ xᵉ (inrᵉ fᵉ) =
    map-Σᵉ
      ( edge-combinator-Directed-Treeᵉ
        ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ))
      ( node-inclusion-combinator-Directed-Treeᵉ iᵉ)
      ( edge-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ)
      ( direct-successor-is-proper-node-Directed-Treeᵉ (Tᵉ iᵉ) xᵉ fᵉ)

  center-unique-direct-successor-combinator-Directed-Treeᵉ :
    (xᵉ : node-combinator-Directed-Treeᵉ) →
    is-root-combinator-Directed-Treeᵉ xᵉ +ᵉ
    Σᵉ node-combinator-Directed-Treeᵉ (edge-combinator-Directed-Treeᵉ xᵉ)
  center-unique-direct-successor-combinator-Directed-Treeᵉ
    root-combinator-Directed-Treeᵉ =
    inlᵉ reflᵉ
  center-unique-direct-successor-combinator-Directed-Treeᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ) =
    inrᵉ
      ( cases-center-unique-direct-successor-combinator-Directed-Treeᵉ iᵉ xᵉ
        ( is-isolated-root-Directed-Treeᵉ (Tᵉ iᵉ) xᵉ))

  cases-contraction-unique-direct-successor-combinator-Directed-Treeᵉ :
    (iᵉ : Iᵉ) (xᵉ : node-Directed-Treeᵉ (Tᵉ iᵉ)) →
    (dᵉ : is-decidableᵉ (is-root-Directed-Treeᵉ (Tᵉ iᵉ) xᵉ)) →
    ( pᵉ :
      Σᵉ ( node-combinator-Directed-Treeᵉ)
        ( edge-combinator-Directed-Treeᵉ
          ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ))) →
    cases-center-unique-direct-successor-combinator-Directed-Treeᵉ iᵉ xᵉ dᵉ ＝ᵉ pᵉ
  cases-contraction-unique-direct-successor-combinator-Directed-Treeᵉ iᵉ ._
    ( inlᵉ rᵉ)
    ( ._ ,ᵉ edge-to-root-combinator-Directed-Treeᵉ .iᵉ) =
    apᵉ
      ( λ uᵉ →
        cases-center-unique-direct-successor-combinator-Directed-Treeᵉ iᵉ
          ( root-Directed-Treeᵉ (Tᵉ iᵉ))
          ( inlᵉ uᵉ))
      ( eq-refl-root-Directed-Treeᵉ (Tᵉ iᵉ) rᵉ)
  cases-contraction-unique-direct-successor-combinator-Directed-Treeᵉ iᵉ ._
    ( inrᵉ fᵉ)
    ( ._ ,ᵉ edge-to-root-combinator-Directed-Treeᵉ .iᵉ) =
    ex-falsoᵉ (fᵉ reflᵉ)
  cases-contraction-unique-direct-successor-combinator-Directed-Treeᵉ iᵉ ._
    ( inlᵉ reflᵉ)
    ( ._ ,ᵉ edge-inclusion-combinator-Directed-Treeᵉ .iᵉ ._ yᵉ eᵉ) =
    ex-falsoᵉ (no-direct-successor-root-Directed-Treeᵉ (Tᵉ iᵉ) (yᵉ ,ᵉ eᵉ))
  cases-contraction-unique-direct-successor-combinator-Directed-Treeᵉ iᵉ xᵉ
    ( inrᵉ fᵉ)
    ( ._ ,ᵉ edge-inclusion-combinator-Directed-Treeᵉ .iᵉ .xᵉ yᵉ eᵉ) =
    apᵉ
      ( map-Σᵉ
        ( edge-combinator-Directed-Treeᵉ
          ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ))
        ( node-inclusion-combinator-Directed-Treeᵉ iᵉ)
        ( edge-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ))
      ( eq-is-contrᵉ
        ( unique-direct-successor-is-proper-node-Directed-Treeᵉ (Tᵉ iᵉ) xᵉ fᵉ))

  contraction-unique-direct-successor-combinator-Directed-Treeᵉ :
    ( xᵉ : node-combinator-Directed-Treeᵉ) →
    ( pᵉ :
      is-root-combinator-Directed-Treeᵉ xᵉ +ᵉ
      Σᵉ node-combinator-Directed-Treeᵉ (edge-combinator-Directed-Treeᵉ xᵉ)) →
    center-unique-direct-successor-combinator-Directed-Treeᵉ xᵉ ＝ᵉ pᵉ
  contraction-unique-direct-successor-combinator-Directed-Treeᵉ ._ (inlᵉ reflᵉ) =
    reflᵉ
  contraction-unique-direct-successor-combinator-Directed-Treeᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ)
    ( inrᵉ (yᵉ ,ᵉ eᵉ)) =
    apᵉ
      ( inrᵉ)
      ( cases-contraction-unique-direct-successor-combinator-Directed-Treeᵉ iᵉ xᵉ
        ( is-isolated-root-Directed-Treeᵉ (Tᵉ iᵉ) xᵉ)
        ( yᵉ ,ᵉ eᵉ))

  unique-direct-successor-combinator-Directed-Treeᵉ :
    unique-direct-successor-Directed-Graphᵉ
      ( graph-combinator-Directed-Treeᵉ)
      ( root-combinator-Directed-Treeᵉ)
  pr1ᵉ (unique-direct-successor-combinator-Directed-Treeᵉ xᵉ) =
    center-unique-direct-successor-combinator-Directed-Treeᵉ xᵉ
  pr2ᵉ (unique-direct-successor-combinator-Directed-Treeᵉ xᵉ) =
    contraction-unique-direct-successor-combinator-Directed-Treeᵉ xᵉ

  is-tree-combinator-Directed-Treeᵉ :
    is-tree-Directed-Graphᵉ graph-combinator-Directed-Treeᵉ
  is-tree-combinator-Directed-Treeᵉ =
    is-tree-unique-direct-successor-Directed-Graphᵉ
      graph-combinator-Directed-Treeᵉ
      root-combinator-Directed-Treeᵉ
      unique-direct-successor-combinator-Directed-Treeᵉ
      walk-to-root-combinator-Directed-Treeᵉ

  combinator-Directed-Treeᵉ : Directed-Treeᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ combinator-Directed-Treeᵉ = graph-combinator-Directed-Treeᵉ
  pr2ᵉ combinator-Directed-Treeᵉ = is-tree-combinator-Directed-Treeᵉ

  base-combinator-Directed-Treeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  base-combinator-Directed-Treeᵉ = base-Directed-Treeᵉ combinator-Directed-Treeᵉ

  is-proper-node-combinator-Directed-Treeᵉ :
    node-combinator-Directed-Treeᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-proper-node-combinator-Directed-Treeᵉ =
    is-proper-node-Directed-Treeᵉ combinator-Directed-Treeᵉ

  proper-node-combinator-Directed-Treeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  proper-node-combinator-Directed-Treeᵉ =
    proper-node-Directed-Treeᵉ combinator-Directed-Treeᵉ

  is-proper-node-inclusion-combinator-Directed-Treeᵉ :
    {iᵉ : Iᵉ} {xᵉ : node-Directed-Treeᵉ (Tᵉ iᵉ)} →
    is-proper-node-combinator-Directed-Treeᵉ
      ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ)
  is-proper-node-inclusion-combinator-Directed-Treeᵉ {iᵉ} {xᵉ} ()
```

## Properties

### The type of direct predecessors of `x : T i` is equivalent to the type of direct predecessors of the inclusion of `x` in `combinator T`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (Tᵉ : Iᵉ → Directed-Treeᵉ l2ᵉ l3ᵉ)
  (iᵉ : Iᵉ) (xᵉ : node-Directed-Treeᵉ (Tᵉ iᵉ))
  where

  direct-predecessor-combinator-Directed-Treeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  direct-predecessor-combinator-Directed-Treeᵉ =
    Σᵉ ( node-combinator-Directed-Treeᵉ Tᵉ)
      ( λ yᵉ →
        edge-combinator-Directed-Treeᵉ Tᵉ yᵉ
          ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ))

  map-compute-direct-predecessor-combinator-Directed-Treeᵉ :
    direct-predecessor-Directed-Treeᵉ (Tᵉ iᵉ) xᵉ →
    direct-predecessor-combinator-Directed-Treeᵉ
  pr1ᵉ (map-compute-direct-predecessor-combinator-Directed-Treeᵉ (yᵉ ,ᵉ eᵉ)) =
    node-inclusion-combinator-Directed-Treeᵉ iᵉ yᵉ
  pr2ᵉ (map-compute-direct-predecessor-combinator-Directed-Treeᵉ (yᵉ ,ᵉ eᵉ)) =
    edge-inclusion-combinator-Directed-Treeᵉ iᵉ yᵉ xᵉ eᵉ

  map-inv-compute-direct-predecessor-combinator-Directed-Treeᵉ :
    direct-predecessor-combinator-Directed-Treeᵉ →
    direct-predecessor-Directed-Treeᵉ (Tᵉ iᵉ) xᵉ
  map-inv-compute-direct-predecessor-combinator-Directed-Treeᵉ
    ( ._ ,ᵉ edge-inclusion-combinator-Directed-Treeᵉ .iᵉ yᵉ .xᵉ eᵉ) =
    ( yᵉ ,ᵉ eᵉ)

  is-section-map-inv-compute-direct-predecessor-combinator-Directed-Treeᵉ :
    ( map-compute-direct-predecessor-combinator-Directed-Treeᵉ ∘ᵉ
      map-inv-compute-direct-predecessor-combinator-Directed-Treeᵉ) ~ᵉ idᵉ
  is-section-map-inv-compute-direct-predecessor-combinator-Directed-Treeᵉ
    ( ._ ,ᵉ edge-inclusion-combinator-Directed-Treeᵉ .iᵉ yᵉ .xᵉ eᵉ) =
    reflᵉ

  is-retraction-map-inv-compute-direct-predecessor-combinator-Directed-Treeᵉ :
    ( map-inv-compute-direct-predecessor-combinator-Directed-Treeᵉ ∘ᵉ
      map-compute-direct-predecessor-combinator-Directed-Treeᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-compute-direct-predecessor-combinator-Directed-Treeᵉ
    ( yᵉ ,ᵉ eᵉ) =
    reflᵉ

  is-equiv-map-compute-direct-predecessor-combinator-Directed-Treeᵉ :
    is-equivᵉ map-compute-direct-predecessor-combinator-Directed-Treeᵉ
  is-equiv-map-compute-direct-predecessor-combinator-Directed-Treeᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-compute-direct-predecessor-combinator-Directed-Treeᵉ
      is-section-map-inv-compute-direct-predecessor-combinator-Directed-Treeᵉ
      is-retraction-map-inv-compute-direct-predecessor-combinator-Directed-Treeᵉ

  compute-direct-predecessor-combinator-Directed-Treeᵉ :
    direct-predecessor-Directed-Treeᵉ (Tᵉ iᵉ) xᵉ ≃ᵉ
    direct-predecessor-combinator-Directed-Treeᵉ
  pr1ᵉ compute-direct-predecessor-combinator-Directed-Treeᵉ =
    map-compute-direct-predecessor-combinator-Directed-Treeᵉ
  pr2ᵉ compute-direct-predecessor-combinator-Directed-Treeᵉ =
    is-equiv-map-compute-direct-predecessor-combinator-Directed-Treeᵉ
```

### If `e` is an edge from `node-inclusion i x` to `node-inclusion j y`, then `i ＝ j`

```agda
eq-index-edge-combinator-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (Tᵉ : Iᵉ → Directed-Treeᵉ l2ᵉ l3ᵉ)
  {iᵉ : Iᵉ} (xᵉ : node-Directed-Treeᵉ (Tᵉ iᵉ))
  {jᵉ : Iᵉ} (yᵉ : node-Directed-Treeᵉ (Tᵉ jᵉ)) →
  edge-combinator-Directed-Treeᵉ Tᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ)
    ( node-inclusion-combinator-Directed-Treeᵉ jᵉ yᵉ) →
  iᵉ ＝ᵉ jᵉ
eq-index-edge-combinator-Directed-Treeᵉ Tᵉ xᵉ yᵉ
  ( edge-inclusion-combinator-Directed-Treeᵉ _ .xᵉ .yᵉ eᵉ) = reflᵉ
```

### The base of the combinator tree of a family `T` of directed tree indexed by `I` is equivalent to `I`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (Tᵉ : Iᵉ → Directed-Treeᵉ l2ᵉ l3ᵉ)
  where

  node-base-index-combinator-Directed-Treeᵉ :
    Iᵉ → node-combinator-Directed-Treeᵉ Tᵉ
  node-base-index-combinator-Directed-Treeᵉ iᵉ =
    node-inclusion-combinator-Directed-Treeᵉ iᵉ (root-Directed-Treeᵉ (Tᵉ iᵉ))

  edge-base-index-combinator-Directed-Treeᵉ :
    (iᵉ : Iᵉ) →
    edge-combinator-Directed-Treeᵉ Tᵉ
      ( node-base-index-combinator-Directed-Treeᵉ iᵉ)
      ( root-combinator-Directed-Treeᵉ)
  edge-base-index-combinator-Directed-Treeᵉ iᵉ =
    edge-to-root-combinator-Directed-Treeᵉ iᵉ

  base-index-combinator-Directed-Treeᵉ :
    Iᵉ → base-combinator-Directed-Treeᵉ Tᵉ
  pr1ᵉ (base-index-combinator-Directed-Treeᵉ iᵉ) =
    node-base-index-combinator-Directed-Treeᵉ iᵉ
  pr2ᵉ (base-index-combinator-Directed-Treeᵉ iᵉ) =
    edge-base-index-combinator-Directed-Treeᵉ iᵉ

  index-base-combinator-Directed-Treeᵉ :
    base-combinator-Directed-Treeᵉ Tᵉ → Iᵉ
  index-base-combinator-Directed-Treeᵉ
    ( ._ ,ᵉ edge-to-root-combinator-Directed-Treeᵉ iᵉ) =
    iᵉ

  is-section-index-base-combinator-Directed-Treeᵉ :
    ( base-index-combinator-Directed-Treeᵉ ∘ᵉ
      index-base-combinator-Directed-Treeᵉ) ~ᵉ idᵉ
  is-section-index-base-combinator-Directed-Treeᵉ
    ( ._ ,ᵉ edge-to-root-combinator-Directed-Treeᵉ iᵉ) =
    reflᵉ

  is-retraction-index-base-combinator-Directed-Treeᵉ :
    ( index-base-combinator-Directed-Treeᵉ ∘ᵉ
      base-index-combinator-Directed-Treeᵉ) ~ᵉ idᵉ
  is-retraction-index-base-combinator-Directed-Treeᵉ iᵉ = reflᵉ

  is-equiv-base-index-combinator-Directed-Treeᵉ :
    is-equivᵉ base-index-combinator-Directed-Treeᵉ
  is-equiv-base-index-combinator-Directed-Treeᵉ =
    is-equiv-is-invertibleᵉ
      index-base-combinator-Directed-Treeᵉ
      is-section-index-base-combinator-Directed-Treeᵉ
      is-retraction-index-base-combinator-Directed-Treeᵉ

  equiv-base-index-combinator-Directed-Treeᵉ :
    Iᵉ ≃ᵉ base-combinator-Directed-Treeᵉ Tᵉ
  pr1ᵉ equiv-base-index-combinator-Directed-Treeᵉ =
    base-index-combinator-Directed-Treeᵉ
  pr2ᵉ equiv-base-index-combinator-Directed-Treeᵉ =
    is-equiv-base-index-combinator-Directed-Treeᵉ
```

### The type of nodes of the combinator tree of `T` is equivalent to the dependent sum of the types of nodes of each `T i`, plus a root

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (Tᵉ : Iᵉ → Directed-Treeᵉ l2ᵉ l3ᵉ)
  where

  map-compute-node-combinator-Directed-Treeᵉ :
    Maybeᵉ (Σᵉ Iᵉ (node-Directed-Treeᵉ ∘ᵉ Tᵉ)) →
    node-combinator-Directed-Treeᵉ Tᵉ
  map-compute-node-combinator-Directed-Treeᵉ (inlᵉ (iᵉ ,ᵉ xᵉ)) =
    node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ
  map-compute-node-combinator-Directed-Treeᵉ (inrᵉ _) =
    root-combinator-Directed-Treeᵉ

  map-inv-compute-node-combinator-Directed-Treeᵉ :
    node-combinator-Directed-Treeᵉ Tᵉ →
    Maybeᵉ (Σᵉ Iᵉ (node-Directed-Treeᵉ ∘ᵉ Tᵉ))
  map-inv-compute-node-combinator-Directed-Treeᵉ root-combinator-Directed-Treeᵉ =
    exception-Maybeᵉ
  map-inv-compute-node-combinator-Directed-Treeᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ) =
    unit-Maybeᵉ (iᵉ ,ᵉ xᵉ)

  is-section-map-inv-compute-node-combinator-Directed-Treeᵉ :
    ( map-compute-node-combinator-Directed-Treeᵉ ∘ᵉ
      map-inv-compute-node-combinator-Directed-Treeᵉ) ~ᵉ idᵉ
  is-section-map-inv-compute-node-combinator-Directed-Treeᵉ
    root-combinator-Directed-Treeᵉ =
    reflᵉ
  is-section-map-inv-compute-node-combinator-Directed-Treeᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ) =
    reflᵉ

  is-retraction-map-inv-compute-node-combinator-Directed-Treeᵉ :
    ( map-inv-compute-node-combinator-Directed-Treeᵉ ∘ᵉ
      map-compute-node-combinator-Directed-Treeᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-compute-node-combinator-Directed-Treeᵉ (inlᵉ (iᵉ ,ᵉ xᵉ)) =
    reflᵉ
  is-retraction-map-inv-compute-node-combinator-Directed-Treeᵉ (inrᵉ _) = reflᵉ

  is-equiv-map-compute-node-combinator-Directed-Treeᵉ :
    is-equivᵉ map-compute-node-combinator-Directed-Treeᵉ
  is-equiv-map-compute-node-combinator-Directed-Treeᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-compute-node-combinator-Directed-Treeᵉ
      is-section-map-inv-compute-node-combinator-Directed-Treeᵉ
      is-retraction-map-inv-compute-node-combinator-Directed-Treeᵉ

  compute-node-combinator-Directed-Treeᵉ :
    Maybeᵉ (Σᵉ Iᵉ (node-Directed-Treeᵉ ∘ᵉ Tᵉ)) ≃ᵉ node-combinator-Directed-Treeᵉ Tᵉ
  pr1ᵉ compute-node-combinator-Directed-Treeᵉ =
    map-compute-node-combinator-Directed-Treeᵉ
  pr2ᵉ compute-node-combinator-Directed-Treeᵉ =
    is-equiv-map-compute-node-combinator-Directed-Treeᵉ
```

### The type of proper nodes of the combinator tree of `T` is equivalent to the dependent sum of the types of nodes of each `T i`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (Tᵉ : Iᵉ → Directed-Treeᵉ l2ᵉ l3ᵉ)
  where

  map-compute-proper-node-combinator-Directed-Treeᵉ :
    Σᵉ Iᵉ (node-Directed-Treeᵉ ∘ᵉ Tᵉ) →
    proper-node-combinator-Directed-Treeᵉ Tᵉ
  map-compute-proper-node-combinator-Directed-Treeᵉ (iᵉ ,ᵉ xᵉ) =
    ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ ,ᵉ
      is-proper-node-inclusion-combinator-Directed-Treeᵉ Tᵉ)

  map-inv-compute-proper-node-combinator-Directed-Treeᵉ :
    proper-node-combinator-Directed-Treeᵉ Tᵉ →
    Σᵉ Iᵉ (node-Directed-Treeᵉ ∘ᵉ Tᵉ)
  map-inv-compute-proper-node-combinator-Directed-Treeᵉ
    ( root-combinator-Directed-Treeᵉ ,ᵉ Hᵉ) =
    ex-falsoᵉ (Hᵉ reflᵉ)
  map-inv-compute-proper-node-combinator-Directed-Treeᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ ,ᵉ Hᵉ) = (iᵉ ,ᵉ xᵉ)

  is-section-map-inv-compute-proper-node-combinator-Directed-Treeᵉ :
    ( map-compute-proper-node-combinator-Directed-Treeᵉ ∘ᵉ
      map-inv-compute-proper-node-combinator-Directed-Treeᵉ) ~ᵉ idᵉ
  is-section-map-inv-compute-proper-node-combinator-Directed-Treeᵉ
    ( root-combinator-Directed-Treeᵉ ,ᵉ Hᵉ) =
    ex-falsoᵉ (Hᵉ reflᵉ)
  is-section-map-inv-compute-proper-node-combinator-Directed-Treeᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ ,ᵉ Hᵉ) =
    eq-pair-eq-fiberᵉ
      ( eq-is-propᵉ
        ( is-prop-is-proper-node-Directed-Treeᵉ
          ( combinator-Directed-Treeᵉ Tᵉ)
          ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ)))

  is-retraction-map-inv-compute-proper-node-combinator-Directed-Treeᵉ :
    ( map-inv-compute-proper-node-combinator-Directed-Treeᵉ ∘ᵉ
      map-compute-proper-node-combinator-Directed-Treeᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-compute-proper-node-combinator-Directed-Treeᵉ (iᵉ ,ᵉ xᵉ) =
    reflᵉ

  is-equiv-map-compute-proper-node-combinator-Directed-Treeᵉ :
    is-equivᵉ map-compute-proper-node-combinator-Directed-Treeᵉ
  is-equiv-map-compute-proper-node-combinator-Directed-Treeᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-compute-proper-node-combinator-Directed-Treeᵉ
      is-section-map-inv-compute-proper-node-combinator-Directed-Treeᵉ
      is-retraction-map-inv-compute-proper-node-combinator-Directed-Treeᵉ

  compute-proper-node-combinator-Directed-Treeᵉ :
    Σᵉ Iᵉ (node-Directed-Treeᵉ ∘ᵉ Tᵉ) ≃ᵉ proper-node-combinator-Directed-Treeᵉ Tᵉ
  pr1ᵉ compute-proper-node-combinator-Directed-Treeᵉ =
    map-compute-proper-node-combinator-Directed-Treeᵉ
  pr2ᵉ compute-proper-node-combinator-Directed-Treeᵉ =
    is-equiv-map-compute-proper-node-combinator-Directed-Treeᵉ
```

### The fibers at a base element `b` of the comibinator of a family `T` of trees is equivalent to `T (index-base b)`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (Tᵉ : Iᵉ → Directed-Treeᵉ l2ᵉ l3ᵉ)
  where

  node-fiber-combinator-Directed-Treeᵉ :
    (iᵉ : Iᵉ) →
    node-Directed-Treeᵉ (Tᵉ iᵉ) →
    node-fiber-Directed-Treeᵉ
      ( combinator-Directed-Treeᵉ Tᵉ)
      ( node-base-index-combinator-Directed-Treeᵉ Tᵉ iᵉ)
  pr1ᵉ (node-fiber-combinator-Directed-Treeᵉ iᵉ xᵉ) =
    node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ
  pr2ᵉ (node-fiber-combinator-Directed-Treeᵉ iᵉ xᵉ) =
    walk-inclusion-combinator-Directed-Treeᵉ Tᵉ iᵉ xᵉ
      ( root-Directed-Treeᵉ (Tᵉ iᵉ))
      ( walk-to-root-Directed-Treeᵉ (Tᵉ iᵉ) xᵉ)

  compute-map-Σ-node-fiber-combinator-Directed-Treeᵉ :
    ( map-Σᵉ
      ( λ bᵉ →
        Σᵉ ( node-combinator-Directed-Treeᵉ Tᵉ)
          ( λ xᵉ →
            walk-combinator-Directed-Treeᵉ Tᵉ xᵉ
              ( node-base-Directed-Treeᵉ (combinator-Directed-Treeᵉ Tᵉ) bᵉ)))
      ( base-index-combinator-Directed-Treeᵉ Tᵉ)
      ( node-fiber-combinator-Directed-Treeᵉ)) ~ᵉ
    map-equivᵉ
      ( ( compute-proper-node-Directed-Treeᵉ (combinator-Directed-Treeᵉ Tᵉ)) ∘eᵉ
        ( compute-proper-node-combinator-Directed-Treeᵉ Tᵉ))
  compute-map-Σ-node-fiber-combinator-Directed-Treeᵉ (iᵉ ,ᵉ xᵉ) =
    invᵉ
      ( eq-compute-proper-node-Directed-Treeᵉ
        ( combinator-Directed-Treeᵉ Tᵉ)
        ( is-proper-node-inclusion-combinator-Directed-Treeᵉ Tᵉ)
        ( base-index-combinator-Directed-Treeᵉ Tᵉ iᵉ)
        ( walk-inclusion-combinator-Directed-Treeᵉ Tᵉ iᵉ xᵉ
          ( root-Directed-Treeᵉ (Tᵉ iᵉ))
          ( walk-to-root-Directed-Treeᵉ (Tᵉ iᵉ) xᵉ)))

  is-equiv-map-Σ-node-fiber-combinator-Directed-Treeᵉ :
    is-equivᵉ
      ( map-Σᵉ
        ( λ bᵉ →
          Σᵉ ( node-combinator-Directed-Treeᵉ Tᵉ)
            ( λ xᵉ →
              walk-combinator-Directed-Treeᵉ Tᵉ xᵉ
                ( node-base-Directed-Treeᵉ (combinator-Directed-Treeᵉ Tᵉ) bᵉ)))
        ( base-index-combinator-Directed-Treeᵉ Tᵉ)
        ( node-fiber-combinator-Directed-Treeᵉ))
  is-equiv-map-Σ-node-fiber-combinator-Directed-Treeᵉ =
    is-equiv-htpyᵉ
      ( map-equivᵉ
        ( ( compute-proper-node-Directed-Treeᵉ (combinator-Directed-Treeᵉ Tᵉ)) ∘eᵉ
          ( compute-proper-node-combinator-Directed-Treeᵉ Tᵉ)))
      ( compute-map-Σ-node-fiber-combinator-Directed-Treeᵉ)
      ( is-equiv-map-equivᵉ
        ( ( compute-proper-node-Directed-Treeᵉ (combinator-Directed-Treeᵉ Tᵉ)) ∘eᵉ
          ( compute-proper-node-combinator-Directed-Treeᵉ Tᵉ)))

  is-equiv-node-fiber-combinator-Directed-Treeᵉ :
    (iᵉ : Iᵉ) → is-equivᵉ (node-fiber-combinator-Directed-Treeᵉ iᵉ)
  is-equiv-node-fiber-combinator-Directed-Treeᵉ =
    is-fiberwise-equiv-is-equiv-map-Σᵉ
      ( λ bᵉ →
        Σᵉ ( node-combinator-Directed-Treeᵉ Tᵉ)
          ( λ xᵉ →
            walk-combinator-Directed-Treeᵉ Tᵉ xᵉ
              ( node-base-Directed-Treeᵉ (combinator-Directed-Treeᵉ Tᵉ) bᵉ)))
      ( base-index-combinator-Directed-Treeᵉ Tᵉ)
      ( node-fiber-combinator-Directed-Treeᵉ)
      ( is-equiv-base-index-combinator-Directed-Treeᵉ Tᵉ)
      ( is-equiv-map-Σ-node-fiber-combinator-Directed-Treeᵉ)

  edge-fiber-combinator-Directed-Treeᵉ :
    (iᵉ : Iᵉ) (xᵉ yᵉ : node-Directed-Treeᵉ (Tᵉ iᵉ)) →
    edge-Directed-Treeᵉ (Tᵉ iᵉ) xᵉ yᵉ →
    edge-fiber-Directed-Treeᵉ
      ( combinator-Directed-Treeᵉ Tᵉ)
      ( node-base-index-combinator-Directed-Treeᵉ Tᵉ iᵉ)
      ( node-fiber-combinator-Directed-Treeᵉ iᵉ xᵉ)
      ( node-fiber-combinator-Directed-Treeᵉ iᵉ yᵉ)
  pr1ᵉ (edge-fiber-combinator-Directed-Treeᵉ iᵉ xᵉ yᵉ eᵉ) =
    edge-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ yᵉ eᵉ
  pr2ᵉ (edge-fiber-combinator-Directed-Treeᵉ iᵉ xᵉ yᵉ eᵉ) =
    apᵉ
      ( walk-inclusion-combinator-Directed-Treeᵉ Tᵉ iᵉ xᵉ
        ( root-Directed-Treeᵉ (Tᵉ iᵉ)))
      ( eq-is-contrᵉ (unique-walk-to-root-Directed-Treeᵉ (Tᵉ iᵉ) xᵉ))

  hom-fiber-combinator-Directed-Treeᵉ :
    (iᵉ : Iᵉ) →
    hom-Directed-Treeᵉ
      ( Tᵉ iᵉ)
      ( fiber-Directed-Treeᵉ
        ( combinator-Directed-Treeᵉ Tᵉ)
        ( node-base-index-combinator-Directed-Treeᵉ Tᵉ iᵉ))
  pr1ᵉ (hom-fiber-combinator-Directed-Treeᵉ iᵉ) =
    node-fiber-combinator-Directed-Treeᵉ iᵉ
  pr2ᵉ (hom-fiber-combinator-Directed-Treeᵉ iᵉ) =
    edge-fiber-combinator-Directed-Treeᵉ iᵉ

  is-equiv-hom-fiber-combinator-Directed-Treeᵉ :
    (iᵉ : Iᵉ) →
    is-equiv-hom-Directed-Treeᵉ
      ( Tᵉ iᵉ)
      ( fiber-Directed-Treeᵉ
        ( combinator-Directed-Treeᵉ Tᵉ)
        ( node-base-index-combinator-Directed-Treeᵉ Tᵉ iᵉ))
      ( hom-fiber-combinator-Directed-Treeᵉ iᵉ)
  is-equiv-hom-fiber-combinator-Directed-Treeᵉ iᵉ =
    is-equiv-is-equiv-node-hom-Directed-Treeᵉ
      ( Tᵉ iᵉ)
      ( fiber-Directed-Treeᵉ
        ( combinator-Directed-Treeᵉ Tᵉ)
        ( node-base-index-combinator-Directed-Treeᵉ Tᵉ iᵉ))
      ( hom-fiber-combinator-Directed-Treeᵉ iᵉ)
      ( is-equiv-node-fiber-combinator-Directed-Treeᵉ iᵉ)

  fiber-combinator-Directed-Treeᵉ :
    (iᵉ : Iᵉ) →
    equiv-Directed-Treeᵉ
      ( Tᵉ iᵉ)
      ( fiber-Directed-Treeᵉ
        ( combinator-Directed-Treeᵉ Tᵉ)
        ( node-base-index-combinator-Directed-Treeᵉ Tᵉ iᵉ))
  fiber-combinator-Directed-Treeᵉ iᵉ =
    equiv-is-equiv-hom-Directed-Treeᵉ
      ( Tᵉ iᵉ)
      ( fiber-Directed-Treeᵉ
        ( combinator-Directed-Treeᵉ Tᵉ)
        ( node-base-index-combinator-Directed-Treeᵉ Tᵉ iᵉ))
      ( hom-fiber-combinator-Directed-Treeᵉ iᵉ)
      ( is-equiv-hom-fiber-combinator-Directed-Treeᵉ iᵉ)
```

### Any tree is the combinator tree of the fibers at the nodes equipped with edges to the root

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ)
  where

  node-combinator-fiber-base-Directed-Treeᵉ :
    node-combinator-Directed-Treeᵉ (fiber-base-Directed-Treeᵉ Tᵉ) →
    node-Directed-Treeᵉ Tᵉ
  node-combinator-fiber-base-Directed-Treeᵉ root-combinator-Directed-Treeᵉ =
    root-Directed-Treeᵉ Tᵉ
  node-combinator-fiber-base-Directed-Treeᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ bᵉ (xᵉ ,ᵉ wᵉ)) = xᵉ

  cases-map-inv-node-combinator-fiber-base-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) →
    is-root-Directed-Treeᵉ Tᵉ xᵉ +ᵉ
    Σᵉ ( base-Directed-Treeᵉ Tᵉ)
      ( walk-Directed-Treeᵉ Tᵉ xᵉ ∘ᵉ node-base-Directed-Treeᵉ Tᵉ) →
    node-combinator-Directed-Treeᵉ (fiber-base-Directed-Treeᵉ Tᵉ)
  cases-map-inv-node-combinator-fiber-base-Directed-Treeᵉ ._ (inlᵉ reflᵉ) =
    root-combinator-Directed-Treeᵉ
  cases-map-inv-node-combinator-fiber-base-Directed-Treeᵉ xᵉ (inrᵉ (bᵉ ,ᵉ wᵉ)) =
    node-inclusion-combinator-Directed-Treeᵉ bᵉ (xᵉ ,ᵉ wᵉ)

  map-inv-node-combinator-fiber-base-Directed-Treeᵉ :
    node-Directed-Treeᵉ Tᵉ →
    node-combinator-Directed-Treeᵉ (fiber-base-Directed-Treeᵉ Tᵉ)
  map-inv-node-combinator-fiber-base-Directed-Treeᵉ xᵉ =
    cases-map-inv-node-combinator-fiber-base-Directed-Treeᵉ xᵉ
      ( is-root-or-walk-to-base-Directed-Treeᵉ Tᵉ xᵉ)

  cases-is-section-map-inv-node-combinator-fiber-base-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Tᵉ) →
    (Hᵉ :
      is-root-Directed-Treeᵉ Tᵉ xᵉ +ᵉ
      Σᵉ ( base-Directed-Treeᵉ Tᵉ)
        ( walk-Directed-Treeᵉ Tᵉ xᵉ ∘ᵉ node-base-Directed-Treeᵉ Tᵉ)) →
    node-combinator-fiber-base-Directed-Treeᵉ
      ( cases-map-inv-node-combinator-fiber-base-Directed-Treeᵉ xᵉ Hᵉ) ＝ᵉ xᵉ
  cases-is-section-map-inv-node-combinator-fiber-base-Directed-Treeᵉ ._
    ( inlᵉ reflᵉ) =
    reflᵉ
  cases-is-section-map-inv-node-combinator-fiber-base-Directed-Treeᵉ xᵉ
    ( inrᵉ (bᵉ ,ᵉ wᵉ)) =
    reflᵉ

  is-section-map-inv-node-combinator-fiber-base-Directed-Treeᵉ :
    ( node-combinator-fiber-base-Directed-Treeᵉ ∘ᵉ
      map-inv-node-combinator-fiber-base-Directed-Treeᵉ) ~ᵉ idᵉ
  is-section-map-inv-node-combinator-fiber-base-Directed-Treeᵉ xᵉ =
    cases-is-section-map-inv-node-combinator-fiber-base-Directed-Treeᵉ xᵉ
      ( is-root-or-walk-to-base-Directed-Treeᵉ Tᵉ xᵉ)

  is-retraction-map-inv-node-combinator-fiber-base-Directed-Treeᵉ :
    ( map-inv-node-combinator-fiber-base-Directed-Treeᵉ ∘ᵉ
      node-combinator-fiber-base-Directed-Treeᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-node-combinator-fiber-base-Directed-Treeᵉ
    root-combinator-Directed-Treeᵉ =
    apᵉ
      ( cases-map-inv-node-combinator-fiber-base-Directed-Treeᵉ
        ( root-Directed-Treeᵉ Tᵉ))
      ( eq-is-contrᵉ
        ( unique-walk-to-base-Directed-Treeᵉ Tᵉ (root-Directed-Treeᵉ Tᵉ)))
  is-retraction-map-inv-node-combinator-fiber-base-Directed-Treeᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ bᵉ (xᵉ ,ᵉ wᵉ)) =
    apᵉ
      ( cases-map-inv-node-combinator-fiber-base-Directed-Treeᵉ xᵉ)
      ( eq-is-contrᵉ ( unique-walk-to-base-Directed-Treeᵉ Tᵉ xᵉ))

  is-equiv-node-combinator-fiber-base-Directed-Treeᵉ :
    is-equivᵉ node-combinator-fiber-base-Directed-Treeᵉ
  is-equiv-node-combinator-fiber-base-Directed-Treeᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-node-combinator-fiber-base-Directed-Treeᵉ
      is-section-map-inv-node-combinator-fiber-base-Directed-Treeᵉ
      is-retraction-map-inv-node-combinator-fiber-base-Directed-Treeᵉ

  equiv-node-combinator-fiber-base-Directed-Treeᵉ :
    node-combinator-Directed-Treeᵉ (fiber-base-Directed-Treeᵉ Tᵉ) ≃ᵉ
    node-Directed-Treeᵉ Tᵉ
  pr1ᵉ equiv-node-combinator-fiber-base-Directed-Treeᵉ =
    node-combinator-fiber-base-Directed-Treeᵉ
  pr2ᵉ equiv-node-combinator-fiber-base-Directed-Treeᵉ =
    is-equiv-node-combinator-fiber-base-Directed-Treeᵉ

  edge-combinator-fiber-base-Directed-Treeᵉ :
    (xᵉ yᵉ : node-combinator-Directed-Treeᵉ (fiber-base-Directed-Treeᵉ Tᵉ)) →
    edge-combinator-Directed-Treeᵉ (fiber-base-Directed-Treeᵉ Tᵉ) xᵉ yᵉ →
    edge-Directed-Treeᵉ Tᵉ
      ( node-combinator-fiber-base-Directed-Treeᵉ xᵉ)
      ( node-combinator-fiber-base-Directed-Treeᵉ yᵉ)
  edge-combinator-fiber-base-Directed-Treeᵉ ._ ._
    ( edge-to-root-combinator-Directed-Treeᵉ (bᵉ ,ᵉ eᵉ)) = eᵉ
  edge-combinator-fiber-base-Directed-Treeᵉ ._ ._
    ( edge-inclusion-combinator-Directed-Treeᵉ iᵉ (uᵉ ,ᵉ .ᵉ_) yᵉ (eᵉ ,ᵉ reflᵉ)) = eᵉ

  hom-combinator-fiber-base-Directed-Treeᵉ :
    hom-Directed-Treeᵉ
      ( combinator-Directed-Treeᵉ (fiber-base-Directed-Treeᵉ Tᵉ))
      ( Tᵉ)
  pr1ᵉ hom-combinator-fiber-base-Directed-Treeᵉ =
    node-combinator-fiber-base-Directed-Treeᵉ
  pr2ᵉ hom-combinator-fiber-base-Directed-Treeᵉ =
    edge-combinator-fiber-base-Directed-Treeᵉ

  is-equiv-combinator-fiber-base-Directed-Treeᵉ :
    is-equiv-hom-Directed-Treeᵉ
      ( combinator-Directed-Treeᵉ (fiber-base-Directed-Treeᵉ Tᵉ))
      ( Tᵉ)
      ( hom-combinator-fiber-base-Directed-Treeᵉ)
  is-equiv-combinator-fiber-base-Directed-Treeᵉ =
    is-equiv-is-equiv-node-hom-Directed-Treeᵉ
      ( combinator-Directed-Treeᵉ (fiber-base-Directed-Treeᵉ Tᵉ))
      ( Tᵉ)
      ( hom-combinator-fiber-base-Directed-Treeᵉ)
      ( is-equiv-node-combinator-fiber-base-Directed-Treeᵉ)

  combinator-fiber-base-Directed-Treeᵉ :
    equiv-Directed-Treeᵉ
      ( combinator-Directed-Treeᵉ (fiber-base-Directed-Treeᵉ Tᵉ))
      ( Tᵉ)
  combinator-fiber-base-Directed-Treeᵉ =
    equiv-is-equiv-hom-Directed-Treeᵉ
      ( combinator-Directed-Treeᵉ (fiber-base-Directed-Treeᵉ Tᵉ))
      ( Tᵉ)
      ( hom-combinator-fiber-base-Directed-Treeᵉ)
      ( is-equiv-combinator-fiber-base-Directed-Treeᵉ)
```