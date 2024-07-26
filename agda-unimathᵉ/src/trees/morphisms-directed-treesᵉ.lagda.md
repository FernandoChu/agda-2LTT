# Morphisms of directed trees

```agda
module trees.morphisms-directed-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-transportᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.morphisms-directed-graphsᵉ
open import graph-theory.walks-directed-graphsᵉ

open import trees.directed-treesᵉ
```

</details>

## Idea

Aᵉ **morphismᵉ ofᵉ directedᵉ trees**ᵉ fromᵉ `S`ᵉ to `T`ᵉ isᵉ aᵉ morphismᵉ betweenᵉ theirᵉ
underlyingᵉ directedᵉ graphs.ᵉ

## Definitions

### Morphisms of directed trees

```agda
hom-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
hom-Directed-Treeᵉ Sᵉ Tᵉ =
  hom-Directed-Graphᵉ (graph-Directed-Treeᵉ Sᵉ) (graph-Directed-Treeᵉ Tᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ)
  (fᵉ : hom-Directed-Treeᵉ Sᵉ Tᵉ)
  where

  node-hom-Directed-Treeᵉ : node-Directed-Treeᵉ Sᵉ → node-Directed-Treeᵉ Tᵉ
  node-hom-Directed-Treeᵉ =
    vertex-hom-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)

  edge-hom-Directed-Treeᵉ :
    {xᵉ yᵉ : node-Directed-Treeᵉ Sᵉ} →
    edge-Directed-Treeᵉ Sᵉ xᵉ yᵉ →
    edge-Directed-Treeᵉ Tᵉ (node-hom-Directed-Treeᵉ xᵉ) (node-hom-Directed-Treeᵉ yᵉ)
  edge-hom-Directed-Treeᵉ =
    edge-hom-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)

  direct-predecessor-hom-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Sᵉ) →
    Σᵉ ( node-Directed-Treeᵉ Sᵉ) (λ yᵉ → edge-Directed-Treeᵉ Sᵉ yᵉ xᵉ) →
    Σᵉ ( node-Directed-Treeᵉ Tᵉ)
      ( λ yᵉ → edge-Directed-Treeᵉ Tᵉ yᵉ (node-hom-Directed-Treeᵉ xᵉ))
  direct-predecessor-hom-Directed-Treeᵉ xᵉ =
    map-Σᵉ
      ( λ yᵉ → edge-Directed-Treeᵉ Tᵉ yᵉ (node-hom-Directed-Treeᵉ xᵉ))
      ( node-hom-Directed-Treeᵉ)
      ( λ yᵉ → edge-hom-Directed-Treeᵉ)

  walk-hom-Directed-Treeᵉ :
    {xᵉ yᵉ : node-Directed-Treeᵉ Sᵉ} →
    walk-Directed-Treeᵉ Sᵉ xᵉ yᵉ →
    walk-Directed-Treeᵉ Tᵉ (node-hom-Directed-Treeᵉ xᵉ) (node-hom-Directed-Treeᵉ yᵉ)
  walk-hom-Directed-Treeᵉ =
    walk-hom-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)
```

### Identity morphisms of directed trees

```agda
id-hom-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) → hom-Directed-Treeᵉ Tᵉ Tᵉ
id-hom-Directed-Treeᵉ Tᵉ =
  id-hom-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ)
```

### Composition of morphisms of directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Rᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Sᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ) (Tᵉ : Directed-Treeᵉ l5ᵉ l6ᵉ)
  (gᵉ : hom-Directed-Treeᵉ Sᵉ Tᵉ) (fᵉ : hom-Directed-Treeᵉ Rᵉ Sᵉ)
  where

  node-comp-hom-Directed-Treeᵉ :
    node-Directed-Treeᵉ Rᵉ → node-Directed-Treeᵉ Tᵉ
  node-comp-hom-Directed-Treeᵉ =
    vertex-comp-hom-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Rᵉ)
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( gᵉ)
      ( fᵉ)

  edge-comp-hom-Directed-Treeᵉ :
    (xᵉ yᵉ : node-Directed-Treeᵉ Rᵉ) (eᵉ : edge-Directed-Treeᵉ Rᵉ xᵉ yᵉ) →
    edge-Directed-Treeᵉ Tᵉ
      ( node-comp-hom-Directed-Treeᵉ xᵉ)
      ( node-comp-hom-Directed-Treeᵉ yᵉ)
  edge-comp-hom-Directed-Treeᵉ =
    edge-comp-hom-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Rᵉ)
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( gᵉ)
      ( fᵉ)

  comp-hom-Directed-Treeᵉ :
    hom-Directed-Treeᵉ Rᵉ Tᵉ
  comp-hom-Directed-Treeᵉ =
    comp-hom-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Rᵉ)
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( gᵉ)
      ( fᵉ)
```

### Homotopies of morphisms of directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ)
  (fᵉ gᵉ : hom-Directed-Treeᵉ Sᵉ Tᵉ)
  where

  htpy-hom-Directed-Treeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-hom-Directed-Treeᵉ =
    htpy-hom-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)
      ( gᵉ)

  node-htpy-hom-Directed-Treeᵉ :
    htpy-hom-Directed-Treeᵉ →
    node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ ~ᵉ node-hom-Directed-Treeᵉ Sᵉ Tᵉ gᵉ
  node-htpy-hom-Directed-Treeᵉ =
    vertex-htpy-hom-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)
      ( gᵉ)

  edge-htpy-hom-Directed-Treeᵉ :
    ( αᵉ : htpy-hom-Directed-Treeᵉ) →
    ( xᵉ yᵉ : node-Directed-Treeᵉ Sᵉ) (eᵉ : edge-Directed-Treeᵉ Sᵉ xᵉ yᵉ) →
    binary-trᵉ
      ( edge-Directed-Treeᵉ Tᵉ)
      ( node-htpy-hom-Directed-Treeᵉ αᵉ xᵉ)
      ( node-htpy-hom-Directed-Treeᵉ αᵉ yᵉ)
      ( edge-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ eᵉ) ＝ᵉ
    edge-hom-Directed-Treeᵉ Sᵉ Tᵉ gᵉ eᵉ
  edge-htpy-hom-Directed-Treeᵉ =
    edge-htpy-hom-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)
      ( gᵉ)

  direct-predecessor-htpy-hom-Directed-Treeᵉ :
    ( αᵉ : htpy-hom-Directed-Treeᵉ) →
    ( xᵉ : node-Directed-Treeᵉ Sᵉ) →
    ( ( totᵉ
        ( λ yᵉ →
          trᵉ
            ( edge-Directed-Treeᵉ Tᵉ yᵉ)
            ( node-htpy-hom-Directed-Treeᵉ αᵉ xᵉ))) ∘ᵉ
      ( direct-predecessor-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ)) ~ᵉ
    ( direct-predecessor-hom-Directed-Treeᵉ Sᵉ Tᵉ gᵉ xᵉ)
  direct-predecessor-htpy-hom-Directed-Treeᵉ αᵉ xᵉ (yᵉ ,ᵉ eᵉ) =
    eq-pair-Σᵉ
      ( node-htpy-hom-Directed-Treeᵉ αᵉ yᵉ)
      ( ( compute-binary-trᵉ
          ( edge-Directed-Treeᵉ Tᵉ)
          ( node-htpy-hom-Directed-Treeᵉ αᵉ yᵉ)
          ( node-htpy-hom-Directed-Treeᵉ αᵉ xᵉ)
          ( edge-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ eᵉ)) ∙ᵉ
        ( edge-htpy-hom-Directed-Treeᵉ αᵉ yᵉ xᵉ eᵉ))
```

### The reflexivity homotopy of morphisms of directed trees

```agda
refl-htpy-hom-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ) →
  (fᵉ : hom-Directed-Treeᵉ Sᵉ Tᵉ) → htpy-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ fᵉ
refl-htpy-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ =
  refl-htpy-hom-Directed-Graphᵉ
    ( graph-Directed-Treeᵉ Sᵉ)
    ( graph-Directed-Treeᵉ Tᵉ)
    ( fᵉ)
```

## Properties

### Homotopies characterize identifications of morphisms of directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ)
  (fᵉ : hom-Directed-Treeᵉ Sᵉ Tᵉ)
  where

  is-torsorial-htpy-hom-Directed-Treeᵉ :
    is-torsorialᵉ (htpy-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
  is-torsorial-htpy-hom-Directed-Treeᵉ =
    is-torsorial-htpy-hom-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)

  htpy-eq-hom-Directed-Treeᵉ :
    (gᵉ : hom-Directed-Treeᵉ Sᵉ Tᵉ) → fᵉ ＝ᵉ gᵉ → htpy-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ gᵉ
  htpy-eq-hom-Directed-Treeᵉ =
    htpy-eq-hom-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)

  is-equiv-htpy-eq-hom-Directed-Treeᵉ :
    (gᵉ : hom-Directed-Treeᵉ Sᵉ Tᵉ) → is-equivᵉ (htpy-eq-hom-Directed-Treeᵉ gᵉ)
  is-equiv-htpy-eq-hom-Directed-Treeᵉ =
    is-equiv-htpy-eq-hom-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)

  extensionality-hom-Directed-Treeᵉ :
    (gᵉ : hom-Directed-Treeᵉ Sᵉ Tᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ gᵉ
  extensionality-hom-Directed-Treeᵉ =
    extensionality-hom-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)

  eq-htpy-hom-Directed-Treeᵉ :
    (gᵉ : hom-Directed-Treeᵉ Sᵉ Tᵉ) → htpy-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-Directed-Treeᵉ =
    eq-htpy-hom-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)
```

### If `f x` is the root of `T`, then `x` is the root of `S`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ)
  (fᵉ : hom-Directed-Treeᵉ Sᵉ Tᵉ)
  where

  is-root-is-root-node-hom-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Sᵉ) →
    is-root-Directed-Treeᵉ Tᵉ (node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ) →
    is-root-Directed-Treeᵉ Sᵉ xᵉ
  is-root-is-root-node-hom-Directed-Treeᵉ xᵉ Hᵉ =
    map-right-unit-law-coproduct-is-emptyᵉ
      ( is-root-Directed-Treeᵉ Sᵉ xᵉ)
      ( Σᵉ (node-Directed-Treeᵉ Sᵉ) (edge-Directed-Treeᵉ Sᵉ xᵉ))
      ( λ (yᵉ ,ᵉ eᵉ) →
        no-direct-successor-root-Directed-Treeᵉ Tᵉ
          ( trᵉ
            ( λ uᵉ → Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ uᵉ))
            ( invᵉ Hᵉ)
            ( node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ yᵉ ,ᵉ
              edge-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ eᵉ)))
      ( centerᵉ (unique-direct-successor-Directed-Treeᵉ Sᵉ xᵉ))

  is-not-root-node-hom-is-not-root-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Sᵉ) →
    ¬ᵉ (is-root-Directed-Treeᵉ Sᵉ xᵉ) →
    ¬ᵉ (is-root-Directed-Treeᵉ Tᵉ (node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ))
  is-not-root-node-hom-is-not-root-Directed-Treeᵉ xᵉ =
    map-negᵉ (is-root-is-root-node-hom-Directed-Treeᵉ xᵉ)
```

## See also

-ᵉ Root-preservingᵉ morphismsᵉ ofᵉ directedᵉ treesᵉ areᵉ introducedᵉ in
  [`rooted-morphisms-directed-trees`](trees.rooted-morphisms-directed-trees.mdᵉ)