# Equivalences of directed trees

```agda
module trees.equivalences-directed-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-transportᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.equivalences-directed-graphsᵉ
open import graph-theory.walks-directed-graphsᵉ

open import trees.directed-treesᵉ
open import trees.morphisms-directed-treesᵉ
open import trees.rooted-morphisms-directed-treesᵉ
```

</details>

## Idea

**Equivalencesᵉ ofᵉ directedᵉ trees**ᵉ areᵉ morphismsᵉ ofᵉ directedᵉ treesᵉ ofᵉ whichᵉ theᵉ
actionsᵉ onᵉ nodesᵉ andᵉ onᵉ edgesᵉ areᵉ bothᵉ equivalences.ᵉ Inᵉ otherᵉ words,ᵉ
equivalencesᵉ ofᵉ directedᵉ treesᵉ areᵉ justᵉ equivalencesᵉ betweenᵉ theirᵉ underlyingᵉ
directedᵉ graphs.ᵉ

## Definitions

### The condition of being an equivalence of directed trees

```agda
is-equiv-hom-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ) →
  hom-Directed-Treeᵉ Sᵉ Tᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
is-equiv-hom-Directed-Treeᵉ Sᵉ Tᵉ =
  is-equiv-hom-Directed-Graphᵉ (graph-Directed-Treeᵉ Sᵉ) (graph-Directed-Treeᵉ Tᵉ)
```

### Equivalences of directed trees

```agda
equiv-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
equiv-Directed-Treeᵉ Sᵉ Tᵉ =
  equiv-Directed-Graphᵉ (graph-Directed-Treeᵉ Sᵉ) (graph-Directed-Treeᵉ Tᵉ)

equiv-is-equiv-hom-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ) →
  (fᵉ : hom-Directed-Treeᵉ Sᵉ Tᵉ) → is-equiv-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ →
  equiv-Directed-Treeᵉ Sᵉ Tᵉ
equiv-is-equiv-hom-Directed-Treeᵉ Sᵉ Tᵉ =
  equiv-is-equiv-hom-Directed-Graphᵉ
    ( graph-Directed-Treeᵉ Sᵉ)
    ( graph-Directed-Treeᵉ Tᵉ)

compute-equiv-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ) →
  equiv-Directed-Treeᵉ Sᵉ Tᵉ ≃ᵉ
  Σᵉ (hom-Directed-Treeᵉ Sᵉ Tᵉ) (is-equiv-hom-Directed-Treeᵉ Sᵉ Tᵉ)
compute-equiv-Directed-Treeᵉ Sᵉ Tᵉ =
  compute-equiv-Directed-Graphᵉ
    ( graph-Directed-Treeᵉ Sᵉ)
    ( graph-Directed-Treeᵉ Tᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ)
  (eᵉ : equiv-Directed-Treeᵉ Sᵉ Tᵉ)
  where

  equiv-node-equiv-Directed-Treeᵉ :
    node-Directed-Treeᵉ Sᵉ ≃ᵉ node-Directed-Treeᵉ Tᵉ
  equiv-node-equiv-Directed-Treeᵉ =
    equiv-vertex-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eᵉ)

  node-equiv-Directed-Treeᵉ :
    node-Directed-Treeᵉ Sᵉ → node-Directed-Treeᵉ Tᵉ
  node-equiv-Directed-Treeᵉ =
    vertex-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eᵉ)

  is-equiv-node-equiv-Directed-Treeᵉ : is-equivᵉ node-equiv-Directed-Treeᵉ
  is-equiv-node-equiv-Directed-Treeᵉ =
    is-equiv-vertex-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eᵉ)

  inv-node-equiv-Directed-Treeᵉ :
    node-Directed-Treeᵉ Tᵉ → node-Directed-Treeᵉ Sᵉ
  inv-node-equiv-Directed-Treeᵉ =
    inv-vertex-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eᵉ)

  is-section-inv-node-equiv-Directed-Treeᵉ :
    ( node-equiv-Directed-Treeᵉ ∘ᵉ inv-node-equiv-Directed-Treeᵉ) ~ᵉ idᵉ
  is-section-inv-node-equiv-Directed-Treeᵉ =
    is-section-inv-vertex-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eᵉ)

  is-retraction-inv-node-equiv-Directed-Treeᵉ :
    ( inv-node-equiv-Directed-Treeᵉ ∘ᵉ node-equiv-Directed-Treeᵉ) ~ᵉ idᵉ
  is-retraction-inv-node-equiv-Directed-Treeᵉ =
    is-retraction-inv-vertex-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eᵉ)

  equiv-edge-equiv-Directed-Treeᵉ :
    (xᵉ yᵉ : node-Directed-Treeᵉ Sᵉ) →
    edge-Directed-Treeᵉ Sᵉ xᵉ yᵉ ≃ᵉ
    edge-Directed-Treeᵉ Tᵉ
      ( node-equiv-Directed-Treeᵉ xᵉ)
      ( node-equiv-Directed-Treeᵉ yᵉ)
  equiv-edge-equiv-Directed-Treeᵉ =
    equiv-edge-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eᵉ)

  edge-equiv-Directed-Treeᵉ :
    (xᵉ yᵉ : node-Directed-Treeᵉ Sᵉ) →
    edge-Directed-Treeᵉ Sᵉ xᵉ yᵉ →
    edge-Directed-Treeᵉ Tᵉ
      ( node-equiv-Directed-Treeᵉ xᵉ)
      ( node-equiv-Directed-Treeᵉ yᵉ)
  edge-equiv-Directed-Treeᵉ =
    edge-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eᵉ)

  is-equiv-edge-equiv-Directed-Treeᵉ :
    (xᵉ yᵉ : node-Directed-Treeᵉ Sᵉ) → is-equivᵉ (edge-equiv-Directed-Treeᵉ xᵉ yᵉ)
  is-equiv-edge-equiv-Directed-Treeᵉ =
    is-equiv-edge-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eᵉ)

  hom-equiv-Directed-Treeᵉ : hom-Directed-Treeᵉ Sᵉ Tᵉ
  hom-equiv-Directed-Treeᵉ =
    hom-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eᵉ)

  is-equiv-equiv-Directed-Treeᵉ :
    is-equiv-hom-Directed-Treeᵉ Sᵉ Tᵉ hom-equiv-Directed-Treeᵉ
  is-equiv-equiv-Directed-Treeᵉ =
    is-equiv-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eᵉ)

  equiv-direct-predecessor-equiv-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Sᵉ) →
    ( Σᵉ (node-Directed-Treeᵉ Sᵉ) (λ yᵉ → edge-Directed-Treeᵉ Sᵉ yᵉ xᵉ)) ≃ᵉ
    ( Σᵉ ( node-Directed-Treeᵉ Tᵉ)
        ( λ yᵉ → edge-Directed-Treeᵉ Tᵉ yᵉ (node-equiv-Directed-Treeᵉ xᵉ)))
  equiv-direct-predecessor-equiv-Directed-Treeᵉ xᵉ =
    equiv-Σᵉ
      ( λ yᵉ → edge-Directed-Treeᵉ Tᵉ yᵉ (node-equiv-Directed-Treeᵉ xᵉ))
      ( equiv-node-equiv-Directed-Treeᵉ)
      ( λ yᵉ → equiv-edge-equiv-Directed-Treeᵉ yᵉ xᵉ)

  direct-predecessor-equiv-Directed-Treeᵉ :
    (xᵉ : node-Directed-Treeᵉ Sᵉ) →
    Σᵉ (node-Directed-Treeᵉ Sᵉ) (λ yᵉ → edge-Directed-Treeᵉ Sᵉ yᵉ xᵉ) →
    Σᵉ ( node-Directed-Treeᵉ Tᵉ)
      ( λ yᵉ → edge-Directed-Treeᵉ Tᵉ yᵉ (node-equiv-Directed-Treeᵉ xᵉ))
  direct-predecessor-equiv-Directed-Treeᵉ xᵉ =
    map-equivᵉ (equiv-direct-predecessor-equiv-Directed-Treeᵉ xᵉ)

  equiv-walk-equiv-Directed-Treeᵉ :
    {xᵉ yᵉ : node-Directed-Treeᵉ Sᵉ} →
    walk-Directed-Treeᵉ Sᵉ xᵉ yᵉ ≃ᵉ
    walk-Directed-Treeᵉ Tᵉ
      ( node-equiv-Directed-Treeᵉ xᵉ)
      ( node-equiv-Directed-Treeᵉ yᵉ)
  equiv-walk-equiv-Directed-Treeᵉ =
    equiv-walk-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eᵉ)

  walk-equiv-Directed-Treeᵉ :
    {xᵉ yᵉ : node-Directed-Treeᵉ Sᵉ} →
    walk-Directed-Treeᵉ Sᵉ xᵉ yᵉ →
    walk-Directed-Treeᵉ Tᵉ
      ( node-equiv-Directed-Treeᵉ xᵉ)
      ( node-equiv-Directed-Treeᵉ yᵉ)
  walk-equiv-Directed-Treeᵉ =
    walk-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eᵉ)
```

### Identity equivalences of directed trees

```agda
id-equiv-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) → equiv-Directed-Treeᵉ Tᵉ Tᵉ
id-equiv-Directed-Treeᵉ Tᵉ = id-equiv-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ)
```

### Composition of equivalences of directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Rᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Sᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ) (Tᵉ : Directed-Treeᵉ l5ᵉ l6ᵉ)
  (gᵉ : equiv-Directed-Treeᵉ Sᵉ Tᵉ) (fᵉ : equiv-Directed-Treeᵉ Rᵉ Sᵉ)
  where

  comp-equiv-Directed-Treeᵉ : equiv-Directed-Treeᵉ Rᵉ Tᵉ
  comp-equiv-Directed-Treeᵉ =
    comp-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Rᵉ)
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( gᵉ)
      ( fᵉ)

  equiv-node-comp-equiv-Directed-Treeᵉ :
    node-Directed-Treeᵉ Rᵉ ≃ᵉ node-Directed-Treeᵉ Tᵉ
  equiv-node-comp-equiv-Directed-Treeᵉ =
    equiv-node-equiv-Directed-Treeᵉ Rᵉ Tᵉ comp-equiv-Directed-Treeᵉ

  node-comp-equiv-Directed-Treeᵉ :
    node-Directed-Treeᵉ Rᵉ → node-Directed-Treeᵉ Tᵉ
  node-comp-equiv-Directed-Treeᵉ =
    node-equiv-Directed-Treeᵉ Rᵉ Tᵉ comp-equiv-Directed-Treeᵉ

  equiv-edge-comp-equiv-Directed-Treeᵉ :
    (xᵉ yᵉ : node-Directed-Treeᵉ Rᵉ) →
    edge-Directed-Treeᵉ Rᵉ xᵉ yᵉ ≃ᵉ
    edge-Directed-Treeᵉ Tᵉ
      ( node-comp-equiv-Directed-Treeᵉ xᵉ)
      ( node-comp-equiv-Directed-Treeᵉ yᵉ)
  equiv-edge-comp-equiv-Directed-Treeᵉ =
    equiv-edge-equiv-Directed-Treeᵉ Rᵉ Tᵉ comp-equiv-Directed-Treeᵉ

  edge-comp-equiv-Directed-Treeᵉ :
    (xᵉ yᵉ : node-Directed-Treeᵉ Rᵉ) →
    edge-Directed-Treeᵉ Rᵉ xᵉ yᵉ →
    edge-Directed-Treeᵉ Tᵉ
      ( node-comp-equiv-Directed-Treeᵉ xᵉ)
      ( node-comp-equiv-Directed-Treeᵉ yᵉ)
  edge-comp-equiv-Directed-Treeᵉ =
    edge-equiv-Directed-Treeᵉ Rᵉ Tᵉ comp-equiv-Directed-Treeᵉ
```

### Homotopies of equivalences of directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ)
  (fᵉ gᵉ : equiv-Directed-Treeᵉ Sᵉ Tᵉ)
  where

  htpy-equiv-Directed-Treeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-equiv-Directed-Treeᵉ =
    htpy-hom-Directed-Treeᵉ Sᵉ Tᵉ
      ( hom-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
      ( hom-equiv-Directed-Treeᵉ Sᵉ Tᵉ gᵉ)

  node-htpy-equiv-Directed-Treeᵉ :
    htpy-equiv-Directed-Treeᵉ →
    node-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ ~ᵉ node-equiv-Directed-Treeᵉ Sᵉ Tᵉ gᵉ
  node-htpy-equiv-Directed-Treeᵉ =
    node-htpy-hom-Directed-Treeᵉ Sᵉ Tᵉ
      ( hom-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
      ( hom-equiv-Directed-Treeᵉ Sᵉ Tᵉ gᵉ)

  edge-htpy-equiv-Directed-Treeᵉ :
    (αᵉ : htpy-equiv-Directed-Treeᵉ) (xᵉ yᵉ : node-Directed-Treeᵉ Sᵉ)
    (eᵉ : edge-Directed-Treeᵉ Sᵉ xᵉ yᵉ) →
    binary-trᵉ
      ( edge-Directed-Treeᵉ Tᵉ)
      ( node-htpy-equiv-Directed-Treeᵉ αᵉ xᵉ)
      ( node-htpy-equiv-Directed-Treeᵉ αᵉ yᵉ)
      ( edge-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ yᵉ eᵉ) ＝ᵉ
    edge-equiv-Directed-Treeᵉ Sᵉ Tᵉ gᵉ xᵉ yᵉ eᵉ
  edge-htpy-equiv-Directed-Treeᵉ =
    edge-htpy-hom-Directed-Treeᵉ Sᵉ Tᵉ
      ( hom-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
      ( hom-equiv-Directed-Treeᵉ Sᵉ Tᵉ gᵉ)
```

### The reflexivity homotopy of equivalences of directed trees

```agda
refl-htpy-equiv-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ)
  (fᵉ : equiv-Directed-Treeᵉ Sᵉ Tᵉ) → htpy-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ fᵉ
refl-htpy-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ =
  refl-htpy-hom-Directed-Treeᵉ Sᵉ Tᵉ (hom-equiv-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
```

## Properties

### Homotopies characterize the identity type of equivalences of directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ)
  (eᵉ : equiv-Directed-Treeᵉ Sᵉ Tᵉ)
  where

  is-torsorial-htpy-equiv-Directed-Treeᵉ :
    is-torsorialᵉ (htpy-equiv-Directed-Treeᵉ Sᵉ Tᵉ eᵉ)
  is-torsorial-htpy-equiv-Directed-Treeᵉ =
    is-torsorial-htpy-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eᵉ)

  htpy-eq-equiv-Directed-Treeᵉ :
    (fᵉ : equiv-Directed-Treeᵉ Sᵉ Tᵉ) → (eᵉ ＝ᵉ fᵉ) → htpy-equiv-Directed-Treeᵉ Sᵉ Tᵉ eᵉ fᵉ
  htpy-eq-equiv-Directed-Treeᵉ =
    htpy-eq-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eᵉ)

  is-equiv-htpy-eq-equiv-Directed-Treeᵉ :
    (fᵉ : equiv-Directed-Treeᵉ Sᵉ Tᵉ) → is-equivᵉ (htpy-eq-equiv-Directed-Treeᵉ fᵉ)
  is-equiv-htpy-eq-equiv-Directed-Treeᵉ =
    is-equiv-htpy-eq-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eᵉ)

  extensionality-equiv-Directed-Treeᵉ :
    (fᵉ : equiv-Directed-Treeᵉ Sᵉ Tᵉ) → (eᵉ ＝ᵉ fᵉ) ≃ᵉ htpy-equiv-Directed-Treeᵉ Sᵉ Tᵉ eᵉ fᵉ
  extensionality-equiv-Directed-Treeᵉ =
    extensionality-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eᵉ)

  eq-htpy-equiv-Directed-Treeᵉ :
    (fᵉ : equiv-Directed-Treeᵉ Sᵉ Tᵉ) → htpy-equiv-Directed-Treeᵉ Sᵉ Tᵉ eᵉ fᵉ → eᵉ ＝ᵉ fᵉ
  eq-htpy-equiv-Directed-Treeᵉ =
    eq-htpy-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( eᵉ)
```

### Equivalences of directed trees preserve the root

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ)
  (fᵉ : hom-Directed-Treeᵉ Sᵉ Tᵉ)
  where

  preserves-root-is-equiv-node-hom-Directed-Treeᵉ :
    is-equivᵉ (node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ) →
    preserves-root-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ
  preserves-root-is-equiv-node-hom-Directed-Treeᵉ Hᵉ =
    ( invᵉ (is-section-map-inv-is-equivᵉ Hᵉ (root-Directed-Treeᵉ Tᵉ))) ∙ᵉ
    ( invᵉ
      ( apᵉ
        ( node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
        ( is-root-is-root-node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ
          ( map-inv-is-equivᵉ Hᵉ (root-Directed-Treeᵉ Tᵉ))
          ( invᵉ (is-section-map-inv-is-equivᵉ Hᵉ (root-Directed-Treeᵉ Tᵉ))))))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ)
  (eᵉ : equiv-Directed-Treeᵉ Sᵉ Tᵉ)
  where

  preserves-root-equiv-Directed-Treeᵉ :
    preserves-root-hom-Directed-Treeᵉ Sᵉ Tᵉ (hom-equiv-Directed-Treeᵉ Sᵉ Tᵉ eᵉ)
  preserves-root-equiv-Directed-Treeᵉ =
    preserves-root-is-equiv-node-hom-Directed-Treeᵉ Sᵉ Tᵉ
      ( hom-equiv-Directed-Treeᵉ Sᵉ Tᵉ eᵉ)
      ( is-equiv-node-equiv-Directed-Treeᵉ Sᵉ Tᵉ eᵉ)

  rooted-hom-equiv-Directed-Treeᵉ :
    rooted-hom-Directed-Treeᵉ Sᵉ Tᵉ
  pr1ᵉ rooted-hom-equiv-Directed-Treeᵉ = hom-equiv-Directed-Treeᵉ Sᵉ Tᵉ eᵉ
  pr2ᵉ rooted-hom-equiv-Directed-Treeᵉ = preserves-root-equiv-Directed-Treeᵉ
```

### Equivalences characterize identifications of trees

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ)
  where

  extensionality-Directed-Treeᵉ :
    (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) → (Tᵉ ＝ᵉ Sᵉ) ≃ᵉ equiv-Directed-Treeᵉ Tᵉ Sᵉ
  extensionality-Directed-Treeᵉ =
    extensionality-type-subtypeᵉ
      ( is-tree-directed-graph-Propᵉ)
      ( is-tree-Directed-Treeᵉ Tᵉ)
      ( id-equiv-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ))
      ( extensionality-Directed-Graphᵉ (graph-Directed-Treeᵉ Tᵉ))

  equiv-eq-Directed-Treeᵉ :
    (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) → (Tᵉ ＝ᵉ Sᵉ) → equiv-Directed-Treeᵉ Tᵉ Sᵉ
  equiv-eq-Directed-Treeᵉ Sᵉ = map-equivᵉ (extensionality-Directed-Treeᵉ Sᵉ)

  eq-equiv-Directed-Treeᵉ :
    (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) → equiv-Directed-Treeᵉ Tᵉ Sᵉ → (Tᵉ ＝ᵉ Sᵉ)
  eq-equiv-Directed-Treeᵉ Sᵉ = map-inv-equivᵉ (extensionality-Directed-Treeᵉ Sᵉ)

  is-torsorial-equiv-Directed-Treeᵉ :
    is-torsorialᵉ (equiv-Directed-Treeᵉ Tᵉ)
  is-torsorial-equiv-Directed-Treeᵉ =
    is-contr-equiv'ᵉ
      ( Σᵉ (Directed-Treeᵉ l1ᵉ l2ᵉ) (λ Sᵉ → Tᵉ ＝ᵉ Sᵉ))
      ( equiv-totᵉ extensionality-Directed-Treeᵉ)
      ( is-torsorial-Idᵉ Tᵉ)
```

### A morphism of directed trees is an equivalence if it is an equivalence on the nodes

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ)
  (fᵉ : hom-Directed-Treeᵉ Sᵉ Tᵉ)
  where

  is-equiv-total-edge-is-equiv-node-hom-Directed-Treeᵉ :
    is-equivᵉ (node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ) → (xᵉ : node-Directed-Treeᵉ Sᵉ) →
    is-equivᵉ
      ( map-Σᵉ
        ( edge-Directed-Treeᵉ Tᵉ (node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ))
        ( node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
        ( λ yᵉ → edge-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ {xᵉ} {yᵉ}))
  is-equiv-total-edge-is-equiv-node-hom-Directed-Treeᵉ Hᵉ xᵉ with
    is-isolated-root-Directed-Treeᵉ Sᵉ xᵉ
  ... | inlᵉ reflᵉ =
    is-equiv-is-emptyᵉ _
      ( λ uᵉ →
        no-direct-successor-root-Directed-Treeᵉ Tᵉ
          ( trᵉ
            ( λ vᵉ → Σᵉ (node-Directed-Treeᵉ Tᵉ) (edge-Directed-Treeᵉ Tᵉ vᵉ))
            ( invᵉ (preserves-root-is-equiv-node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ Hᵉ))
            ( uᵉ)))
  ... | inrᵉ pᵉ =
    is-equiv-is-contrᵉ _
      ( unique-direct-successor-is-proper-node-Directed-Treeᵉ Sᵉ xᵉ pᵉ)
      ( unique-direct-successor-is-proper-node-Directed-Treeᵉ Tᵉ
        ( node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ)
        ( is-not-root-node-hom-is-not-root-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ pᵉ))

  is-equiv-is-equiv-node-hom-Directed-Treeᵉ :
    is-equivᵉ (node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ) →
    is-equiv-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ
  pr1ᵉ (is-equiv-is-equiv-node-hom-Directed-Treeᵉ Hᵉ) = Hᵉ
  pr2ᵉ (is-equiv-is-equiv-node-hom-Directed-Treeᵉ Hᵉ) xᵉ =
    is-fiberwise-equiv-is-equiv-map-Σᵉ
      ( edge-Directed-Treeᵉ Tᵉ (node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ))
      ( node-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
      ( λ yᵉ → edge-hom-Directed-Treeᵉ Sᵉ Tᵉ fᵉ {xᵉ} {yᵉ})
      ( Hᵉ)
      ( is-equiv-total-edge-is-equiv-node-hom-Directed-Treeᵉ Hᵉ xᵉ)
```

### The inverse of an equivalence of directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Sᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ) (Tᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ)
  (fᵉ : equiv-Directed-Treeᵉ Sᵉ Tᵉ)
  where

  inv-equiv-Directed-Treeᵉ : equiv-Directed-Treeᵉ Tᵉ Sᵉ
  inv-equiv-Directed-Treeᵉ =
    inv-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)

  hom-inv-equiv-Directed-Treeᵉ : hom-Directed-Treeᵉ Tᵉ Sᵉ
  hom-inv-equiv-Directed-Treeᵉ =
    hom-inv-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)

  equiv-node-inv-equiv-Directed-Treeᵉ :
    node-Directed-Treeᵉ Tᵉ ≃ᵉ node-Directed-Treeᵉ Sᵉ
  equiv-node-inv-equiv-Directed-Treeᵉ =
    equiv-vertex-inv-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)

  node-inv-equiv-Directed-Treeᵉ :
    node-Directed-Treeᵉ Tᵉ → node-Directed-Treeᵉ Sᵉ
  node-inv-equiv-Directed-Treeᵉ =
    vertex-inv-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)

  edge-inv-equiv-Directed-Treeᵉ :
    (xᵉ yᵉ : node-Directed-Treeᵉ Tᵉ) →
    edge-Directed-Treeᵉ Tᵉ xᵉ yᵉ →
    edge-Directed-Treeᵉ Sᵉ
      ( node-inv-equiv-Directed-Treeᵉ xᵉ)
      ( node-inv-equiv-Directed-Treeᵉ yᵉ)
  edge-inv-equiv-Directed-Treeᵉ =
    edge-inv-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)

  equiv-edge-inv-equiv-Directed-Treeᵉ :
    (xᵉ yᵉ : node-Directed-Treeᵉ Tᵉ) →
    edge-Directed-Treeᵉ Tᵉ xᵉ yᵉ ≃ᵉ
    edge-Directed-Treeᵉ Sᵉ
      ( node-inv-equiv-Directed-Treeᵉ xᵉ)
      ( node-inv-equiv-Directed-Treeᵉ yᵉ)
  equiv-edge-inv-equiv-Directed-Treeᵉ =
    equiv-edge-inv-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)

  is-section-inv-equiv-Directed-Treeᵉ :
    htpy-equiv-Directed-Treeᵉ Tᵉ Tᵉ
      ( comp-equiv-Directed-Treeᵉ Tᵉ Sᵉ Tᵉ fᵉ inv-equiv-Directed-Treeᵉ)
      ( id-equiv-Directed-Treeᵉ Tᵉ)
  is-section-inv-equiv-Directed-Treeᵉ =
    is-section-inv-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)

  is-retraction-inv-equiv-Directed-Treeᵉ :
    htpy-equiv-Directed-Treeᵉ Sᵉ Sᵉ
      ( comp-equiv-Directed-Treeᵉ Sᵉ Tᵉ Sᵉ inv-equiv-Directed-Treeᵉ fᵉ)
      ( id-equiv-Directed-Treeᵉ Sᵉ)
  is-retraction-inv-equiv-Directed-Treeᵉ =
    is-retraction-inv-equiv-Directed-Graphᵉ
      ( graph-Directed-Treeᵉ Sᵉ)
      ( graph-Directed-Treeᵉ Tᵉ)
      ( fᵉ)
```