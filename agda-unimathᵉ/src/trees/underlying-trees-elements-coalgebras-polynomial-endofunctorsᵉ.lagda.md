# The underlying trees of elements of coalgebras of polynomial endofunctors

```agda
module trees.underlying-trees-elements-coalgebras-polynomial-endofunctorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-transportᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.isolated-elementsᵉ
open import foundation.negated-equalityᵉ
open import foundation.propositionsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ
open import graph-theory.morphisms-directed-graphsᵉ
open import graph-theory.walks-directed-graphsᵉ

open import trees.coalgebras-polynomial-endofunctorsᵉ
open import trees.combinator-directed-treesᵉ
open import trees.combinator-enriched-directed-treesᵉ
open import trees.directed-treesᵉ
open import trees.elementhood-relation-coalgebras-polynomial-endofunctorsᵉ
open import trees.enriched-directed-treesᵉ
open import trees.equivalences-directed-treesᵉ
open import trees.equivalences-enriched-directed-treesᵉ
```

</details>

## Idea

Forᵉ everyᵉ elementᵉ `x`ᵉ ofᵉ aᵉ coalgebraᵉ ofᵉ aᵉ polynomialᵉ endofunctorᵉ weᵉ canᵉ
inductivelyᵉ defineᵉ anᵉ enrichedᵉ directedᵉ tree.ᵉ Thisᵉ treeᵉ isᵉ calledᵉ theᵉ
**underlyingᵉ enrichedᵉ directedᵉ tree**ᵉ ofᵉ `x`.ᵉ

## Definition

### The underlying graph of an element of a coalgebra of a polynomial endofunctor

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : coalgebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ)
  where

  data
    node-element-coalgebraᵉ :
      type-coalgebra-polynomial-endofunctorᵉ Xᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
    where
    root-coalgebraᵉ :
      (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ) →
      node-element-coalgebraᵉ wᵉ
    node-inclusion-element-coalgebraᵉ :
      {uᵉ vᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ} →
      (uᵉ ∈ᵉ vᵉ in-coalgebraᵉ Xᵉ) →
      node-element-coalgebraᵉ uᵉ →
      node-element-coalgebraᵉ vᵉ

  data
    edge-element-coalgebraᵉ :
      (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
      (xᵉ yᵉ : node-element-coalgebraᵉ wᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
    where
    edge-to-root-element-coalgebraᵉ :
      {uᵉ vᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ}
      (Hᵉ : uᵉ ∈ᵉ vᵉ in-coalgebraᵉ Xᵉ) →
      edge-element-coalgebraᵉ vᵉ
        ( node-inclusion-element-coalgebraᵉ Hᵉ
          ( root-coalgebraᵉ uᵉ))
        ( root-coalgebraᵉ vᵉ)
    edge-inclusion-element-coalgebraᵉ :
      {uᵉ vᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ}
      (Hᵉ : uᵉ ∈ᵉ vᵉ in-coalgebraᵉ Xᵉ) →
      {xᵉ yᵉ : node-element-coalgebraᵉ uᵉ}
      (eᵉ : edge-element-coalgebraᵉ uᵉ xᵉ yᵉ) →
      edge-element-coalgebraᵉ vᵉ
        ( node-inclusion-element-coalgebraᵉ Hᵉ xᵉ)
        ( node-inclusion-element-coalgebraᵉ Hᵉ yᵉ)

  graph-element-coalgebraᵉ :
    type-coalgebra-polynomial-endofunctorᵉ Xᵉ →
    Directed-Graphᵉ (l2ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ (graph-element-coalgebraᵉ wᵉ) =
    node-element-coalgebraᵉ wᵉ
  pr2ᵉ (graph-element-coalgebraᵉ wᵉ) =
    edge-element-coalgebraᵉ wᵉ

  walk-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
    (xᵉ yᵉ : node-element-coalgebraᵉ wᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  walk-element-coalgebraᵉ wᵉ =
    walk-Directed-Graphᵉ (graph-element-coalgebraᵉ wᵉ)
```

### The external graph of an element of a W-type

```agda
  node-external-graph-element-coalgebraᵉ :
    type-coalgebra-polynomial-endofunctorᵉ Xᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  node-external-graph-element-coalgebraᵉ wᵉ =
    Σᵉ ( type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
      ( λ uᵉ → walk-coalgebra-polynomial-endofunctorᵉ Xᵉ uᵉ wᵉ)

  edge-external-graph-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
    (xᵉ yᵉ : node-external-graph-element-coalgebraᵉ wᵉ) →
    UUᵉ (l2ᵉ ⊔ l3ᵉ)
  edge-external-graph-element-coalgebraᵉ
    wᵉ (xᵉ ,ᵉ Hᵉ) (yᵉ ,ᵉ Kᵉ) =
    Σᵉ ( xᵉ ∈ᵉ yᵉ in-coalgebraᵉ Xᵉ) (λ eᵉ → cons-walk-Directed-Graphᵉ eᵉ Kᵉ ＝ᵉ Hᵉ)

  external-graph-element-coalgebraᵉ :
    type-coalgebra-polynomial-endofunctorᵉ Xᵉ → Directed-Graphᵉ (l2ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ (external-graph-element-coalgebraᵉ wᵉ) =
    node-external-graph-element-coalgebraᵉ wᵉ
  pr2ᵉ (external-graph-element-coalgebraᵉ wᵉ) =
    edge-external-graph-element-coalgebraᵉ wᵉ
```

## Properties

### To be a root is decidable

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : coalgebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ)
  where

  is-root-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ) →
    node-element-coalgebraᵉ Xᵉ wᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  is-root-element-coalgebraᵉ wᵉ xᵉ =
    root-coalgebraᵉ wᵉ ＝ᵉ xᵉ

  is-isolated-root-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ) →
    is-isolatedᵉ (root-coalgebraᵉ {Xᵉ = Xᵉ} wᵉ)
  is-isolated-root-element-coalgebraᵉ wᵉ
    ( root-coalgebraᵉ wᵉ) =
    inlᵉ reflᵉ
  is-isolated-root-element-coalgebraᵉ wᵉ
    ( node-inclusion-element-coalgebraᵉ Hᵉ yᵉ) =
    inrᵉ (λ ())

  is-contr-loop-space-root-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ) →
    is-contrᵉ
      ( root-coalgebraᵉ wᵉ ＝ᵉ
        root-coalgebraᵉ wᵉ)
  is-contr-loop-space-root-element-coalgebraᵉ wᵉ =
    is-contr-loop-space-isolated-elementᵉ
      ( root-coalgebraᵉ wᵉ)
      ( is-isolated-root-element-coalgebraᵉ wᵉ)
```

### Characterization of equality of the type of nodes of the underlying graph of an element of `coalgebra A B`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : coalgebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ)
  where

  data
    Eq-node-element-coalgebraᵉ
      ( wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ) :
      ( xᵉ yᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
    where
    root-refl-Eq-node-element-coalgebraᵉ :
      Eq-node-element-coalgebraᵉ wᵉ
        ( root-coalgebraᵉ wᵉ)
        ( root-coalgebraᵉ wᵉ)
    node-inclusion-Eq-node-element-coalgebraᵉ :
      {uᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ}
      (Hᵉ : uᵉ ∈ᵉ wᵉ in-coalgebraᵉ Xᵉ)
      {xᵉ yᵉ : node-element-coalgebraᵉ Xᵉ uᵉ} →
      Eq-node-element-coalgebraᵉ uᵉ xᵉ yᵉ →
      Eq-node-element-coalgebraᵉ wᵉ
        ( node-inclusion-element-coalgebraᵉ Hᵉ xᵉ)
        ( node-inclusion-element-coalgebraᵉ Hᵉ yᵉ)

  refl-Eq-node-element-coalgebraᵉ :
    {wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ}
    (xᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    Eq-node-element-coalgebraᵉ wᵉ xᵉ xᵉ
  refl-Eq-node-element-coalgebraᵉ
    ( root-coalgebraᵉ wᵉ) =
    root-refl-Eq-node-element-coalgebraᵉ
  refl-Eq-node-element-coalgebraᵉ
    ( node-inclusion-element-coalgebraᵉ {uᵉ} Hᵉ xᵉ) =
    node-inclusion-Eq-node-element-coalgebraᵉ Hᵉ
      ( refl-Eq-node-element-coalgebraᵉ xᵉ)

  center-total-Eq-node-element-coalgebraᵉ :
    {wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ}
    (xᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    Σᵉ ( node-element-coalgebraᵉ Xᵉ wᵉ)
      ( Eq-node-element-coalgebraᵉ wᵉ xᵉ)
  pr1ᵉ (center-total-Eq-node-element-coalgebraᵉ xᵉ) = xᵉ
  pr2ᵉ (center-total-Eq-node-element-coalgebraᵉ xᵉ) =
    refl-Eq-node-element-coalgebraᵉ xᵉ

  contraction-total-Eq-node-element-coalgebraᵉ :
    {wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ}
    (xᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    (uᵉ :
      Σᵉ ( node-element-coalgebraᵉ Xᵉ wᵉ)
        ( Eq-node-element-coalgebraᵉ wᵉ xᵉ)) →
    center-total-Eq-node-element-coalgebraᵉ xᵉ ＝ᵉ uᵉ
  contraction-total-Eq-node-element-coalgebraᵉ ._
    (.ᵉ_ ,ᵉ root-refl-Eq-node-element-coalgebraᵉ) =
    reflᵉ
  contraction-total-Eq-node-element-coalgebraᵉ ._
    ( .(node-inclusion-element-coalgebraᵉ Hᵉ _) ,ᵉ
      node-inclusion-Eq-node-element-coalgebraᵉ Hᵉ eᵉ) =
    apᵉ
      ( map-Σᵉ
        ( λ zᵉ → Eq-node-element-coalgebraᵉ _ _ zᵉ)
        ( node-inclusion-element-coalgebraᵉ Hᵉ)
        ( λ yᵉ →
          node-inclusion-Eq-node-element-coalgebraᵉ Hᵉ))
      ( contraction-total-Eq-node-element-coalgebraᵉ _
        ( _ ,ᵉ eᵉ))

  is-torsorial-Eq-node-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
    (xᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    is-torsorialᵉ (Eq-node-element-coalgebraᵉ wᵉ xᵉ)
  pr1ᵉ (is-torsorial-Eq-node-element-coalgebraᵉ wᵉ xᵉ) =
    center-total-Eq-node-element-coalgebraᵉ xᵉ
  pr2ᵉ (is-torsorial-Eq-node-element-coalgebraᵉ wᵉ xᵉ) =
    contraction-total-Eq-node-element-coalgebraᵉ xᵉ

  Eq-eq-node-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
    {xᵉ yᵉ : node-element-coalgebraᵉ Xᵉ wᵉ} →
    xᵉ ＝ᵉ yᵉ → Eq-node-element-coalgebraᵉ wᵉ xᵉ yᵉ
  Eq-eq-node-element-coalgebraᵉ wᵉ reflᵉ =
    refl-Eq-node-element-coalgebraᵉ _

  is-equiv-Eq-eq-node-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
    (xᵉ yᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    is-equivᵉ (Eq-eq-node-element-coalgebraᵉ wᵉ {xᵉ} {yᵉ})
  is-equiv-Eq-eq-node-element-coalgebraᵉ wᵉ xᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-Eq-node-element-coalgebraᵉ wᵉ xᵉ)
      ( λ yᵉ → Eq-eq-node-element-coalgebraᵉ wᵉ {xᵉ} {yᵉ})

  extensionality-node-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
    (xᵉ yᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    (xᵉ ＝ᵉ yᵉ) ≃ᵉ Eq-node-element-coalgebraᵉ wᵉ xᵉ yᵉ
  pr1ᵉ (extensionality-node-element-coalgebraᵉ wᵉ xᵉ yᵉ) =
    Eq-eq-node-element-coalgebraᵉ wᵉ {xᵉ} {yᵉ}
  pr2ᵉ (extensionality-node-element-coalgebraᵉ wᵉ xᵉ yᵉ) =
    is-equiv-Eq-eq-node-element-coalgebraᵉ wᵉ xᵉ yᵉ

  eq-Eq-node-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
    (xᵉ yᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    Eq-node-element-coalgebraᵉ wᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  eq-Eq-node-element-coalgebraᵉ wᵉ xᵉ yᵉ =
    map-inv-equivᵉ
      ( extensionality-node-element-coalgebraᵉ wᵉ xᵉ yᵉ)
```

Noteᵉ thatᵉ weᵉ don'tᵉ expectᵉ thatᵉ `node-inclusion-element-coalgebra'`ᵉ isᵉ anᵉ
embedding.ᵉ Theᵉ totalᵉ spaceᵉ `Σᵉ (yᵉ : Bᵉ x),ᵉ node-element-coalgebra'ᵉ (αᵉ y)`ᵉ embedsᵉ
intoᵉ `node-element-coalgebra'ᵉ (tree-coalgebraᵉ xᵉ α)`,ᵉ andᵉ thisᵉ impliesᵉ thatᵉ theᵉ
nodeᵉ inclusionᵉ hasᵉ theᵉ sameᵉ truncationᵉ levelᵉ asᵉ theᵉ fiberᵉ inclusionsᵉ

```text
  node-element-coalgebra'ᵉ (αᵉ bᵉ) → Σᵉ (yᵉ : Bᵉ x),ᵉ node-element-coalgebra'ᵉ (αᵉ yᵉ)
```

Inᵉ otherᵉ words,ᵉ theᵉ fiberᵉ isᵉ `Ωᵉ (Bᵉ ,ᵉ b)`.ᵉ

### For any `u ∈-coalgebra v` in `coalgebra A B` we have a graph inclusion from the underlying graph of `u` to the underlying graph of `v`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : coalgebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ)
  where

  inclusion-element-coalgebraᵉ :
    {uᵉ vᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ} →
    uᵉ ∈ᵉ vᵉ in-coalgebraᵉ Xᵉ →
    hom-Directed-Graphᵉ
      ( graph-element-coalgebraᵉ Xᵉ uᵉ)
      ( graph-element-coalgebraᵉ Xᵉ vᵉ)
  pr1ᵉ (inclusion-element-coalgebraᵉ {uᵉ} {vᵉ} Hᵉ) =
    node-inclusion-element-coalgebraᵉ Hᵉ
  pr2ᵉ
    ( inclusion-element-coalgebraᵉ {uᵉ} {vᵉ} Hᵉ)
    xᵉ yᵉ eᵉ =
    edge-inclusion-element-coalgebraᵉ Hᵉ eᵉ

  walk-inclusion-element-coalgebraᵉ :
    {uᵉ vᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ} →
    (Hᵉ : uᵉ ∈ᵉ vᵉ in-coalgebraᵉ Xᵉ) →
    {xᵉ yᵉ : node-element-coalgebraᵉ Xᵉ uᵉ} →
    walk-element-coalgebraᵉ Xᵉ uᵉ xᵉ yᵉ →
    walk-element-coalgebraᵉ Xᵉ vᵉ
      ( node-inclusion-element-coalgebraᵉ Hᵉ xᵉ)
      ( node-inclusion-element-coalgebraᵉ Hᵉ yᵉ)
  walk-inclusion-element-coalgebraᵉ {uᵉ} {vᵉ} Hᵉ =
    walk-hom-Directed-Graphᵉ
      ( graph-element-coalgebraᵉ Xᵉ uᵉ)
      ( graph-element-coalgebraᵉ Xᵉ vᵉ)
      ( inclusion-element-coalgebraᵉ Hᵉ)
```

### The type of edges from the root of `u ∈-coalgebra v` to the root of `v` is contractible

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : coalgebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ)
  where

  is-contr-edge-to-root-element-coalgebraᵉ :
    {uᵉ vᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ}
    (Hᵉ : uᵉ ∈ᵉ vᵉ in-coalgebraᵉ Xᵉ) →
    is-contrᵉ
      ( edge-element-coalgebraᵉ Xᵉ vᵉ
        ( node-inclusion-element-coalgebraᵉ Hᵉ
          ( root-coalgebraᵉ uᵉ))
        ( root-coalgebraᵉ vᵉ))
  pr1ᵉ (is-contr-edge-to-root-element-coalgebraᵉ Hᵉ) =
    edge-to-root-element-coalgebraᵉ Hᵉ
  pr2ᵉ
    ( is-contr-edge-to-root-element-coalgebraᵉ Hᵉ)
    ( edge-to-root-element-coalgebraᵉ .Hᵉ) =
    reflᵉ
```

### The type of edges from any node to the root is a proposition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : coalgebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ)
  where

  is-proof-irrelevant-edge-to-root-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
    (xᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    is-proof-irrelevantᵉ
      ( edge-element-coalgebraᵉ Xᵉ wᵉ xᵉ
        ( root-coalgebraᵉ wᵉ))
  is-proof-irrelevant-edge-to-root-element-coalgebraᵉ wᵉ ._
    ( edge-to-root-element-coalgebraᵉ Hᵉ) =
    is-contr-edge-to-root-element-coalgebraᵉ Xᵉ Hᵉ

  is-prop-edge-to-root-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
    (xᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    is-propᵉ
      ( edge-element-coalgebraᵉ Xᵉ wᵉ xᵉ
        ( root-coalgebraᵉ wᵉ))
  is-prop-edge-to-root-element-coalgebraᵉ wᵉ xᵉ =
    is-prop-is-proof-irrelevantᵉ
      ( is-proof-irrelevant-edge-to-root-element-coalgebraᵉ
        wᵉ xᵉ)
```

### The underlying graph of any element of a W-type is a directed tree

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : coalgebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ)
  where

  no-edge-from-root-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ) →
    is-emptyᵉ
      ( Σᵉ ( node-element-coalgebraᵉ Xᵉ wᵉ)
          ( edge-element-coalgebraᵉ Xᵉ wᵉ
            ( root-coalgebraᵉ wᵉ)))
  no-edge-from-root-element-coalgebraᵉ wᵉ (xᵉ ,ᵉ ())

  is-empty-eq-root-node-inclusion-element-coalgebraᵉ :
    {vᵉ wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ}
    (Hᵉ : vᵉ ∈ᵉ wᵉ in-coalgebraᵉ Xᵉ)
    (xᵉ : node-element-coalgebraᵉ Xᵉ vᵉ) →
    root-coalgebraᵉ wᵉ ≠ᵉ node-inclusion-element-coalgebraᵉ Hᵉ xᵉ
  is-empty-eq-root-node-inclusion-element-coalgebraᵉ
    Hᵉ xᵉ ()

  has-unique-predecessor-node-inclusion-element-coalgebraᵉ :
    {vᵉ wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ}
    (Hᵉ : vᵉ ∈ᵉ wᵉ in-coalgebraᵉ Xᵉ)
    (xᵉ : node-element-coalgebraᵉ Xᵉ vᵉ) →
    is-contrᵉ
      ( Σᵉ ( node-element-coalgebraᵉ Xᵉ wᵉ)
          ( edge-element-coalgebraᵉ Xᵉ wᵉ
            ( node-inclusion-element-coalgebraᵉ Hᵉ xᵉ)))
  pr1ᵉ
    ( pr1ᵉ
      ( has-unique-predecessor-node-inclusion-element-coalgebraᵉ Hᵉ
        ( root-coalgebraᵉ wᵉ))) =
    root-coalgebraᵉ _
  pr2ᵉ
    ( pr1ᵉ
      ( has-unique-predecessor-node-inclusion-element-coalgebraᵉ Hᵉ
        ( root-coalgebraᵉ wᵉ))) =
    edge-to-root-element-coalgebraᵉ Hᵉ
  pr2ᵉ
    ( has-unique-predecessor-node-inclusion-element-coalgebraᵉ Hᵉ
      ( root-coalgebraᵉ wᵉ))
    ( ._ ,ᵉ edge-to-root-element-coalgebraᵉ .Hᵉ) =
    reflᵉ
  pr1ᵉ
    ( has-unique-predecessor-node-inclusion-element-coalgebraᵉ Hᵉ
      ( node-inclusion-element-coalgebraᵉ Kᵉ xᵉ)) =
    map-Σᵉ
      ( λ yᵉ →
        edge-element-coalgebraᵉ Xᵉ _
          ( node-inclusion-element-coalgebraᵉ Hᵉ
            ( node-inclusion-element-coalgebraᵉ Kᵉ xᵉ))
          ( yᵉ))
      ( node-inclusion-element-coalgebraᵉ Hᵉ)
      ( λ yᵉ → edge-inclusion-element-coalgebraᵉ Hᵉ)
      ( centerᵉ
        ( has-unique-predecessor-node-inclusion-element-coalgebraᵉ Kᵉ xᵉ))
  pr2ᵉ
    ( has-unique-predecessor-node-inclusion-element-coalgebraᵉ Hᵉ
      ( node-inclusion-element-coalgebraᵉ Kᵉ xᵉ))
    ( .(node-inclusion-element-coalgebraᵉ Hᵉ _) ,ᵉ
      edge-inclusion-element-coalgebraᵉ .Hᵉ fᵉ) =
    apᵉ
      ( map-Σᵉ _
        ( node-inclusion-element-coalgebraᵉ Hᵉ)
        ( λ yᵉ → edge-inclusion-element-coalgebraᵉ Hᵉ))
      ( eq-is-contrᵉ
        ( has-unique-predecessor-node-inclusion-element-coalgebraᵉ Kᵉ xᵉ))

  has-unique-predecessor-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
    (xᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    is-contrᵉ
      ( ( root-coalgebraᵉ wᵉ ＝ᵉ xᵉ) +ᵉ
        ( Σᵉ ( node-element-coalgebraᵉ Xᵉ wᵉ)
            ( edge-element-coalgebraᵉ Xᵉ wᵉ xᵉ)))
  has-unique-predecessor-element-coalgebraᵉ wᵉ
    ( root-coalgebraᵉ wᵉ) =
    is-contr-equivᵉ
      ( root-coalgebraᵉ wᵉ ＝ᵉ
        root-coalgebraᵉ wᵉ)
      ( right-unit-law-coproduct-is-emptyᵉ
        ( root-coalgebraᵉ wᵉ ＝ᵉ
          root-coalgebraᵉ wᵉ)
        ( Σᵉ ( node-element-coalgebraᵉ Xᵉ wᵉ)
            ( edge-element-coalgebraᵉ Xᵉ wᵉ
              ( root-coalgebraᵉ wᵉ)))
        ( no-edge-from-root-element-coalgebraᵉ wᵉ))
      ( is-contr-loop-space-root-element-coalgebraᵉ
        ( Xᵉ)
        ( wᵉ))
  has-unique-predecessor-element-coalgebraᵉ wᵉ
    ( node-inclusion-element-coalgebraᵉ Hᵉ xᵉ) =
    is-contr-equivᵉ
      ( Σᵉ ( node-element-coalgebraᵉ Xᵉ wᵉ)
          ( edge-element-coalgebraᵉ Xᵉ wᵉ
            ( node-inclusion-element-coalgebraᵉ Hᵉ xᵉ)))
      ( left-unit-law-coproduct-is-emptyᵉ
        ( root-coalgebraᵉ wᵉ ＝ᵉ
          node-inclusion-element-coalgebraᵉ Hᵉ xᵉ)
        ( Σᵉ ( node-element-coalgebraᵉ Xᵉ wᵉ)
            ( edge-element-coalgebraᵉ Xᵉ wᵉ
              ( node-inclusion-element-coalgebraᵉ Hᵉ xᵉ)))
        ( is-empty-eq-root-node-inclusion-element-coalgebraᵉ Hᵉ xᵉ))
      ( has-unique-predecessor-node-inclusion-element-coalgebraᵉ Hᵉ xᵉ)

  walk-to-root-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
    (xᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    walk-element-coalgebraᵉ Xᵉ wᵉ xᵉ (root-coalgebraᵉ wᵉ)
  walk-to-root-element-coalgebraᵉ wᵉ
    ( root-coalgebraᵉ wᵉ) =
    refl-walk-Directed-Graphᵉ
  walk-to-root-element-coalgebraᵉ wᵉ
    ( node-inclusion-element-coalgebraᵉ {vᵉ} Hᵉ xᵉ) =
    snoc-walk-Directed-Graphᵉ
      ( graph-element-coalgebraᵉ Xᵉ wᵉ)
      ( walk-hom-Directed-Graphᵉ
        ( graph-element-coalgebraᵉ Xᵉ vᵉ)
        ( graph-element-coalgebraᵉ Xᵉ wᵉ)
        ( inclusion-element-coalgebraᵉ Xᵉ Hᵉ)
        ( walk-to-root-element-coalgebraᵉ vᵉ xᵉ))
      ( edge-to-root-element-coalgebraᵉ Hᵉ)

  unique-walk-to-root-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ) →
    is-tree-Directed-Graph'ᵉ
      ( graph-element-coalgebraᵉ Xᵉ wᵉ)
      ( root-coalgebraᵉ wᵉ)
  unique-walk-to-root-element-coalgebraᵉ wᵉ =
    is-tree-unique-direct-successor-Directed-Graph'ᵉ
      ( graph-element-coalgebraᵉ Xᵉ wᵉ)
      ( root-coalgebraᵉ wᵉ)
      ( has-unique-predecessor-element-coalgebraᵉ wᵉ)
      ( walk-to-root-element-coalgebraᵉ wᵉ)

  directed-tree-element-coalgebraᵉ :
    type-coalgebra-polynomial-endofunctorᵉ Xᵉ → Directed-Treeᵉ (l2ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ (directed-tree-element-coalgebraᵉ wᵉ) =
    graph-element-coalgebraᵉ Xᵉ wᵉ
  pr1ᵉ (pr2ᵉ (directed-tree-element-coalgebraᵉ wᵉ)) =
    root-coalgebraᵉ wᵉ
  pr2ᵉ (pr2ᵉ (directed-tree-element-coalgebraᵉ wᵉ)) =
    unique-walk-to-root-element-coalgebraᵉ wᵉ
```

### The underlying graph of an element of a W-type can be given the structure of an enriched directed tree

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : coalgebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ)
  where

  shape-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ) →
    node-element-coalgebraᵉ Xᵉ wᵉ → Aᵉ
  shape-element-coalgebraᵉ wᵉ
    ( root-coalgebraᵉ wᵉ) =
    shape-coalgebra-polynomial-endofunctorᵉ Xᵉ wᵉ
  shape-element-coalgebraᵉ wᵉ
    ( node-inclusion-element-coalgebraᵉ {uᵉ} Hᵉ yᵉ) =
    shape-element-coalgebraᵉ uᵉ yᵉ

  map-enrichment-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
    (xᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    Bᵉ (shape-element-coalgebraᵉ wᵉ xᵉ) →
    Σᵉ ( node-element-coalgebraᵉ Xᵉ wᵉ)
      ( λ yᵉ → edge-element-coalgebraᵉ Xᵉ wᵉ yᵉ xᵉ)
  pr1ᵉ
    ( map-enrichment-element-coalgebraᵉ wᵉ
      ( root-coalgebraᵉ wᵉ) bᵉ) =
    node-inclusion-element-coalgebraᵉ
      ( bᵉ ,ᵉ reflᵉ)
      ( root-coalgebraᵉ (pr2ᵉ (pr2ᵉ Xᵉ wᵉ) bᵉ))
  pr2ᵉ
    ( map-enrichment-element-coalgebraᵉ wᵉ
      ( root-coalgebraᵉ wᵉ)
      ( bᵉ)) =
    edge-to-root-element-coalgebraᵉ (bᵉ ,ᵉ reflᵉ)
  map-enrichment-element-coalgebraᵉ wᵉ
    ( node-inclusion-element-coalgebraᵉ {uᵉ} Hᵉ yᵉ) bᵉ =
    map-Σᵉ
      ( λ zᵉ →
        edge-element-coalgebraᵉ Xᵉ wᵉ zᵉ
          ( node-inclusion-element-coalgebraᵉ Hᵉ yᵉ))
      ( node-inclusion-element-coalgebraᵉ Hᵉ)
      ( λ zᵉ → edge-inclusion-element-coalgebraᵉ Hᵉ)
      ( map-enrichment-element-coalgebraᵉ
        ( uᵉ)
        ( yᵉ)
        ( bᵉ))

  map-inv-enrichment-directed-tree-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
    (xᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    Σᵉ ( node-element-coalgebraᵉ Xᵉ wᵉ)
      ( λ yᵉ → edge-element-coalgebraᵉ Xᵉ wᵉ yᵉ xᵉ) →
    Bᵉ (shape-element-coalgebraᵉ wᵉ xᵉ)
  map-inv-enrichment-directed-tree-element-coalgebraᵉ wᵉ ._
    ( ._ ,ᵉ edge-to-root-element-coalgebraᵉ Hᵉ) =
    pr1ᵉ Hᵉ
  map-inv-enrichment-directed-tree-element-coalgebraᵉ wᵉ ._
    ( ._ ,ᵉ
      edge-inclusion-element-coalgebraᵉ {uᵉ} Hᵉ {xᵉ} {yᵉ} eᵉ) =
    map-inv-enrichment-directed-tree-element-coalgebraᵉ
      ( uᵉ)
      ( yᵉ)
      ( xᵉ ,ᵉ eᵉ)

  is-section-map-inv-enrichment-directed-tree-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
    (xᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    ( ( map-enrichment-element-coalgebraᵉ
        wᵉ xᵉ) ∘ᵉ
      ( map-inv-enrichment-directed-tree-element-coalgebraᵉ
      wᵉ xᵉ)) ~ᵉ idᵉ
  is-section-map-inv-enrichment-directed-tree-element-coalgebraᵉ wᵉ ._
    ( ._ ,ᵉ edge-to-root-element-coalgebraᵉ (bᵉ ,ᵉ reflᵉ)) =
    reflᵉ
  is-section-map-inv-enrichment-directed-tree-element-coalgebraᵉ wᵉ ._
    ( ._ ,ᵉ
      edge-inclusion-element-coalgebraᵉ {uᵉ} Hᵉ {xᵉ} {yᵉ} eᵉ) =
    apᵉ
      ( map-Σᵉ
        ( λ zᵉ →
          edge-element-coalgebraᵉ Xᵉ wᵉ zᵉ
            ( node-inclusion-element-coalgebraᵉ Hᵉ yᵉ))
        ( node-inclusion-element-coalgebraᵉ Hᵉ)
        ( λ zᵉ → edge-inclusion-element-coalgebraᵉ Hᵉ))
      ( is-section-map-inv-enrichment-directed-tree-element-coalgebraᵉ uᵉ yᵉ
        ( xᵉ ,ᵉ eᵉ))

  is-retraction-map-inv-enrichment-directed-tree-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
    (xᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    ( map-inv-enrichment-directed-tree-element-coalgebraᵉ wᵉ xᵉ ∘ᵉ
      map-enrichment-element-coalgebraᵉ wᵉ xᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-enrichment-directed-tree-element-coalgebraᵉ wᵉ
    ( root-coalgebraᵉ wᵉ) bᵉ =
    reflᵉ
  is-retraction-map-inv-enrichment-directed-tree-element-coalgebraᵉ wᵉ
    ( node-inclusion-element-coalgebraᵉ {uᵉ} Hᵉ yᵉ) bᵉ =
    is-retraction-map-inv-enrichment-directed-tree-element-coalgebraᵉ uᵉ yᵉ bᵉ

  is-equiv-map-enrichment-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
    (xᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    is-equivᵉ (map-enrichment-element-coalgebraᵉ wᵉ xᵉ)
  is-equiv-map-enrichment-element-coalgebraᵉ wᵉ xᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-enrichment-directed-tree-element-coalgebraᵉ wᵉ xᵉ)
      ( is-section-map-inv-enrichment-directed-tree-element-coalgebraᵉ wᵉ xᵉ)
      ( is-retraction-map-inv-enrichment-directed-tree-element-coalgebraᵉ wᵉ xᵉ)

  enrichment-directed-tree-element-coalgebraᵉ :
    (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
    (xᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    Bᵉ (shape-element-coalgebraᵉ wᵉ xᵉ) ≃ᵉ
    Σᵉ ( node-element-coalgebraᵉ Xᵉ wᵉ)
      ( λ yᵉ → edge-element-coalgebraᵉ Xᵉ wᵉ yᵉ xᵉ)
  pr1ᵉ (enrichment-directed-tree-element-coalgebraᵉ wᵉ xᵉ) =
    map-enrichment-element-coalgebraᵉ wᵉ xᵉ
  pr2ᵉ (enrichment-directed-tree-element-coalgebraᵉ wᵉ xᵉ) =
    is-equiv-map-enrichment-element-coalgebraᵉ wᵉ xᵉ

  enriched-directed-tree-element-coalgebraᵉ :
    type-coalgebra-polynomial-endofunctorᵉ Xᵉ →
    Enriched-Directed-Treeᵉ (l2ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l3ᵉ) Aᵉ Bᵉ
  pr1ᵉ (enriched-directed-tree-element-coalgebraᵉ wᵉ) =
    directed-tree-element-coalgebraᵉ Xᵉ wᵉ
  pr1ᵉ
    ( pr2ᵉ (enriched-directed-tree-element-coalgebraᵉ wᵉ)) =
    shape-element-coalgebraᵉ wᵉ
  pr2ᵉ
    ( pr2ᵉ (enriched-directed-tree-element-coalgebraᵉ wᵉ)) =
    enrichment-directed-tree-element-coalgebraᵉ wᵉ
```

### The underlying tree of `w` is the combinator tree of the underlying trees of `component X w b` indexed by `b : B (shape w)`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : coalgebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ)
  (wᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ)
  where

  node-compute-directed-tree-element-coalgebraᵉ :
    node-element-coalgebraᵉ Xᵉ wᵉ →
    node-combinator-Directed-Treeᵉ
      ( λ bᵉ → directed-tree-element-coalgebraᵉ Xᵉ
        ( component-coalgebra-polynomial-endofunctorᵉ Xᵉ wᵉ bᵉ))
  node-compute-directed-tree-element-coalgebraᵉ
    ( root-coalgebraᵉ wᵉ) =
    root-combinator-Directed-Treeᵉ
  node-compute-directed-tree-element-coalgebraᵉ
    ( node-inclusion-element-coalgebraᵉ (bᵉ ,ᵉ reflᵉ) xᵉ) =
    node-inclusion-combinator-Directed-Treeᵉ bᵉ xᵉ

  map-inv-node-compute-directed-tree-element-coalgebraᵉ :
    node-combinator-Directed-Treeᵉ
      ( λ bᵉ →
        directed-tree-element-coalgebraᵉ Xᵉ
          ( component-coalgebra-polynomial-endofunctorᵉ Xᵉ wᵉ bᵉ)) →
    node-element-coalgebraᵉ Xᵉ wᵉ
  map-inv-node-compute-directed-tree-element-coalgebraᵉ
    root-combinator-Directed-Treeᵉ =
    root-coalgebraᵉ _
  map-inv-node-compute-directed-tree-element-coalgebraᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ bᵉ xᵉ) =
    node-inclusion-element-coalgebraᵉ (bᵉ ,ᵉ reflᵉ) xᵉ

  is-section-map-inv-node-compute-directed-tree-element-coalgebraᵉ :
    ( node-compute-directed-tree-element-coalgebraᵉ ∘ᵉ
      map-inv-node-compute-directed-tree-element-coalgebraᵉ) ~ᵉ idᵉ
  is-section-map-inv-node-compute-directed-tree-element-coalgebraᵉ
    root-combinator-Directed-Treeᵉ =
    reflᵉ
  is-section-map-inv-node-compute-directed-tree-element-coalgebraᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ) =
    reflᵉ

  is-retraction-map-inv-node-compute-directed-tree-element-coalgebraᵉ :
    ( map-inv-node-compute-directed-tree-element-coalgebraᵉ ∘ᵉ
      node-compute-directed-tree-element-coalgebraᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-node-compute-directed-tree-element-coalgebraᵉ
    ( root-coalgebraᵉ wᵉ) =
    reflᵉ
  is-retraction-map-inv-node-compute-directed-tree-element-coalgebraᵉ
    ( node-inclusion-element-coalgebraᵉ (bᵉ ,ᵉ reflᵉ) xᵉ) =
    reflᵉ

  is-equiv-node-compute-directed-tree-element-coalgebraᵉ :
    is-equivᵉ node-compute-directed-tree-element-coalgebraᵉ
  is-equiv-node-compute-directed-tree-element-coalgebraᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-node-compute-directed-tree-element-coalgebraᵉ
      is-section-map-inv-node-compute-directed-tree-element-coalgebraᵉ
      is-retraction-map-inv-node-compute-directed-tree-element-coalgebraᵉ

  equiv-node-compute-directed-tree-element-coalgebraᵉ :
    node-element-coalgebraᵉ Xᵉ wᵉ ≃ᵉ
    node-combinator-Directed-Treeᵉ
      ( λ bᵉ →
        directed-tree-element-coalgebraᵉ Xᵉ
          ( component-coalgebra-polynomial-endofunctorᵉ Xᵉ wᵉ bᵉ))
  pr1ᵉ equiv-node-compute-directed-tree-element-coalgebraᵉ =
    node-compute-directed-tree-element-coalgebraᵉ
  pr2ᵉ equiv-node-compute-directed-tree-element-coalgebraᵉ =
    is-equiv-node-compute-directed-tree-element-coalgebraᵉ

  edge-compute-directed-tree-element-coalgebraᵉ :
    (xᵉ yᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    edge-element-coalgebraᵉ Xᵉ wᵉ xᵉ yᵉ →
    edge-combinator-Directed-Treeᵉ
      ( λ bᵉ →
        directed-tree-element-coalgebraᵉ Xᵉ
          ( component-coalgebra-polynomial-endofunctorᵉ Xᵉ wᵉ bᵉ))
      ( node-compute-directed-tree-element-coalgebraᵉ xᵉ)
      ( node-compute-directed-tree-element-coalgebraᵉ yᵉ)
  edge-compute-directed-tree-element-coalgebraᵉ ._ ._
    ( edge-to-root-element-coalgebraᵉ (bᵉ ,ᵉ reflᵉ)) =
    edge-to-root-combinator-Directed-Treeᵉ bᵉ
  edge-compute-directed-tree-element-coalgebraᵉ ._ ._
    ( edge-inclusion-element-coalgebraᵉ (bᵉ ,ᵉ reflᵉ) eᵉ) =
    edge-inclusion-combinator-Directed-Treeᵉ bᵉ _ _ eᵉ

  map-inv-edge-compute-directed-tree-element-coalgebra'ᵉ :
    ( xᵉ yᵉ :
      node-combinator-Directed-Treeᵉ
        ( directed-tree-element-coalgebraᵉ Xᵉ ∘ᵉ
          component-coalgebra-polynomial-endofunctorᵉ Xᵉ wᵉ)) →
    edge-combinator-Directed-Treeᵉ
      ( λ bᵉ →
        directed-tree-element-coalgebraᵉ Xᵉ
          ( component-coalgebra-polynomial-endofunctorᵉ Xᵉ wᵉ bᵉ))
      ( xᵉ)
      ( yᵉ) →
    edge-element-coalgebraᵉ Xᵉ wᵉ
      ( map-inv-node-compute-directed-tree-element-coalgebraᵉ xᵉ)
      ( map-inv-node-compute-directed-tree-element-coalgebraᵉ yᵉ)
  map-inv-edge-compute-directed-tree-element-coalgebra'ᵉ ._ ._
    ( edge-to-root-combinator-Directed-Treeᵉ bᵉ) =
    edge-to-root-element-coalgebraᵉ (bᵉ ,ᵉ reflᵉ)
  map-inv-edge-compute-directed-tree-element-coalgebra'ᵉ ._ ._
    ( edge-inclusion-combinator-Directed-Treeᵉ bᵉ xᵉ yᵉ eᵉ) =
    edge-inclusion-element-coalgebraᵉ (bᵉ ,ᵉ reflᵉ) eᵉ

  map-inv-edge-compute-directed-tree-element-coalgebraᵉ :
    ( xᵉ yᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    edge-combinator-Directed-Treeᵉ
      ( λ bᵉ →
        directed-tree-element-coalgebraᵉ Xᵉ
          ( component-coalgebra-polynomial-endofunctorᵉ Xᵉ wᵉ bᵉ))
      ( node-compute-directed-tree-element-coalgebraᵉ xᵉ)
      ( node-compute-directed-tree-element-coalgebraᵉ yᵉ) →
    edge-element-coalgebraᵉ Xᵉ wᵉ xᵉ yᵉ
  map-inv-edge-compute-directed-tree-element-coalgebraᵉ xᵉ yᵉ =
    ( binary-trᵉ
      ( edge-element-coalgebraᵉ Xᵉ wᵉ)
      ( is-retraction-map-inv-node-compute-directed-tree-element-coalgebraᵉ xᵉ)
      ( is-retraction-map-inv-node-compute-directed-tree-element-coalgebraᵉ yᵉ)) ∘ᵉ
    ( map-inv-edge-compute-directed-tree-element-coalgebra'ᵉ
      ( node-compute-directed-tree-element-coalgebraᵉ xᵉ)
      ( node-compute-directed-tree-element-coalgebraᵉ yᵉ))

  is-section-map-inv-edge-compute-directed-tree-element-coalgebra'ᵉ :
    ( xᵉ yᵉ :
      node-combinator-Directed-Treeᵉ
        ( directed-tree-element-coalgebraᵉ Xᵉ ∘ᵉ
          component-coalgebra-polynomial-endofunctorᵉ Xᵉ wᵉ)) →
    ( eᵉ :
      edge-combinator-Directed-Treeᵉ
        ( λ bᵉ →
          directed-tree-element-coalgebraᵉ Xᵉ
            ( component-coalgebra-polynomial-endofunctorᵉ Xᵉ wᵉ bᵉ))
        ( xᵉ)
        ( yᵉ)) →
    binary-trᵉ
      ( edge-combinator-Directed-Treeᵉ
        ( λ bᵉ →
          directed-tree-element-coalgebraᵉ Xᵉ
            ( component-coalgebra-polynomial-endofunctorᵉ Xᵉ wᵉ bᵉ)))
      ( is-section-map-inv-node-compute-directed-tree-element-coalgebraᵉ xᵉ)
      ( is-section-map-inv-node-compute-directed-tree-element-coalgebraᵉ yᵉ)
      ( edge-compute-directed-tree-element-coalgebraᵉ
        ( map-inv-node-compute-directed-tree-element-coalgebraᵉ xᵉ)
        ( map-inv-node-compute-directed-tree-element-coalgebraᵉ yᵉ)
        ( map-inv-edge-compute-directed-tree-element-coalgebra'ᵉ xᵉ yᵉ eᵉ)) ＝ᵉ eᵉ
  is-section-map-inv-edge-compute-directed-tree-element-coalgebra'ᵉ ._ ._
    ( edge-to-root-combinator-Directed-Treeᵉ iᵉ) =
    reflᵉ
  is-section-map-inv-edge-compute-directed-tree-element-coalgebra'ᵉ ._ ._
    ( edge-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ yᵉ eᵉ) =
    reflᵉ

  is-section-map-inv-edge-compute-directed-tree-element-coalgebraᵉ :
    (xᵉ yᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    ( eᵉ :
      edge-combinator-Directed-Treeᵉ
        ( λ bᵉ →
          directed-tree-element-coalgebraᵉ Xᵉ
            ( component-coalgebra-polynomial-endofunctorᵉ Xᵉ wᵉ bᵉ))
        ( node-compute-directed-tree-element-coalgebraᵉ xᵉ)
        ( node-compute-directed-tree-element-coalgebraᵉ yᵉ)) →
    edge-compute-directed-tree-element-coalgebraᵉ xᵉ yᵉ
      ( map-inv-edge-compute-directed-tree-element-coalgebraᵉ xᵉ yᵉ eᵉ) ＝ᵉ eᵉ
  is-section-map-inv-edge-compute-directed-tree-element-coalgebraᵉ
    ( node-inclusion-element-coalgebraᵉ (bᵉ ,ᵉ reflᵉ) xᵉ)
    ( root-coalgebraᵉ _)
    ( eᵉ) =
    is-section-map-inv-edge-compute-directed-tree-element-coalgebra'ᵉ
      ( node-compute-directed-tree-element-coalgebraᵉ _)
      ( node-compute-directed-tree-element-coalgebraᵉ _)
      ( eᵉ)
  is-section-map-inv-edge-compute-directed-tree-element-coalgebraᵉ
    ( node-inclusion-element-coalgebraᵉ (bᵉ ,ᵉ reflᵉ) xᵉ)
    ( node-inclusion-element-coalgebraᵉ (cᵉ ,ᵉ reflᵉ) yᵉ)
    ( eᵉ) =
    is-section-map-inv-edge-compute-directed-tree-element-coalgebra'ᵉ
      ( node-compute-directed-tree-element-coalgebraᵉ _)
      ( node-compute-directed-tree-element-coalgebraᵉ _)
      ( eᵉ)

  is-retraction-map-inv-edge-compute-directed-tree-element-coalgebraᵉ :
    (xᵉ yᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) (eᵉ : edge-element-coalgebraᵉ Xᵉ wᵉ xᵉ yᵉ) →
    map-inv-edge-compute-directed-tree-element-coalgebraᵉ xᵉ yᵉ
      ( edge-compute-directed-tree-element-coalgebraᵉ xᵉ yᵉ eᵉ) ＝ᵉ eᵉ
  is-retraction-map-inv-edge-compute-directed-tree-element-coalgebraᵉ ._ ._
    ( edge-to-root-element-coalgebraᵉ (bᵉ ,ᵉ reflᵉ)) = reflᵉ
  is-retraction-map-inv-edge-compute-directed-tree-element-coalgebraᵉ ._ ._
    ( edge-inclusion-element-coalgebraᵉ (bᵉ ,ᵉ reflᵉ) eᵉ) = reflᵉ

  is-equiv-edge-compute-directed-tree-element-coalgebraᵉ :
    (xᵉ yᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    is-equivᵉ (edge-compute-directed-tree-element-coalgebraᵉ xᵉ yᵉ)
  is-equiv-edge-compute-directed-tree-element-coalgebraᵉ xᵉ yᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-edge-compute-directed-tree-element-coalgebraᵉ xᵉ yᵉ)
      ( is-section-map-inv-edge-compute-directed-tree-element-coalgebraᵉ xᵉ yᵉ)
      ( is-retraction-map-inv-edge-compute-directed-tree-element-coalgebraᵉ xᵉ yᵉ)

  equiv-edge-compute-directed-tree-element-coalgebraᵉ :
    (xᵉ yᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    edge-element-coalgebraᵉ Xᵉ wᵉ xᵉ yᵉ ≃ᵉ
    edge-combinator-Directed-Treeᵉ
      ( λ bᵉ →
        directed-tree-element-coalgebraᵉ Xᵉ
          ( component-coalgebra-polynomial-endofunctorᵉ Xᵉ wᵉ bᵉ))
      ( node-compute-directed-tree-element-coalgebraᵉ xᵉ)
      ( node-compute-directed-tree-element-coalgebraᵉ yᵉ)
  pr1ᵉ (equiv-edge-compute-directed-tree-element-coalgebraᵉ xᵉ yᵉ) =
    edge-compute-directed-tree-element-coalgebraᵉ xᵉ yᵉ
  pr2ᵉ (equiv-edge-compute-directed-tree-element-coalgebraᵉ xᵉ yᵉ) =
    is-equiv-edge-compute-directed-tree-element-coalgebraᵉ xᵉ yᵉ

  compute-directed-tree-element-coalgebraᵉ :
    equiv-Directed-Treeᵉ
      ( directed-tree-element-coalgebraᵉ Xᵉ wᵉ)
      ( combinator-Directed-Treeᵉ
        ( λ bᵉ →
          directed-tree-element-coalgebraᵉ Xᵉ
            ( component-coalgebra-polynomial-endofunctorᵉ Xᵉ wᵉ bᵉ)))
  pr1ᵉ compute-directed-tree-element-coalgebraᵉ =
    equiv-node-compute-directed-tree-element-coalgebraᵉ
  pr2ᵉ compute-directed-tree-element-coalgebraᵉ =
    equiv-edge-compute-directed-tree-element-coalgebraᵉ

  shape-compute-enriched-directed-tree-element-coalgebraᵉ :
    shape-element-coalgebraᵉ Xᵉ wᵉ ~ᵉ
    ( ( shape-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
        ( λ bᵉ →
          enriched-directed-tree-element-coalgebraᵉ Xᵉ
            ( component-coalgebra-polynomial-endofunctorᵉ Xᵉ wᵉ bᵉ))) ∘ᵉ
      ( node-compute-directed-tree-element-coalgebraᵉ))
  shape-compute-enriched-directed-tree-element-coalgebraᵉ (root-coalgebraᵉ _) =
    reflᵉ
  shape-compute-enriched-directed-tree-element-coalgebraᵉ
    ( node-inclusion-element-coalgebraᵉ (bᵉ ,ᵉ reflᵉ) xᵉ) =
    reflᵉ

  enrichment-compute-enriched-directed-tree-element-coalgebraᵉ :
    (xᵉ : node-element-coalgebraᵉ Xᵉ wᵉ) →
    htpy-equivᵉ
      ( ( equiv-direct-predecessor-equiv-Directed-Treeᵉ
          ( directed-tree-element-coalgebraᵉ Xᵉ wᵉ)
          ( combinator-Directed-Treeᵉ
            ( λ bᵉ →
              directed-tree-element-coalgebraᵉ Xᵉ
                ( component-coalgebra-polynomial-endofunctorᵉ Xᵉ wᵉ bᵉ)))
          ( compute-directed-tree-element-coalgebraᵉ)
          ( xᵉ)) ∘eᵉ
        ( enrichment-directed-tree-element-coalgebraᵉ Xᵉ wᵉ xᵉ))
      ( ( enrichment-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
          ( λ bᵉ →
            enriched-directed-tree-element-coalgebraᵉ Xᵉ
              ( component-coalgebra-polynomial-endofunctorᵉ Xᵉ wᵉ bᵉ))
          ( node-compute-directed-tree-element-coalgebraᵉ xᵉ)) ∘eᵉ
        ( equiv-trᵉ Bᵉ
          ( shape-compute-enriched-directed-tree-element-coalgebraᵉ xᵉ)))
  enrichment-compute-enriched-directed-tree-element-coalgebraᵉ
    ( root-coalgebraᵉ _)
    ( bᵉ) = reflᵉ
  enrichment-compute-enriched-directed-tree-element-coalgebraᵉ
    ( node-inclusion-element-coalgebraᵉ (cᵉ ,ᵉ reflᵉ) xᵉ) bᵉ =
    reflᵉ

  compute-enriched-directed-tree-element-coalgebraᵉ :
    equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
      ( enriched-directed-tree-element-coalgebraᵉ Xᵉ wᵉ)
      ( combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
        ( λ bᵉ →
          enriched-directed-tree-element-coalgebraᵉ Xᵉ
            ( component-coalgebra-polynomial-endofunctorᵉ Xᵉ wᵉ bᵉ)))
  pr1ᵉ compute-enriched-directed-tree-element-coalgebraᵉ =
    compute-directed-tree-element-coalgebraᵉ
  pr1ᵉ (pr2ᵉ compute-enriched-directed-tree-element-coalgebraᵉ) =
    shape-compute-enriched-directed-tree-element-coalgebraᵉ
  pr2ᵉ (pr2ᵉ compute-enriched-directed-tree-element-coalgebraᵉ) =
    enrichment-compute-enriched-directed-tree-element-coalgebraᵉ
```