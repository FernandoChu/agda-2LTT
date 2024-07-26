# Walks in undirected graphs

```agda
module graph-theory.walks-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import graph-theory.undirected-graphsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ **walk**ᵉ in anᵉ [undirectedᵉ graph](graph-theory.undirected-graphs.mdᵉ) consistsᵉ
ofᵉ aᵉ [list](lists.lists.mdᵉ) ofᵉ edgesᵉ thatᵉ connectᵉ theᵉ startingᵉ pointᵉ with theᵉ
endᵉ point.ᵉ Walksᵉ mayᵉ repeatᵉ edgesᵉ andᵉ passᵉ throughᵉ theᵉ sameᵉ vertexᵉ multipleᵉ
times.ᵉ

## Definitions

### Walks in undirected graphs

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  where

  data
    walk-Undirected-Graphᵉ (xᵉ : vertex-Undirected-Graphᵉ Gᵉ) :
      vertex-Undirected-Graphᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lzero)
      where
      refl-walk-Undirected-Graphᵉ : walk-Undirected-Graphᵉ xᵉ xᵉ
      cons-walk-Undirected-Graphᵉ :
        (pᵉ : unordered-pairᵉ (vertex-Undirected-Graphᵉ Gᵉ)) →
        (eᵉ : edge-Undirected-Graphᵉ Gᵉ pᵉ) →
        {yᵉ : type-unordered-pairᵉ pᵉ} →
        walk-Undirected-Graphᵉ xᵉ (element-unordered-pairᵉ pᵉ yᵉ) →
        walk-Undirected-Graphᵉ xᵉ (other-element-unordered-pairᵉ pᵉ yᵉ)
```

### The vertices on a walk

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) {xᵉ : vertex-Undirected-Graphᵉ Gᵉ}
  where

  is-vertex-on-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) →
    vertex-Undirected-Graphᵉ Gᵉ → UUᵉ l1ᵉ
  is-vertex-on-walk-Undirected-Graphᵉ refl-walk-Undirected-Graphᵉ vᵉ = xᵉ ＝ᵉ vᵉ
  is-vertex-on-walk-Undirected-Graphᵉ (cons-walk-Undirected-Graphᵉ pᵉ eᵉ {yᵉ} wᵉ) vᵉ =
    ( is-vertex-on-walk-Undirected-Graphᵉ wᵉ vᵉ) +ᵉ
    ( other-element-unordered-pairᵉ pᵉ yᵉ ＝ᵉ vᵉ)

  vertex-on-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) → UUᵉ l1ᵉ
  vertex-on-walk-Undirected-Graphᵉ wᵉ =
    Σᵉ (vertex-Undirected-Graphᵉ Gᵉ) (is-vertex-on-walk-Undirected-Graphᵉ wᵉ)

  vertex-vertex-on-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) →
    vertex-on-walk-Undirected-Graphᵉ wᵉ → vertex-Undirected-Graphᵉ Gᵉ
  vertex-vertex-on-walk-Undirected-Graphᵉ wᵉ = pr1ᵉ
```

### Edges on a walk

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) {xᵉ : vertex-Undirected-Graphᵉ Gᵉ}
  where

  is-edge-on-walk-Undirected-Graph'ᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) →
    total-edge-Undirected-Graphᵉ Gᵉ → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  is-edge-on-walk-Undirected-Graph'ᵉ refl-walk-Undirected-Graphᵉ eᵉ =
    raise-emptyᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  is-edge-on-walk-Undirected-Graph'ᵉ (cons-walk-Undirected-Graphᵉ qᵉ fᵉ wᵉ) eᵉ =
    ( is-edge-on-walk-Undirected-Graph'ᵉ wᵉ eᵉ) +ᵉ
    ( pairᵉ qᵉ fᵉ ＝ᵉ eᵉ)

  is-edge-on-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) →
    (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
    edge-Undirected-Graphᵉ Gᵉ pᵉ → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  is-edge-on-walk-Undirected-Graphᵉ wᵉ pᵉ eᵉ =
    is-edge-on-walk-Undirected-Graph'ᵉ wᵉ (pairᵉ pᵉ eᵉ)

  edge-on-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) →
    UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  edge-on-walk-Undirected-Graphᵉ wᵉ =
    Σᵉ ( total-edge-Undirected-Graphᵉ Gᵉ)
      ( λ eᵉ → is-edge-on-walk-Undirected-Graph'ᵉ wᵉ eᵉ)

  edge-edge-on-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) →
    edge-on-walk-Undirected-Graphᵉ wᵉ → total-edge-Undirected-Graphᵉ Gᵉ
  edge-edge-on-walk-Undirected-Graphᵉ wᵉ = pr1ᵉ
```

### Concatenating walks

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) {xᵉ : vertex-Undirected-Graphᵉ Gᵉ}
  where

  concat-walk-Undirected-Graphᵉ :
    {yᵉ zᵉ : vertex-Undirected-Graphᵉ Gᵉ} →
    walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ → walk-Undirected-Graphᵉ Gᵉ yᵉ zᵉ →
    walk-Undirected-Graphᵉ Gᵉ xᵉ zᵉ
  concat-walk-Undirected-Graphᵉ wᵉ refl-walk-Undirected-Graphᵉ = wᵉ
  concat-walk-Undirected-Graphᵉ wᵉ (cons-walk-Undirected-Graphᵉ pᵉ eᵉ vᵉ) =
    cons-walk-Undirected-Graphᵉ pᵉ eᵉ (concat-walk-Undirected-Graphᵉ wᵉ vᵉ)
```

### The length of a walk

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) {xᵉ : vertex-Undirected-Graphᵉ Gᵉ}
  where

  length-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} → walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ → ℕᵉ
  length-walk-Undirected-Graphᵉ refl-walk-Undirected-Graphᵉ = 0
  length-walk-Undirected-Graphᵉ (cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ) =
    succ-ℕᵉ (length-walk-Undirected-Graphᵉ wᵉ)
```

## Properties

### The type of vertices on the constant walk is contractible

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) (xᵉ : vertex-Undirected-Graphᵉ Gᵉ)
  where

  is-contr-vertex-on-walk-refl-walk-Undirected-Graphᵉ :
    is-contrᵉ
      ( vertex-on-walk-Undirected-Graphᵉ Gᵉ (refl-walk-Undirected-Graphᵉ {xᵉ = xᵉ}))
  is-contr-vertex-on-walk-refl-walk-Undirected-Graphᵉ =
    is-torsorial-Idᵉ xᵉ
```

### The type of vertices on a walk is equivalent to `Fin (n + 1)` where `n` is the length of the walk

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) {xᵉ : vertex-Undirected-Graphᵉ Gᵉ}
  where

  compute-vertex-on-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) →
    vertex-on-walk-Undirected-Graphᵉ Gᵉ wᵉ ≃ᵉ
    Finᵉ (succ-ℕᵉ (length-walk-Undirected-Graphᵉ Gᵉ wᵉ))
  compute-vertex-on-walk-Undirected-Graphᵉ refl-walk-Undirected-Graphᵉ =
    equiv-is-contrᵉ
      ( is-contr-vertex-on-walk-refl-walk-Undirected-Graphᵉ Gᵉ xᵉ)
      ( is-contr-Fin-one-ℕᵉ)
  compute-vertex-on-walk-Undirected-Graphᵉ
    ( cons-walk-Undirected-Graphᵉ pᵉ eᵉ {yᵉ} wᵉ) =
    ( equiv-coproductᵉ
      ( compute-vertex-on-walk-Undirected-Graphᵉ wᵉ)
      ( equiv-is-contrᵉ
        ( is-torsorial-Idᵉ (other-element-unordered-pairᵉ pᵉ yᵉ))
        ( is-contr-unitᵉ))) ∘eᵉ
    ( left-distributive-Σ-coproductᵉ
      ( vertex-Undirected-Graphᵉ Gᵉ)
      ( is-vertex-on-walk-Undirected-Graphᵉ Gᵉ wᵉ)
      ( λ zᵉ → other-element-unordered-pairᵉ pᵉ yᵉ ＝ᵉ zᵉ))
```

### The type of edges on a constant walk is empty

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) (xᵉ : vertex-Undirected-Graphᵉ Gᵉ)
  where

  is-empty-edge-on-walk-refl-walk-Undirected-Graphᵉ :
    is-emptyᵉ
      ( edge-on-walk-Undirected-Graphᵉ Gᵉ (refl-walk-Undirected-Graphᵉ {xᵉ = xᵉ}))
  is-empty-edge-on-walk-refl-walk-Undirected-Graphᵉ = is-empty-raise-emptyᵉ ∘ᵉ pr2ᵉ
```

### The type of edges on a walk is equivalent to `Fin n` where `n` is the length of the walk

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) {xᵉ : vertex-Undirected-Graphᵉ Gᵉ}
  where

  compute-edge-on-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) →
    edge-on-walk-Undirected-Graphᵉ Gᵉ wᵉ ≃ᵉ Finᵉ (length-walk-Undirected-Graphᵉ Gᵉ wᵉ)
  compute-edge-on-walk-Undirected-Graphᵉ refl-walk-Undirected-Graphᵉ =
    equiv-is-emptyᵉ
      ( is-empty-edge-on-walk-refl-walk-Undirected-Graphᵉ Gᵉ xᵉ)
      ( idᵉ)
  compute-edge-on-walk-Undirected-Graphᵉ (cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ) =
    ( equiv-coproductᵉ
      ( compute-edge-on-walk-Undirected-Graphᵉ wᵉ)
      ( equiv-is-contrᵉ
        ( is-torsorial-Idᵉ (pairᵉ pᵉ eᵉ))
        ( is-contr-unitᵉ))) ∘eᵉ
    ( left-distributive-Σ-coproductᵉ
      ( total-edge-Undirected-Graphᵉ Gᵉ)
      ( is-edge-on-walk-Undirected-Graph'ᵉ Gᵉ wᵉ)
      ( λ zᵉ → pairᵉ pᵉ eᵉ ＝ᵉ zᵉ))
```

### Right unit law for concatenation of walks

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) {xᵉ : vertex-Undirected-Graphᵉ Gᵉ}
  where

  right-unit-law-concat-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) →
    (concat-walk-Undirected-Graphᵉ Gᵉ wᵉ refl-walk-Undirected-Graphᵉ) ＝ᵉ wᵉ
  right-unit-law-concat-walk-Undirected-Graphᵉ refl-walk-Undirected-Graphᵉ = reflᵉ
  right-unit-law-concat-walk-Undirected-Graphᵉ
    ( cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ) =
    apᵉ
      ( cons-walk-Undirected-Graphᵉ pᵉ eᵉ)
      ( right-unit-law-concat-walk-Undirected-Graphᵉ wᵉ)
```

### For any walk `w` from `x` to `y` and any vertex `v` on `w`, we can decompose `w` into a walk `w1` from `x` to `v` and a walk `w2` from `v` to `y`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) {xᵉ : vertex-Undirected-Graphᵉ Gᵉ}
  where

  first-segment-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ)
    (vᵉ : vertex-on-walk-Undirected-Graphᵉ Gᵉ wᵉ) →
    walk-Undirected-Graphᵉ Gᵉ xᵉ (vertex-vertex-on-walk-Undirected-Graphᵉ Gᵉ wᵉ vᵉ)
  first-segment-walk-Undirected-Graphᵉ
    refl-walk-Undirected-Graphᵉ (vᵉ ,ᵉ reflᵉ) = refl-walk-Undirected-Graphᵉ
  first-segment-walk-Undirected-Graphᵉ
    (cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ) (vᵉ ,ᵉ inlᵉ xᵉ) =
    first-segment-walk-Undirected-Graphᵉ wᵉ (pairᵉ vᵉ xᵉ)
  first-segment-walk-Undirected-Graphᵉ
    ( cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ)
    ( .(other-element-unordered-pairᵉ pᵉ _) ,ᵉ inrᵉ reflᵉ) =
    cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ

  second-segment-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ)
    (vᵉ : vertex-on-walk-Undirected-Graphᵉ Gᵉ wᵉ) →
    walk-Undirected-Graphᵉ Gᵉ (vertex-vertex-on-walk-Undirected-Graphᵉ Gᵉ wᵉ vᵉ) yᵉ
  second-segment-walk-Undirected-Graphᵉ
    refl-walk-Undirected-Graphᵉ (vᵉ ,ᵉ reflᵉ) = refl-walk-Undirected-Graphᵉ
  second-segment-walk-Undirected-Graphᵉ
    (cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ) (vᵉ ,ᵉ inlᵉ Hᵉ) =
    cons-walk-Undirected-Graphᵉ pᵉ eᵉ
      ( second-segment-walk-Undirected-Graphᵉ wᵉ (pairᵉ vᵉ Hᵉ))
  second-segment-walk-Undirected-Graphᵉ
    ( cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ)
    ( .(other-element-unordered-pairᵉ pᵉ _) ,ᵉ inrᵉ reflᵉ) =
    refl-walk-Undirected-Graphᵉ

  eq-decompose-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ)
    (vᵉ : vertex-on-walk-Undirected-Graphᵉ Gᵉ wᵉ) →
    ( concat-walk-Undirected-Graphᵉ Gᵉ
      ( first-segment-walk-Undirected-Graphᵉ wᵉ vᵉ)
      ( second-segment-walk-Undirected-Graphᵉ wᵉ vᵉ)) ＝ᵉ wᵉ
  eq-decompose-walk-Undirected-Graphᵉ refl-walk-Undirected-Graphᵉ (vᵉ ,ᵉ reflᵉ) =
    reflᵉ
  eq-decompose-walk-Undirected-Graphᵉ
    ( cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ) (vᵉ ,ᵉ inlᵉ Hᵉ) =
    apᵉ
      ( cons-walk-Undirected-Graphᵉ pᵉ eᵉ)
      ( eq-decompose-walk-Undirected-Graphᵉ wᵉ (pairᵉ vᵉ Hᵉ))
  eq-decompose-walk-Undirected-Graphᵉ
    ( cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ)
    ( .(other-element-unordered-pairᵉ pᵉ _) ,ᵉ inrᵉ reflᵉ) =
    right-unit-law-concat-walk-Undirected-Graphᵉ Gᵉ
      ( cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ)
```

### For any edge `e` on `p`, if `v` is a vertex on `w` then it is a vertex on `cons p e w`

```agda
is-vertex-on-walk-cons-walk-Undirected-Graphᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ)
  (eᵉ : edge-Undirected-Graphᵉ Gᵉ pᵉ) →
  {xᵉ : vertex-Undirected-Graphᵉ Gᵉ} {yᵉ : type-unordered-pairᵉ pᵉ} →
  (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ (element-unordered-pairᵉ pᵉ yᵉ)) →
  {vᵉ : vertex-Undirected-Graphᵉ Gᵉ} →
  is-vertex-on-walk-Undirected-Graphᵉ Gᵉ wᵉ vᵉ →
  is-vertex-on-walk-Undirected-Graphᵉ Gᵉ (cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ) vᵉ
is-vertex-on-walk-cons-walk-Undirected-Graphᵉ Gᵉ pᵉ eᵉ wᵉ = inlᵉ
```

### For any decomposition of a walk `w` into `w1` followed by `w2`, any vertex on `w` is a vertex on `w1` or on `w2`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) {xᵉ : vertex-Undirected-Graphᵉ Gᵉ}
  where

  is-vertex-on-first-segment-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) →
    (vᵉ : vertex-on-walk-Undirected-Graphᵉ Gᵉ wᵉ) →
    vertex-Undirected-Graphᵉ Gᵉ → UUᵉ l1ᵉ
  is-vertex-on-first-segment-walk-Undirected-Graphᵉ wᵉ vᵉ =
    is-vertex-on-walk-Undirected-Graphᵉ Gᵉ
      ( first-segment-walk-Undirected-Graphᵉ Gᵉ wᵉ vᵉ)

  is-vertex-on-second-segment-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) →
    (vᵉ : vertex-on-walk-Undirected-Graphᵉ Gᵉ wᵉ) →
    vertex-Undirected-Graphᵉ Gᵉ → UUᵉ l1ᵉ
  is-vertex-on-second-segment-walk-Undirected-Graphᵉ wᵉ vᵉ =
    is-vertex-on-walk-Undirected-Graphᵉ Gᵉ
      ( second-segment-walk-Undirected-Graphᵉ Gᵉ wᵉ vᵉ)

  is-vertex-on-first-or-second-segment-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) →
    (uᵉ vᵉ : vertex-on-walk-Undirected-Graphᵉ Gᵉ wᵉ) →
    ( is-vertex-on-first-segment-walk-Undirected-Graphᵉ wᵉ uᵉ
      ( vertex-vertex-on-walk-Undirected-Graphᵉ Gᵉ wᵉ vᵉ)) +ᵉ
    ( is-vertex-on-second-segment-walk-Undirected-Graphᵉ wᵉ uᵉ
      ( vertex-vertex-on-walk-Undirected-Graphᵉ Gᵉ wᵉ vᵉ))
  is-vertex-on-first-or-second-segment-walk-Undirected-Graphᵉ
    refl-walk-Undirected-Graphᵉ (uᵉ ,ᵉ reflᵉ) (.uᵉ ,ᵉ reflᵉ) =
    inlᵉ reflᵉ
  is-vertex-on-first-or-second-segment-walk-Undirected-Graphᵉ
    ( cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ) (uᵉ ,ᵉ inlᵉ Hᵉ) (vᵉ ,ᵉ inlᵉ Kᵉ) =
    map-coproductᵉ idᵉ
      ( is-vertex-on-walk-cons-walk-Undirected-Graphᵉ Gᵉ pᵉ eᵉ
        ( second-segment-walk-Undirected-Graphᵉ Gᵉ wᵉ (uᵉ ,ᵉ Hᵉ)))
      ( is-vertex-on-first-or-second-segment-walk-Undirected-Graphᵉ wᵉ
        ( pairᵉ uᵉ Hᵉ)
        ( pairᵉ vᵉ Kᵉ))
  is-vertex-on-first-or-second-segment-walk-Undirected-Graphᵉ
    ( cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ)
    ( uᵉ ,ᵉ inlᵉ Hᵉ)
    ( .(other-element-unordered-pairᵉ pᵉ _) ,ᵉ inrᵉ reflᵉ) =
    inrᵉ (inrᵉ reflᵉ)
  is-vertex-on-first-or-second-segment-walk-Undirected-Graphᵉ
    ( cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ)
    ( .(other-element-unordered-pairᵉ pᵉ _) ,ᵉ inrᵉ reflᵉ)
    ( vᵉ ,ᵉ inlᵉ xᵉ) =
    inlᵉ (is-vertex-on-walk-cons-walk-Undirected-Graphᵉ Gᵉ pᵉ eᵉ wᵉ xᵉ)
  is-vertex-on-first-or-second-segment-walk-Undirected-Graphᵉ
    ( cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ)
    ( .(other-element-unordered-pairᵉ pᵉ _) ,ᵉ inrᵉ reflᵉ)
    ( .(other-element-unordered-pairᵉ pᵉ _) ,ᵉ inrᵉ reflᵉ) =
    inlᵉ (inrᵉ reflᵉ)
```

### For any decomposition of a walk `w` into `w1` followed by `w2`, any vertex on `w1` is a vertex on `w`

```agda
is-vertex-on-walk-is-vertex-on-first-segment-walk-Undirected-Graphᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) {xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ}
  (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) (vᵉ : vertex-on-walk-Undirected-Graphᵉ Gᵉ wᵉ)
  (uᵉ : vertex-Undirected-Graphᵉ Gᵉ) →
  is-vertex-on-first-segment-walk-Undirected-Graphᵉ Gᵉ wᵉ vᵉ uᵉ →
  is-vertex-on-walk-Undirected-Graphᵉ Gᵉ wᵉ uᵉ
is-vertex-on-walk-is-vertex-on-first-segment-walk-Undirected-Graphᵉ Gᵉ
  refl-walk-Undirected-Graphᵉ
  (vᵉ ,ᵉ reflᵉ)
  .(vertex-vertex-on-walk-Undirected-Graphᵉ Gᵉ refl-walk-Undirected-Graphᵉ
    (vᵉ ,ᵉ reflᵉ))
  reflᵉ =
  reflᵉ
is-vertex-on-walk-is-vertex-on-first-segment-walk-Undirected-Graphᵉ Gᵉ
  ( cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ) (vᵉ ,ᵉ inlᵉ Kᵉ) uᵉ Hᵉ =
  inlᵉ
    ( is-vertex-on-walk-is-vertex-on-first-segment-walk-Undirected-Graphᵉ
      Gᵉ wᵉ (pairᵉ vᵉ Kᵉ) uᵉ Hᵉ)
is-vertex-on-walk-is-vertex-on-first-segment-walk-Undirected-Graphᵉ Gᵉ
  ( cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ)
  (.(other-element-unordered-pairᵉ pᵉ _) ,ᵉ inrᵉ reflᵉ) uᵉ Hᵉ =
  Hᵉ
```

### For any decomposition of a walk `w` into `w1` followed by `w2`, any vertex on `w2` is a vertex on `w`

```agda
is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graphᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) {xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ}
  (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) (vᵉ : vertex-on-walk-Undirected-Graphᵉ Gᵉ wᵉ)
  (uᵉ : vertex-Undirected-Graphᵉ Gᵉ) →
  is-vertex-on-second-segment-walk-Undirected-Graphᵉ Gᵉ wᵉ vᵉ uᵉ →
  is-vertex-on-walk-Undirected-Graphᵉ Gᵉ wᵉ uᵉ
is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graphᵉ
  Gᵉ refl-walk-Undirected-Graphᵉ (vᵉ ,ᵉ reflᵉ) .vᵉ reflᵉ = reflᵉ
is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graphᵉ
  Gᵉ (cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ) (vᵉ ,ᵉ inlᵉ Kᵉ) uᵉ (inlᵉ Hᵉ) =
  is-vertex-on-walk-cons-walk-Undirected-Graphᵉ Gᵉ pᵉ eᵉ wᵉ
    ( is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graphᵉ
      Gᵉ wᵉ (pairᵉ vᵉ Kᵉ) uᵉ Hᵉ)
is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graphᵉ Gᵉ
  ( cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ)
  ( vᵉ ,ᵉ inlᵉ Kᵉ)
  .(other-element-unordered-pairᵉ pᵉ _)
  ( inrᵉ reflᵉ) =
  inrᵉ reflᵉ
is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graphᵉ Gᵉ
  ( cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ)
  ( .(other-element-unordered-pairᵉ pᵉ _) ,ᵉ inrᵉ reflᵉ)
  .(other-element-unordered-pairᵉ pᵉ _)
  ( reflᵉ) =
  inrᵉ reflᵉ
```

### Constant walks are identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) {xᵉ : vertex-Undirected-Graphᵉ Gᵉ}
  where

  is-constant-walk-Undirected-Graph-Propᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} →
    walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ → Propᵉ lzero
  is-constant-walk-Undirected-Graph-Propᵉ wᵉ =
    is-zero-ℕ-Propᵉ (length-walk-Undirected-Graphᵉ Gᵉ wᵉ)

  is-constant-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} → walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ → UUᵉ lzero
  is-constant-walk-Undirected-Graphᵉ wᵉ =
    type-Propᵉ (is-constant-walk-Undirected-Graph-Propᵉ wᵉ)

  constant-walk-Undirected-Graphᵉ :
    (yᵉ : vertex-Undirected-Graphᵉ Gᵉ) → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  constant-walk-Undirected-Graphᵉ yᵉ =
    Σᵉ (walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) is-constant-walk-Undirected-Graphᵉ

  is-decidable-is-constant-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (wᵉ : walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) →
    is-decidableᵉ (is-constant-walk-Undirected-Graphᵉ wᵉ)
  is-decidable-is-constant-walk-Undirected-Graphᵉ wᵉ =
    is-decidable-is-zero-ℕᵉ (length-walk-Undirected-Graphᵉ Gᵉ wᵉ)

  refl-constant-walk-Undirected-Graphᵉ :
    constant-walk-Undirected-Graphᵉ xᵉ
  pr1ᵉ refl-constant-walk-Undirected-Graphᵉ = refl-walk-Undirected-Graphᵉ
  pr2ᵉ refl-constant-walk-Undirected-Graphᵉ = reflᵉ

  is-torsorial-constant-walk-Undirected-Graphᵉ :
    is-torsorialᵉ constant-walk-Undirected-Graphᵉ
  pr1ᵉ (pr1ᵉ is-torsorial-constant-walk-Undirected-Graphᵉ) = xᵉ
  pr2ᵉ (pr1ᵉ is-torsorial-constant-walk-Undirected-Graphᵉ) =
    refl-constant-walk-Undirected-Graphᵉ
  pr2ᵉ is-torsorial-constant-walk-Undirected-Graphᵉ
    (vᵉ ,ᵉ refl-walk-Undirected-Graphᵉ ,ᵉ reflᵉ) =
    reflᵉ
  pr2ᵉ is-torsorial-constant-walk-Undirected-Graphᵉ
    (.(other-element-unordered-pairᵉ pᵉ _) ,ᵉ
      cons-walk-Undirected-Graphᵉ pᵉ eᵉ wᵉ ,ᵉ ())

  constant-walk-eq-Undirected-Graphᵉ :
    (yᵉ : vertex-Undirected-Graphᵉ Gᵉ) → xᵉ ＝ᵉ yᵉ → constant-walk-Undirected-Graphᵉ yᵉ
  constant-walk-eq-Undirected-Graphᵉ yᵉ reflᵉ = refl-constant-walk-Undirected-Graphᵉ

  is-equiv-constant-walk-eq-Undirected-Graphᵉ :
    (yᵉ : vertex-Undirected-Graphᵉ Gᵉ) →
    is-equivᵉ (constant-walk-eq-Undirected-Graphᵉ yᵉ)
  is-equiv-constant-walk-eq-Undirected-Graphᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-constant-walk-Undirected-Graphᵉ)
      ( constant-walk-eq-Undirected-Graphᵉ)

  equiv-constant-walk-eq-Undirected-Graphᵉ :
    (yᵉ : vertex-Undirected-Graphᵉ Gᵉ) →
    (xᵉ ＝ᵉ yᵉ) ≃ᵉ constant-walk-Undirected-Graphᵉ yᵉ
  pr1ᵉ (equiv-constant-walk-eq-Undirected-Graphᵉ yᵉ) =
    constant-walk-eq-Undirected-Graphᵉ yᵉ
  pr2ᵉ (equiv-constant-walk-eq-Undirected-Graphᵉ yᵉ) =
    is-equiv-constant-walk-eq-Undirected-Graphᵉ yᵉ

  eq-constant-walk-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} → constant-walk-Undirected-Graphᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  eq-constant-walk-Undirected-Graphᵉ {yᵉ} =
    map-inv-is-equivᵉ (is-equiv-constant-walk-eq-Undirected-Graphᵉ yᵉ)
```

## External links

-ᵉ [Path](https://www.wikidata.org/entity/Q917421ᵉ) onᵉ Wikidataᵉ
-ᵉ [Pathᵉ (graphᵉ theory)](<https://en.wikipedia.org/wiki/Path_(graph_theory)>ᵉ) atᵉ
  Wikipediaᵉ
-ᵉ [Walk](https://mathworld.wolfram.com/Walk.htmlᵉ) atᵉ Wolframᵉ Mathworldᵉ