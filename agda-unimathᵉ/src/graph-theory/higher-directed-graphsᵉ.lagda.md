# Higher directed graphs

```agda
module graph-theory.higher-directed-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.binary-relationsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "directedᵉ $n$-graph"ᵉ Agda=Higher-Directed-Graphᵉ}} consistsᵉ ofᵉ aᵉ
typeᵉ ofᵉ verticesᵉ equippedᵉ with aᵉ binaryᵉ familyᵉ ofᵉ directedᵉ `n-1`-graphsᵉ onᵉ itsᵉ
edges,ᵉ where aᵉ directedᵉ `0`-graphᵉ consistsᵉ ofᵉ justᵉ aᵉ typeᵉ ofᵉ vertices.ᵉ

## Definition

### The structure of a higher directed graph on a type of vertices

```agda
is-higher-directed-graph-succᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (nᵉ : ℕᵉ) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
is-higher-directed-graph-succᵉ l2ᵉ zero-ℕᵉ Vᵉ =
  Relationᵉ l2ᵉ Vᵉ
is-higher-directed-graph-succᵉ l2ᵉ (succ-ℕᵉ nᵉ) Vᵉ =
  Σᵉ ( is-higher-directed-graph-succᵉ l2ᵉ 0 Vᵉ)
    ( λ Eᵉ → (uᵉ vᵉ : Vᵉ) → is-higher-directed-graph-succᵉ l2ᵉ nᵉ (Eᵉ uᵉ vᵉ))

edge-is-higher-directed-graph-succᵉ :
  {l1ᵉ l2ᵉ : Level} {nᵉ : ℕᵉ} (Vᵉ : UUᵉ l1ᵉ) →
  is-higher-directed-graph-succᵉ l2ᵉ nᵉ Vᵉ → Relationᵉ l2ᵉ Vᵉ
edge-is-higher-directed-graph-succᵉ {nᵉ = zero-ℕᵉ} Vᵉ Eᵉ = Eᵉ
edge-is-higher-directed-graph-succᵉ {nᵉ = succ-ℕᵉ nᵉ} Vᵉ (Eᵉ ,ᵉ _) = Eᵉ
```

### The type of higher directed graphs

```agda
Higher-Directed-Graphᵉ : (lᵉ : Level) (nᵉ : ℕᵉ) → UUᵉ (lsuc lᵉ)
Higher-Directed-Graphᵉ lᵉ 0 = UUᵉ lᵉ
Higher-Directed-Graphᵉ lᵉ (succ-ℕᵉ nᵉ) =
  Σᵉ (UUᵉ lᵉ) (λ Vᵉ → Vᵉ → Vᵉ → Higher-Directed-Graphᵉ lᵉ nᵉ)

vertex-Higher-Directed-Graphᵉ :
  {nᵉ : ℕᵉ} {lᵉ : Level} → Higher-Directed-Graphᵉ lᵉ nᵉ → UUᵉ lᵉ
vertex-Higher-Directed-Graphᵉ {0ᵉ} Gᵉ = Gᵉ
vertex-Higher-Directed-Graphᵉ {succ-ℕᵉ nᵉ} = pr1ᵉ

edge-Higher-Directed-Graphᵉ :
  {nᵉ : ℕᵉ} {lᵉ : Level} (Gᵉ : Higher-Directed-Graphᵉ lᵉ (succ-ℕᵉ nᵉ)) →
  vertex-Higher-Directed-Graphᵉ Gᵉ → vertex-Higher-Directed-Graphᵉ Gᵉ → UUᵉ lᵉ
edge-Higher-Directed-Graphᵉ {0ᵉ} = pr2ᵉ
edge-Higher-Directed-Graphᵉ {succ-ℕᵉ nᵉ} Gᵉ xᵉ yᵉ = pr1ᵉ (pr2ᵉ Gᵉ xᵉ yᵉ)
```

## Properties

### Directed 1-graphs are just directed graphs

```agda
eq-Directed-Graph-Higher-Directed-Graph-1ᵉ :
  {lᵉ : Level} → Higher-Directed-Graphᵉ lᵉ 1 ＝ᵉ Directed-Graphᵉ lᵉ lᵉ
eq-Directed-Graph-Higher-Directed-Graph-1ᵉ = reflᵉ
```