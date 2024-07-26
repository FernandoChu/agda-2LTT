# Large higher directed graphs

```agda
module graph-theory.large-higher-directed-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ
open import graph-theory.higher-directed-graphsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "largeᵉ directedᵉ $n$-graph"ᵉ Agda=Large-Higher-Directed-Graphᵉ}} isᵉ
definedᵉ inductivelyᵉ:

-ᵉ Aᵉ largeᵉ directedᵉ $0$-graphᵉ isᵉ aᵉ largeᵉ collectionᵉ ofᵉ vertices.ᵉ
-ᵉ Aᵉ largeᵉ directedᵉ $n+1$-graphᵉ isᵉ aᵉ largeᵉ collectionᵉ ofᵉ verticesᵉ togetherᵉ with aᵉ
  [largeᵉ binaryᵉ relation](foundation.large-binary-relations.mdᵉ) `E`ᵉ onᵉ theᵉ
  vertices,ᵉ suchᵉ thatᵉ `Eᵉ uᵉ v`ᵉ isᵉ aᵉ
  [(smallᵉ) directedᵉ $n$-graph](graph-theory.higher-directed-graphs.mdᵉ) forᵉ allᵉ
  `u`ᵉ andᵉ `v`.ᵉ

## Definitions

### The structure of a large higher directed graph on a large collection of vertices

```agda
data
  is-large-higher-directed-graphᵉ
  {αᵉ : Level → Level}
  (βᵉ γᵉ : Level → Level → Level)
  (Vᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)) :
  (nᵉ : ℕᵉ) → UUωᵉ
  where

  cons-zero-is-large-higher-directed-graphᵉ :
    is-large-higher-directed-graphᵉ βᵉ γᵉ Vᵉ 0

  cons-base-is-large-higher-directed-graphᵉ :
    Large-Relationᵉ βᵉ Vᵉ → is-large-higher-directed-graphᵉ βᵉ γᵉ Vᵉ 1

  cons-ind-is-large-higher-directed-graphᵉ :
    (nᵉ : ℕᵉ) →
    (Eᵉ : Large-Relationᵉ βᵉ Vᵉ) →
    ( {l1ᵉ l2ᵉ : Level} (uᵉ : Vᵉ l1ᵉ) (vᵉ : Vᵉ l2ᵉ) →
      is-higher-directed-graph-succᵉ (γᵉ l1ᵉ l2ᵉ) nᵉ (Eᵉ uᵉ vᵉ)) →
    is-large-higher-directed-graphᵉ βᵉ γᵉ Vᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ))

edge-is-large-higher-directed-graphᵉ :
  {αᵉ : Level → Level}
  (βᵉ γᵉ : Level → Level → Level)
  (nᵉ : ℕᵉ)
  (Vᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)) →
  is-large-higher-directed-graphᵉ βᵉ γᵉ Vᵉ (succ-ℕᵉ nᵉ) →
  Large-Relationᵉ βᵉ Vᵉ
edge-is-large-higher-directed-graphᵉ
  βᵉ γᵉ .0ᵉ Vᵉ (cons-base-is-large-higher-directed-graphᵉ Eᵉ) =
  Eᵉ
edge-is-large-higher-directed-graphᵉ
  βᵉ γᵉ .(succ-ℕᵉ nᵉ) Vᵉ (cons-ind-is-large-higher-directed-graphᵉ nᵉ Eᵉ _) =
  Eᵉ
```

### The large type of large higher directed graphs

```agda
record
  Large-Higher-Directed-Graphᵉ
    (αᵉ : Level → Level) (βᵉ γᵉ : Level → Level → Level) (nᵉ : ℕᵉ) : UUωᵉ
  where

  field
    vertex-Large-Higher-Directed-Graphᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)

    is-higher-directed-graph-Large-Higher-Directed-Graphᵉ :
      is-large-higher-directed-graphᵉ βᵉ γᵉ vertex-Large-Higher-Directed-Graphᵉ nᵉ

open Large-Higher-Directed-Graphᵉ public

edge-Large-Higher-Directed-Graphᵉ :
  {αᵉ : Level → Level} {βᵉ γᵉ : Level → Level → Level} {nᵉ : ℕᵉ}
  (Gᵉ : Large-Higher-Directed-Graphᵉ αᵉ βᵉ γᵉ (succ-ℕᵉ nᵉ)) →
  Large-Relationᵉ βᵉ (vertex-Large-Higher-Directed-Graphᵉ Gᵉ)
edge-Large-Higher-Directed-Graphᵉ {αᵉ} {βᵉ} {γᵉ} {nᵉ} Gᵉ =
  edge-is-large-higher-directed-graphᵉ βᵉ γᵉ nᵉ
    ( vertex-Large-Higher-Directed-Graphᵉ Gᵉ)
    ( is-higher-directed-graph-Large-Higher-Directed-Graphᵉ Gᵉ)
```