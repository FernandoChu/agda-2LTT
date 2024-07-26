# Rooted quasitrees

```agda
module trees.rooted-quasitreesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.trails-undirected-graphsᵉ
open import graph-theory.undirected-graphsᵉ
```

</details>

## Idea

Aᵉ **rootedᵉ quasitree**ᵉ isᵉ anᵉ undirectedᵉ graphᵉ `G`ᵉ equippedᵉ with aᵉ markedᵉ
vertex`r`,ᵉ to beᵉ calledᵉ theᵉ root,ᵉ suchᵉ thatᵉ forᵉ everyᵉ vertexᵉ `x`ᵉ thereᵉ isᵉ aᵉ
uniqueᵉ trailᵉ fromᵉ `r`ᵉ to `x`.ᵉ

## Definition

```agda
is-rooted-quasitree-Undirected-Graphᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) →
  vertex-Undirected-Graphᵉ Gᵉ → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
is-rooted-quasitree-Undirected-Graphᵉ Gᵉ rᵉ =
  (xᵉ : vertex-Undirected-Graphᵉ Gᵉ) → is-contrᵉ (trail-Undirected-Graphᵉ Gᵉ rᵉ xᵉ)

Rooted-Quasitreeᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Rooted-Quasitreeᵉ l1ᵉ l2ᵉ =
  Σᵉ ( Undirected-Graphᵉ l1ᵉ l2ᵉ)
    ( λ Gᵉ →
      Σᵉ ( vertex-Undirected-Graphᵉ Gᵉ)
        ( is-rooted-quasitree-Undirected-Graphᵉ Gᵉ))
```