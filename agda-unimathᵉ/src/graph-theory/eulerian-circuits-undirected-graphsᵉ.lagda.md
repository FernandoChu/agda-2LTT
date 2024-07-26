# Eulerian circuits in undirected graphs

```agda
module graph-theory.eulerian-circuits-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.morphisms-undirected-graphsᵉ
open import graph-theory.polygonsᵉ
open import graph-theory.undirected-graphsᵉ
```

</details>

## Idea

Anᵉ **Eulerianᵉ circuit**ᵉ in anᵉ
[undirectedᵉ graph](graph-theory.undirected-graphs.mdᵉ) `G`ᵉ consistsᵉ ofᵉ aᵉ
[circuit](graph-theory.circuits-undirected-graphs.mdᵉ) `T`ᵉ in `G`ᵉ suchᵉ thatᵉ everyᵉ
edgeᵉ in `G`ᵉ isᵉ in theᵉ imageᵉ ofᵉ `T`.ᵉ Inᵉ otherᵉ words,ᵉ anᵉ Eulerianᵉ circuitᵉ `T`ᵉ
consistsᵉ ofᵉ [`k`-gon](graph-theory.polygons.mdᵉ) `H`ᵉ equippedᵉ with aᵉ
[graphᵉ homomorphism](graph-theory.morphisms-undirected-graphs.mdᵉ) `fᵉ : Hᵉ → G`ᵉ
thatᵉ inducesᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ)

```text
  Σᵉ (unordered-pair-vertices-Polygonᵉ kᵉ Hᵉ) (edge-Polygonᵉ kᵉ Hᵉ) ≃ᵉ
  Σᵉ (unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) (edge-Undirected-Graphᵉ Gᵉ)
```

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  where

  eulerian-circuit-Undirected-Graphᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  eulerian-circuit-Undirected-Graphᵉ =
    Σᵉ ( ℕᵉ)
      ( λ kᵉ →
        Σᵉ ( Polygonᵉ kᵉ)
          ( λ Hᵉ →
            Σᵉ ( hom-Undirected-Graphᵉ (undirected-graph-Polygonᵉ kᵉ Hᵉ) Gᵉ)
              ( λ fᵉ →
                is-equivᵉ
                  ( totᵉ
                    ( edge-hom-Undirected-Graphᵉ
                      ( undirected-graph-Polygonᵉ kᵉ Hᵉ)
                      ( Gᵉ)
                      ( fᵉ))))))
```

## External links

-ᵉ [Eulerianᵉ circuit](https://d3gt.com/unit.html?eulerian-circuitᵉ) onᵉ D3ᵉ Graphᵉ
  theoryᵉ
-ᵉ [Eulerianᵉ cycle](https://www.wikidata.org/entity/Q11691793ᵉ) onᵉ Wikidataᵉ
-ᵉ [Eulerianᵉ path](https://en.wikipedia.org/wiki/Eulerian_pathᵉ) onᵉ Wikipediaᵉ
-ᵉ [Eulerianᵉ cycle](https://mathworld.wolfram.com/EulerianCycle.htmlᵉ) onᵉ Wolframᵉ
  mathworldᵉ