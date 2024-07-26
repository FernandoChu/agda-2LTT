# Mere equivalences of undirected graphs

```agda
module graph-theory.mere-equivalences-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.equivalences-undirected-graphsᵉ
open import graph-theory.undirected-graphsᵉ
```

</details>

## Idea

Twoᵉ [undirectedᵉ graphs](graph-theory.undirected-graphs.mdᵉ) areᵉ saidᵉ to beᵉ
**merelyᵉ equivalent**ᵉ ifᵉ thereᵉ merelyᵉ
[exists](foundation.existential-quantification.mdᵉ) anᵉ
[equivalenceᵉ ofᵉ undirectedᵉ graphs](graph-theory.equivalences-undirected-graphs.mdᵉ)
betweenᵉ them.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Undirected-Graphᵉ l3ᵉ l4ᵉ)
  where

  mere-equiv-Undirected-Graph-Propᵉ : Propᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  mere-equiv-Undirected-Graph-Propᵉ = trunc-Propᵉ (equiv-Undirected-Graphᵉ Gᵉ Hᵉ)

  mere-equiv-Undirected-Graphᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  mere-equiv-Undirected-Graphᵉ = type-Propᵉ mere-equiv-Undirected-Graph-Propᵉ

  is-prop-mere-equiv-Undirected-Graphᵉ : is-propᵉ mere-equiv-Undirected-Graphᵉ
  is-prop-mere-equiv-Undirected-Graphᵉ =
    is-prop-type-Propᵉ mere-equiv-Undirected-Graph-Propᵉ
```

## Properties

### The mere equivalence relation on undirected graphs is reflexive

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  where

  refl-mere-equiv-Undirected-Graphᵉ : mere-equiv-Undirected-Graphᵉ Gᵉ Gᵉ
  refl-mere-equiv-Undirected-Graphᵉ =
    unit-trunc-Propᵉ (id-equiv-Undirected-Graphᵉ Gᵉ)
```

## External links

-ᵉ [Graphᵉ isomoprhism](https://www.wikidata.org/entity/Q303100ᵉ) atᵉ Wikidataᵉ
-ᵉ [Graphᵉ isomorphism](https://en.wikipedia.org/wiki/Graph_isomorphismᵉ) atᵉ
  Wikipediaᵉ
-ᵉ [Graphᵉ isomorphism](https://mathworld.wolfram.com/GraphIsomorphism.htmlᵉ) atᵉ
  Wolframᵉ Mathworldᵉ
-ᵉ [Isomorphism](https://ncatlab.org/nlab/show/isomorphismᵉ) atᵉ $n$Labᵉ