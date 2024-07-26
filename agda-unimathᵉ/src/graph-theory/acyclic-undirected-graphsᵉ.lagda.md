# Acyclic undirected graphs

```agda
module graph-theory.acyclic-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import graph-theory.geometric-realizations-undirected-graphsᵉ
open import graph-theory.reflecting-maps-undirected-graphsᵉ
open import graph-theory.undirected-graphsᵉ
```

</details>

## Idea

Anᵉ
{{#conceptᵉ "acyclicᵉ undirectedᵉ graph"ᵉ WDID=Q3115453ᵉ WD="acyclicᵉ graph"ᵉ Agda=is-acyclic-Undirected-Graphᵉ}}
isᵉ anᵉ [undirectedᵉ graph](graph-theory.undirected-graphs.mdᵉ) ofᵉ whichᵉ theᵉ
[geometricᵉ realization](graph-theory.geometric-realizations-undirected-graphs.mdᵉ)
isᵉ [contractible](foundation-core.contractible-types.md).ᵉ

Theᵉ notionᵉ ofᵉ acyclicᵉ graphsᵉ isᵉ aᵉ generalizationᵉ ofᵉ theᵉ notionᵉ ofᵉ
[undirectedᵉ trees](trees.undirected-trees.md).ᵉ Noteᵉ thatᵉ in thisᵉ library,ᵉ anᵉ
undirectedᵉ treeᵉ isᵉ anᵉ undirectedᵉ graphᵉ in whichᵉ theᵉ typeᵉ ofᵉ
[trails](graph-theory.trails-undirected-graphs.mdᵉ) betweenᵉ anyᵉ twoᵉ pointsᵉ isᵉ
contractible.ᵉ Theᵉ typeᵉ ofᵉ nodesᵉ ofᵉ suchᵉ undirectedᵉ treesᵉ consequentlyᵉ hasᵉ
[decidableᵉ equality](foundation.decidable-equality.md).ᵉ Onᵉ theᵉ otherᵉ hand,ᵉ thereᵉ
areᵉ acyclicᵉ undirectedᵉ graphsᵉ thatᵉ areᵉ notᵉ undirectedᵉ treesᵉ in thisᵉ sense.ᵉ Oneᵉ
wayᵉ to obtainᵉ themᵉ isᵉ viaᵉ
[acyclicᵉ types](synthetic-homotopy-theory.acyclic-types.md),ᵉ whichᵉ areᵉ typesᵉ ofᵉ
whichᵉ theᵉ [suspension](synthetic-homotopy-theory.suspensions-of-types.mdᵉ) isᵉ
contractible.ᵉ Theᵉ undirectedᵉ suspensionᵉ diagramᵉ ofᵉ suchᵉ typesᵉ isᵉ anᵉ acyclicᵉ
graph.ᵉ Furthermore,ᵉ anyᵉ [directedᵉ tree](trees.directed-trees.mdᵉ) inducesᵉ anᵉ
acyclicᵉ undirectedᵉ graphᵉ byᵉ forgettingᵉ theᵉ directionsᵉ ofᵉ theᵉ edges.ᵉ

## Definition

### Acyclic undirected graphs

Theᵉ followingᵉ isᵉ aᵉ preliminaryᵉ definitionᵉ thatᵉ requiresᵉ usᵉ to parametrizeᵉ overᵉ
anᵉ extraᵉ universeᵉ level.ᵉ Thisᵉ willᵉ notᵉ beᵉ necessaryᵉ anymoreᵉ ifᵉ weᵉ constructedᵉ aᵉ
geometricᵉ realizationᵉ ofᵉ everyᵉ undirectedᵉ graph.ᵉ Onceᵉ weᵉ didᵉ that,ᵉ weᵉ wouldᵉ
simplyᵉ sayᵉ thatᵉ theᵉ geometricᵉ realizationᵉ ofᵉ `G`ᵉ isᵉ contractible.ᵉ

```agda
is-acyclic-Undirected-Graphᵉ :
  {l1ᵉ l2ᵉ : Level} (lᵉ : Level) (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ)
is-acyclic-Undirected-Graphᵉ lᵉ Gᵉ =
  is-geometric-realization-reflecting-map-Undirected-Graphᵉ lᵉ Gᵉ
    ( terminal-reflecting-map-Undirected-Graphᵉ Gᵉ)
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}

## External links

-ᵉ [Trees](https://ncatlab.org/nlab/show/treeᵉ) atᵉ $n$Labᵉ
-ᵉ [Forests](<https://en.wikipedia.org/wiki/Tree_(graph_theory)#Forest>ᵉ) atᵉ
  Wikipediaᵉ
-ᵉ [Acyclicᵉ graphs](https://mathworld.wolfram.com/AcyclicGraph.htmlᵉ) atᵉ Wolframᵉ
  Mathworld.ᵉ