# Wide displayed large reflexive graphs

```agda
module graph-theory.wide-displayed-large-reflexive-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.large-reflexive-graphsᵉ
open import graph-theory.reflexive-graphsᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "wideᵉ displayedᵉ largeᵉ reflexiveᵉ graph"ᵉ Agda=Wide-Displayed-Large-Reflexive-Graphᵉ}}
isᵉ aᵉ
[displayedᵉ largeᵉ reflexiveᵉ graph](graph-theory.displayed-large-reflexive-graphs.mdᵉ)
overᵉ aᵉ baseᵉ [largeᵉ reflexiveᵉ graph](graph-theory.large-reflexive-graphs.mdᵉ) `G`ᵉ
thatᵉ doesᵉ notᵉ addᵉ structureᵉ onᵉ theᵉ vertices,ᵉ butᵉ onlyᵉ theᵉ edges.ᵉ

**Terminology.**ᵉ Theᵉ useᵉ ofᵉ theᵉ termᵉ "wide"ᵉ hereᵉ isᵉ motivatedᵉ byᵉ theᵉ ideaᵉ thatᵉ aᵉ
"wideᵉ displayedᵉ graph"ᵉ shouldᵉ generalizeᵉ "wideᵉ subgraphs",ᵉ i.e.,ᵉ aᵉ subgraphᵉ
whichᵉ containsᵉ allᵉ vertices,ᵉ in theᵉ sameᵉ wayᵉ "displayedᵉ graphs"ᵉ generalizeᵉ
"subgraphs".ᵉ

## Definitions

### Wide displayed large reflexive graphs

```agda
record
  Wide-Displayed-Large-Reflexive-Graphᵉ
  {α'ᵉ : Level → Level} {β'ᵉ : Level → Level → Level}
  (βᵉ : Level → Level → Level)
  (Gᵉ : Large-Reflexive-Graphᵉ α'ᵉ β'ᵉ) : UUωᵉ
  where

  field

    edge-Wide-Displayed-Large-Reflexive-Graphᵉ :
      {l1ᵉ l2ᵉ : Level}
      {xᵉ : vertex-Large-Reflexive-Graphᵉ Gᵉ l1ᵉ}
      {yᵉ : vertex-Large-Reflexive-Graphᵉ Gᵉ l2ᵉ}
      (fᵉ : edge-Large-Reflexive-Graphᵉ Gᵉ xᵉ yᵉ) →
      UUᵉ (βᵉ l1ᵉ l2ᵉ)

    refl-Wide-Displayed-Large-Reflexive-Graphᵉ :
      {lᵉ : Level}
      (xᵉ : vertex-Large-Reflexive-Graphᵉ Gᵉ lᵉ) →
      edge-Wide-Displayed-Large-Reflexive-Graphᵉ (refl-Large-Reflexive-Graphᵉ Gᵉ xᵉ)

open Wide-Displayed-Large-Reflexive-Graphᵉ public
```

### The total large reflexive graph of a displayed large reflexive graph

```agda
module _
  {α1ᵉ : Level → Level} {β1ᵉ β2ᵉ : Level → Level → Level}
  {Gᵉ : Large-Reflexive-Graphᵉ α1ᵉ β1ᵉ}
  (Hᵉ : Wide-Displayed-Large-Reflexive-Graphᵉ β2ᵉ Gᵉ)
  where

  vertex-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ :
    (lᵉ : Level) → UUᵉ (α1ᵉ lᵉ)
  vertex-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ lᵉ =
    vertex-Large-Reflexive-Graphᵉ Gᵉ lᵉ

  edge-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ :
    {l1ᵉ l2ᵉ : Level} →
    vertex-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ l1ᵉ →
    vertex-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ l2ᵉ →
    UUᵉ (β1ᵉ l1ᵉ l2ᵉ ⊔ β2ᵉ l1ᵉ l2ᵉ)
  edge-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ xᵉ yᵉ =
    Σᵉ ( edge-Large-Reflexive-Graphᵉ Gᵉ xᵉ yᵉ)
      ( edge-Wide-Displayed-Large-Reflexive-Graphᵉ Hᵉ)

  refl-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ :
    {lᵉ : Level}
    (xᵉ :
      vertex-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ
        lᵉ) →
    edge-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ xᵉ xᵉ
  refl-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ xᵉ =
    ( refl-Large-Reflexive-Graphᵉ Gᵉ xᵉ ,ᵉ
      refl-Wide-Displayed-Large-Reflexive-Graphᵉ Hᵉ xᵉ)

  total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ :
    Large-Reflexive-Graphᵉ α1ᵉ (λ l1ᵉ l2ᵉ → β1ᵉ l1ᵉ l2ᵉ ⊔ β2ᵉ l1ᵉ l2ᵉ)
  vertex-Large-Reflexive-Graphᵉ
    total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ =
      vertex-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ
  edge-Large-Reflexive-Graphᵉ
    total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ =
    edge-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ
  refl-Large-Reflexive-Graphᵉ
    total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ =
    refl-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ
```

### The fiber reflexive graph of a wide displayed large reflexive graph over a vertex

```agda
module _
  {α1ᵉ : Level → Level} {β1ᵉ β2ᵉ : Level → Level → Level}
  {Gᵉ : Large-Reflexive-Graphᵉ α1ᵉ β1ᵉ}
  (Hᵉ : Wide-Displayed-Large-Reflexive-Graphᵉ β2ᵉ Gᵉ)
  {lᵉ : Level} (xᵉ : vertex-Large-Reflexive-Graphᵉ Gᵉ lᵉ)
  where

  fiber-vertex-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ :
    Reflexive-Graphᵉ lzero (β2ᵉ lᵉ lᵉ)
  pr1ᵉ fiber-vertex-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ = unitᵉ
  pr1ᵉ (pr2ᵉ fiber-vertex-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ)
    _ _ =
    edge-Wide-Displayed-Large-Reflexive-Graphᵉ Hᵉ (refl-Large-Reflexive-Graphᵉ Gᵉ xᵉ)
  pr2ᵉ (pr2ᵉ fiber-vertex-reflexive-graph-Wide-Displayed-Large-Reflexive-Graphᵉ)
    _ =
    refl-Wide-Displayed-Large-Reflexive-Graphᵉ Hᵉ xᵉ
```