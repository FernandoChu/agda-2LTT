# Displayed large reflexive graphs

```agda
module graph-theory.displayed-large-reflexive-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.large-reflexive-graphsᵉ
open import graph-theory.reflexive-graphsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "displayedᵉ largeᵉ reflexiveᵉ graph"ᵉ}} `H`ᵉ aᵉ overᵉ aᵉ baseᵉ
[largeᵉ reflexiveᵉ graph](graph-theory.large-reflexive-graphs.mdᵉ) `G`ᵉ isᵉ theᵉ
[structure](foundation.structure.mdᵉ) ofᵉ aᵉ dependentᵉ largeᵉ reflexiveᵉ graphᵉ overᵉ
`G`.ᵉ Itᵉ consistsᵉ ofᵉ

-ᵉ Aᵉ familyᵉ ofᵉ verticesᵉ overᵉ theᵉ verticesᵉ ofᵉ `G`.ᵉ
-ᵉ Aᵉ familyᵉ ofᵉ dependentᵉ edgesᵉ overᵉ theᵉ edgesᵉ ofᵉ `G`.ᵉ Moreᵉ concretely,ᵉ forᵉ everyᵉ
  edgeᵉ `eᵉ : xᵉ → y`ᵉ in `G`ᵉ andᵉ `x'`ᵉ in `H`ᵉ overᵉ `x`,ᵉ andᵉ `y'`ᵉ overᵉ `x`,ᵉ aᵉ typeᵉ ofᵉ
  _edgesᵉ fromᵉ `x'`ᵉ to `y'`ᵉ overᵉ `e`ᵉ_:

  ```text
    x'ᵉ ·········>ᵉ y'ᵉ   ∋ᵉ Hᵉ

           ↧ᵉ

    xᵉ ---------->ᵉ yᵉ    ∋ᵉ G.ᵉ
           eᵉ
  ```

-ᵉ Aᵉ familyᵉ ofᵉ reflexivityᵉ edgesᵉ `reflᵉ : x'ᵉ → x'`ᵉ overᵉ everyᵉ reflexivityᵉ edgeᵉ in
  `G`.ᵉ

## Definitions

### Displayed large reflexive graphs

```agda
record
  Displayed-Large-Reflexive-Graphᵉ
  {α'ᵉ : Level → Level} {β'ᵉ : Level → Level → Level}
  (αᵉ : Level → Level) (βᵉ : Level → Level → Level)
  (Gᵉ : Large-Reflexive-Graphᵉ α'ᵉ β'ᵉ) : UUωᵉ
  where

  field
    vertex-Displayed-Large-Reflexive-Graphᵉ :
      {lᵉ : Level} (xᵉ : vertex-Large-Reflexive-Graphᵉ Gᵉ lᵉ) → UUᵉ (αᵉ lᵉ)

    edge-Displayed-Large-Reflexive-Graphᵉ :
      {l1ᵉ l2ᵉ : Level}
      {xᵉ : vertex-Large-Reflexive-Graphᵉ Gᵉ l1ᵉ}
      {yᵉ : vertex-Large-Reflexive-Graphᵉ Gᵉ l2ᵉ}
      (fᵉ : edge-Large-Reflexive-Graphᵉ Gᵉ xᵉ yᵉ)
      (x'ᵉ : vertex-Displayed-Large-Reflexive-Graphᵉ xᵉ)
      (y'ᵉ : vertex-Displayed-Large-Reflexive-Graphᵉ yᵉ) →
      UUᵉ (βᵉ l1ᵉ l2ᵉ)

    refl-Displayed-Large-Reflexive-Graphᵉ :
      {lᵉ : Level}
      {xᵉ : vertex-Large-Reflexive-Graphᵉ Gᵉ lᵉ}
      (x'ᵉ : vertex-Displayed-Large-Reflexive-Graphᵉ xᵉ) →
      edge-Displayed-Large-Reflexive-Graphᵉ
        ( refl-Large-Reflexive-Graphᵉ Gᵉ xᵉ)
        ( x'ᵉ)
        ( x'ᵉ)

open Displayed-Large-Reflexive-Graphᵉ public
```

### The total large reflexive graph of a displayed large reflexive graph

```agda
module _
  {α1ᵉ α2ᵉ : Level → Level} {β1ᵉ β2ᵉ : Level → Level → Level}
  {Gᵉ : Large-Reflexive-Graphᵉ α1ᵉ β1ᵉ}
  (Hᵉ : Displayed-Large-Reflexive-Graphᵉ α2ᵉ β2ᵉ Gᵉ)
  where

  vertex-total-large-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ :
    (lᵉ : Level) → UUᵉ (α1ᵉ lᵉ ⊔ α2ᵉ lᵉ)
  vertex-total-large-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ lᵉ =
    Σᵉ ( vertex-Large-Reflexive-Graphᵉ Gᵉ lᵉ)
      ( vertex-Displayed-Large-Reflexive-Graphᵉ Hᵉ)

  edge-total-large-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ :
    {l1ᵉ l2ᵉ : Level} →
    vertex-total-large-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ l1ᵉ →
    vertex-total-large-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ l2ᵉ →
    UUᵉ (β1ᵉ l1ᵉ l2ᵉ ⊔ β2ᵉ l1ᵉ l2ᵉ)
  edge-total-large-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ
    ( xᵉ ,ᵉ x'ᵉ) (yᵉ ,ᵉ y'ᵉ) =
    Σᵉ ( edge-Large-Reflexive-Graphᵉ Gᵉ xᵉ yᵉ)
      ( λ eᵉ → edge-Displayed-Large-Reflexive-Graphᵉ Hᵉ eᵉ x'ᵉ y'ᵉ)

  refl-total-large-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ :
    {lᵉ : Level}
    (xᵉ : vertex-total-large-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ lᵉ) →
    edge-total-large-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ xᵉ xᵉ
  refl-total-large-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ (xᵉ ,ᵉ x'ᵉ) =
    ( refl-Large-Reflexive-Graphᵉ Gᵉ xᵉ ,ᵉ
      refl-Displayed-Large-Reflexive-Graphᵉ Hᵉ x'ᵉ)

  total-large-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ :
    Large-Reflexive-Graphᵉ (λ lᵉ → α1ᵉ lᵉ ⊔ α2ᵉ lᵉ) (λ l1ᵉ l2ᵉ → β1ᵉ l1ᵉ l2ᵉ ⊔ β2ᵉ l1ᵉ l2ᵉ)
  vertex-Large-Reflexive-Graphᵉ
    total-large-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ =
      vertex-total-large-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ
  edge-Large-Reflexive-Graphᵉ
    total-large-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ =
    edge-total-large-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ
  refl-Large-Reflexive-Graphᵉ
    total-large-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ =
    refl-total-large-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ
```

### The fiber reflexive graph of a displayed large reflexive graph over a vertex

```agda
module _
  {α1ᵉ α2ᵉ : Level → Level} {β1ᵉ β2ᵉ : Level → Level → Level}
  {Gᵉ : Large-Reflexive-Graphᵉ α1ᵉ β1ᵉ}
  (Hᵉ : Displayed-Large-Reflexive-Graphᵉ α2ᵉ β2ᵉ Gᵉ)
  {lᵉ : Level} (xᵉ : vertex-Large-Reflexive-Graphᵉ Gᵉ lᵉ)
  where

  fiber-vertex-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ :
    Reflexive-Graphᵉ (α2ᵉ lᵉ) (β2ᵉ lᵉ lᵉ)
  pr1ᵉ fiber-vertex-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ =
    vertex-Displayed-Large-Reflexive-Graphᵉ Hᵉ xᵉ
  pr1ᵉ (pr2ᵉ fiber-vertex-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ) =
    edge-Displayed-Large-Reflexive-Graphᵉ Hᵉ (refl-Large-Reflexive-Graphᵉ Gᵉ xᵉ)
  pr2ᵉ (pr2ᵉ fiber-vertex-reflexive-graph-Displayed-Large-Reflexive-Graphᵉ) =
    refl-Displayed-Large-Reflexive-Graphᵉ Hᵉ
```