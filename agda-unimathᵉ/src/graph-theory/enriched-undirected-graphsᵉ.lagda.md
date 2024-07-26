# Enriched undirected graphs

```agda
module graph-theory.enriched-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.connected-componentsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.neighbors-undirected-graphsᵉ
open import graph-theory.undirected-graphsᵉ

open import higher-group-theory.higher-group-actionsᵉ
open import higher-group-theory.higher-groupsᵉ
```

</details>

## Idea

Considerᵉ aᵉ typeᵉ `A`ᵉ equippedᵉ with aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`.ᵉ Anᵉ
**`(A,B)`-enrichedᵉ undirectedᵉ graph**ᵉ isᵉ anᵉ
[undirectedᵉ graph](graph-theory.undirected-graphs.mdᵉ) `Gᵉ :=ᵉ (V,E)`ᵉ equippedᵉ with
aᵉ mapᵉ `shᵉ : Vᵉ → A`,ᵉ andᵉ forᵉ eachᵉ vertexᵉ `v`ᵉ anᵉ
[equivalence](foundation-core.equivalences.mdᵉ) fromᵉ `Bᵉ (shᵉ v)`ᵉ to theᵉ typeᵉ ofᵉ
allᵉ edgesᵉ goingᵉ outᵉ ofᵉ `v`,ᵉ i.e.,ᵉ to theᵉ typeᵉ `neighborᵉ v`ᵉ ofᵉ
[neighbors](graph-theory.neighbors-undirected-graphs.md).ᵉ

Theᵉ mapᵉ `shᵉ : Vᵉ → A`ᵉ assignsᵉ to eachᵉ vertexᵉ aᵉ shape,ᵉ andᵉ with itᵉ anᵉ
[∞-group](higher-group-theory.higher-groups.mdᵉ) `BAutᵉ (shᵉ v)`.ᵉ Theᵉ typeᵉ familyᵉ
`B`ᵉ restrictedᵉ to `BAutᵉ (shᵉ v)`ᵉ isᵉ anᵉ
[`Autᵉ (shᵉ v)`-type](higher-group-theory.higher-group-actions.md),ᵉ andᵉ theᵉ
equivalenceᵉ `Bᵉ (shᵉ vᵉ) ≃ᵉ neighborᵉ v`ᵉ thenᵉ ensuresᵉ typeᵉ typeᵉ beingᵉ actedᵉ onᵉ isᵉ
`neighborᵉ v`.ᵉ

## Definition

```agda
Enriched-Undirected-Graphᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ l4ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ)
Enriched-Undirected-Graphᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ =
  Σᵉ ( Undirected-Graphᵉ l3ᵉ l4ᵉ)
    ( λ Gᵉ →
      Σᵉ ( vertex-Undirected-Graphᵉ Gᵉ → Aᵉ)
        ( λ fᵉ →
          ( xᵉ : vertex-Undirected-Graphᵉ Gᵉ) →
          Bᵉ (fᵉ xᵉ) ≃ᵉ neighbor-Undirected-Graphᵉ Gᵉ xᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Gᵉ : Enriched-Undirected-Graphᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  where

  undirected-graph-Enriched-Undirected-Graphᵉ : Undirected-Graphᵉ l3ᵉ l4ᵉ
  undirected-graph-Enriched-Undirected-Graphᵉ = pr1ᵉ Gᵉ

  vertex-Enriched-Undirected-Graphᵉ : UUᵉ l3ᵉ
  vertex-Enriched-Undirected-Graphᵉ =
    vertex-Undirected-Graphᵉ undirected-graph-Enriched-Undirected-Graphᵉ

  unordered-pair-vertices-Enriched-Undirected-Graphᵉ : UUᵉ (lsuc lzero ⊔ l3ᵉ)
  unordered-pair-vertices-Enriched-Undirected-Graphᵉ =
    unordered-pair-vertices-Undirected-Graphᵉ
      undirected-graph-Enriched-Undirected-Graphᵉ

  edge-Enriched-Undirected-Graphᵉ :
    unordered-pair-vertices-Enriched-Undirected-Graphᵉ → UUᵉ l4ᵉ
  edge-Enriched-Undirected-Graphᵉ =
    edge-Undirected-Graphᵉ undirected-graph-Enriched-Undirected-Graphᵉ

  shape-vertex-Enriched-Undirected-Graphᵉ : vertex-Enriched-Undirected-Graphᵉ → Aᵉ
  shape-vertex-Enriched-Undirected-Graphᵉ = pr1ᵉ (pr2ᵉ Gᵉ)

  classifying-type-∞-group-vertex-Enriched-Undirected-Graphᵉ :
    vertex-Enriched-Undirected-Graphᵉ → UUᵉ l1ᵉ
  classifying-type-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ =
    connected-componentᵉ Aᵉ (shape-vertex-Enriched-Undirected-Graphᵉ vᵉ)

  point-classifying-type-∞-group-vertex-Enriched-Undirected-Graphᵉ :
    (vᵉ : vertex-Enriched-Undirected-Graphᵉ) →
    classifying-type-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ
  point-classifying-type-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ =
    point-connected-componentᵉ Aᵉ (shape-vertex-Enriched-Undirected-Graphᵉ vᵉ)

  ∞-group-vertex-Enriched-Undirected-Graphᵉ :
    vertex-Enriched-Undirected-Graphᵉ → ∞-Groupᵉ l1ᵉ
  ∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ =
    connected-component-∞-Groupᵉ Aᵉ (shape-vertex-Enriched-Undirected-Graphᵉ vᵉ)

  type-∞-group-vertex-Enriched-Undirected-Graphᵉ :
    vertex-Enriched-Undirected-Graphᵉ → UUᵉ l1ᵉ
  type-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ =
    type-∞-Groupᵉ (∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ)

  mul-∞-group-vertex-Enriched-Undirected-Graphᵉ :
    (vᵉ : vertex-Enriched-Undirected-Graphᵉ) →
    (hᵉ gᵉ : type-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ) →
    type-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ
  mul-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ hᵉ gᵉ =
    mul-∞-Groupᵉ (∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ) hᵉ gᵉ

  neighbor-Enriched-Undirected-Graphᵉ :
    vertex-Enriched-Undirected-Graphᵉ → UUᵉ (l3ᵉ ⊔ l4ᵉ)
  neighbor-Enriched-Undirected-Graphᵉ =
    neighbor-Undirected-Graphᵉ undirected-graph-Enriched-Undirected-Graphᵉ

  equiv-neighbor-Enriched-Undirected-Graphᵉ :
    (vᵉ : vertex-Enriched-Undirected-Graphᵉ) →
    Bᵉ (shape-vertex-Enriched-Undirected-Graphᵉ vᵉ) ≃ᵉ
    neighbor-Enriched-Undirected-Graphᵉ vᵉ
  equiv-neighbor-Enriched-Undirected-Graphᵉ = pr2ᵉ (pr2ᵉ Gᵉ)

  map-equiv-neighbor-Enriched-Undirected-Graphᵉ :
    (vᵉ : vertex-Enriched-Undirected-Graphᵉ) →
    Bᵉ (shape-vertex-Enriched-Undirected-Graphᵉ vᵉ) →
    neighbor-Enriched-Undirected-Graphᵉ vᵉ
  map-equiv-neighbor-Enriched-Undirected-Graphᵉ vᵉ =
    map-equivᵉ (equiv-neighbor-Enriched-Undirected-Graphᵉ vᵉ)

  map-inv-equiv-neighbor-Enriched-Undirected-Graphᵉ :
    (vᵉ : vertex-Enriched-Undirected-Graphᵉ) →
    neighbor-Enriched-Undirected-Graphᵉ vᵉ →
    Bᵉ (shape-vertex-Enriched-Undirected-Graphᵉ vᵉ)
  map-inv-equiv-neighbor-Enriched-Undirected-Graphᵉ vᵉ =
    map-inv-equivᵉ (equiv-neighbor-Enriched-Undirected-Graphᵉ vᵉ)

  is-section-map-inv-equiv-neighbor-Enriched-Undirected-Graphᵉ :
    (vᵉ : vertex-Enriched-Undirected-Graphᵉ) →
    ( map-equiv-neighbor-Enriched-Undirected-Graphᵉ vᵉ ∘ᵉ
      map-inv-equiv-neighbor-Enriched-Undirected-Graphᵉ vᵉ) ~ᵉ idᵉ
  is-section-map-inv-equiv-neighbor-Enriched-Undirected-Graphᵉ vᵉ =
    is-section-map-inv-equivᵉ (equiv-neighbor-Enriched-Undirected-Graphᵉ vᵉ)

  is-retraction-map-inv-equiv-neighbor-Enriched-Undirected-Graphᵉ :
    (vᵉ : vertex-Enriched-Undirected-Graphᵉ) →
    ( map-inv-equiv-neighbor-Enriched-Undirected-Graphᵉ vᵉ ∘ᵉ
      map-equiv-neighbor-Enriched-Undirected-Graphᵉ vᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-equiv-neighbor-Enriched-Undirected-Graphᵉ vᵉ =
    is-retraction-map-inv-equivᵉ (equiv-neighbor-Enriched-Undirected-Graphᵉ vᵉ)

  action-∞-group-vertex-Enriched-Undirected-Graphᵉ :
    (vᵉ : vertex-Enriched-Undirected-Graphᵉ) →
    action-∞-Groupᵉ l2ᵉ (∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ)
  action-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ uᵉ = Bᵉ (pr1ᵉ uᵉ)

  mul-action-∞-group-vertex-Enriched-Undirected-Graphᵉ :
    (vᵉ : vertex-Enriched-Undirected-Graphᵉ)
    (gᵉ : type-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ) →
    neighbor-Enriched-Undirected-Graphᵉ vᵉ → neighbor-Enriched-Undirected-Graphᵉ vᵉ
  mul-action-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ gᵉ eᵉ =
    map-equiv-neighbor-Enriched-Undirected-Graphᵉ vᵉ
      ( mul-action-∞-Groupᵉ
        ( ∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ)
        ( action-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ)
        ( gᵉ)
        ( map-inv-equiv-neighbor-Enriched-Undirected-Graphᵉ vᵉ eᵉ))

  associative-mul-action-∞-group-vertex-Enriched-Undirected-Graphᵉ :
    (vᵉ : vertex-Enriched-Undirected-Graphᵉ)
    (hᵉ gᵉ : type-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ) →
    (xᵉ : neighbor-Enriched-Undirected-Graphᵉ vᵉ) →
    ( mul-action-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ
      ( mul-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ hᵉ gᵉ)
      ( xᵉ)) ＝ᵉ
    ( mul-action-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ gᵉ
      ( mul-action-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ hᵉ xᵉ))
  associative-mul-action-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ hᵉ gᵉ xᵉ =
    apᵉ
      ( map-equiv-neighbor-Enriched-Undirected-Graphᵉ vᵉ)
      ( ( associative-mul-action-∞-Groupᵉ
          ( ∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ)
          ( action-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ)
          ( hᵉ)
          ( gᵉ)
          ( map-inv-equiv-neighbor-Enriched-Undirected-Graphᵉ vᵉ xᵉ)) ∙ᵉ
        ( apᵉ
          ( mul-action-∞-Groupᵉ
            ( ∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ)
            ( action-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ)
            ( gᵉ))
          ( invᵉ
            ( is-retraction-map-inv-equiv-neighbor-Enriched-Undirected-Graphᵉ vᵉ
              ( mul-action-∞-Groupᵉ
                ( ∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ)
                ( action-∞-group-vertex-Enriched-Undirected-Graphᵉ vᵉ) hᵉ
                ( map-inv-equiv-neighbor-Enriched-Undirected-Graphᵉ vᵉ xᵉ))))))
```

## External links

-ᵉ [Graph](https://ncatlab.org/nlab/show/graphᵉ) atᵉ $n$Labᵉ
-ᵉ [Graph](https://www.wikidata.org/entity/Q141488ᵉ) onᵉ Wikidataᵉ
-ᵉ [Graphᵉ (discreteᵉ mathematics)](<https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)>ᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [Graph](https://mathworld.wolfram.com/Graph.htmlᵉ) atᵉ Wolframᵉ Mathworldᵉ