# Hydrocarbons

```agda
module organic-chemistry.hydrocarbonsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbersᵉ

open import finite-group-theory.tetrahedra-in-3-spaceᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.negationᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import graph-theory.connected-undirected-graphsᵉ
open import graph-theory.finite-graphsᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Weᵉ defineᵉ theᵉ typeᵉ ofᵉ allᵉ theoreticallyᵉ possibleᵉ hydrocarbons,ᵉ correctlyᵉ
accountingᵉ forᵉ theᵉ symmetriesᵉ betweenᵉ hydrocarbonsᵉ andᵉ theᵉ differentᵉ isomers.ᵉ

Hydrocarbonsᵉ areᵉ builtᵉ outᵉ ofᵉ carbonᵉ andᵉ hydrogenᵉ atoms.ᵉ Theᵉ symmetryᵉ groupᵉ ofᵉ
anᵉ isolatedᵉ carbonᵉ atomᵉ in 3-spaceᵉ isᵉ theᵉ alternatingᵉ groupᵉ `A₄`,ᵉ where theᵉ
numberᵉ 4 comesᵉ fromᵉ theᵉ numberᵉ ofᵉ bondsᵉ aᵉ carbonᵉ atomᵉ makesᵉ in aᵉ molecule.ᵉ

Bondsᵉ in hydrocarbonsᵉ canᵉ appearᵉ asᵉ singleᵉ bonds,ᵉ doubleᵉ bonds,ᵉ andᵉ tripleᵉ
bonds,ᵉ butᵉ thereᵉ areᵉ noᵉ quadrupleᵉ bonds.ᵉ

Weᵉ defineᵉ hydrocarbonsᵉ to beᵉ graphsᵉ equippedᵉ with aᵉ familyᵉ ofᵉ tetrahedraᵉ in
3-dimensionalᵉ spaceᵉ indexedᵉ byᵉ theᵉ verticesᵉ andᵉ forᵉ eachᵉ vertexᵉ `c`ᵉ anᵉ embeddingᵉ
fromᵉ theᵉ typeᵉ ofᵉ allᵉ edgesᵉ incidentᵉ to `c`ᵉ intoᵉ theᵉ verticesᵉ ofᵉ theᵉ tetrahedronᵉ
associatedᵉ to `c`,ᵉ satisfyingᵉ theᵉ followingᵉ conditionsᵉ:

-ᵉ Thereᵉ areᵉ atᵉ mostᵉ 3 edgesᵉ betweenᵉ anyᵉ twoᵉ verticesᵉ
-ᵉ Theᵉ graphᵉ containsᵉ noᵉ loopsᵉ
-ᵉ Theᵉ graphᵉ isᵉ connectedᵉ

## Definition

```agda
hydrocarbonᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
hydrocarbonᵉ l1ᵉ l2ᵉ =
  Σᵉ ( Undirected-Graph-𝔽ᵉ l1ᵉ l2ᵉ)
    ( λ Gᵉ →
      Σᵉ ( vertex-Undirected-Graph-𝔽ᵉ Gᵉ → tetrahedron-in-3-spaceᵉ)
        ( λ Cᵉ →
          ( ( cᵉ : vertex-Undirected-Graph-𝔽ᵉ Gᵉ) →
            Σᵉ ( vertex-Undirected-Graph-𝔽ᵉ Gᵉ)
              ( λ c'ᵉ →
                edge-Undirected-Graph-𝔽ᵉ Gᵉ (standard-unordered-pairᵉ cᵉ c'ᵉ)) ↪ᵉ
                type-UU-Finᵉ 4 (pr1ᵉ (Cᵉ cᵉ))) ×ᵉ
          ( ( (cᵉ : vertex-Undirected-Graph-𝔽ᵉ Gᵉ) →
              ¬ᵉ ( edge-Undirected-Graph-𝔽ᵉ Gᵉ
                  ( standard-unordered-pairᵉ cᵉ cᵉ))) ×ᵉ
            ( ( (cᵉ c'ᵉ : vertex-Undirected-Graph-𝔽ᵉ Gᵉ) →
                leq-ℕᵉ
                  ( number-of-elements-is-finiteᵉ
                    ( is-finite-type-𝔽ᵉ (pr2ᵉ Gᵉ (standard-unordered-pairᵉ cᵉ c'ᵉ))))
                  ( 3ᵉ)) ×ᵉ
                is-connected-Undirected-Graphᵉ
                  ( undirected-graph-Undirected-Graph-𝔽ᵉ Gᵉ)))))

module _
  {l1ᵉ l2ᵉ : Level} (Hᵉ : hydrocarbonᵉ l1ᵉ l2ᵉ)
  where

  finite-graph-hydrocarbonᵉ : Undirected-Graph-𝔽ᵉ l1ᵉ l2ᵉ
  finite-graph-hydrocarbonᵉ = pr1ᵉ Hᵉ

  vertex-hydrocarbon-𝔽ᵉ : 𝔽ᵉ l1ᵉ
  vertex-hydrocarbon-𝔽ᵉ = pr1ᵉ finite-graph-hydrocarbonᵉ

  vertex-hydrocarbonᵉ : UUᵉ l1ᵉ
  vertex-hydrocarbonᵉ = vertex-Undirected-Graph-𝔽ᵉ finite-graph-hydrocarbonᵉ

  is-finite-vertex-hydrocarbonᵉ : is-finiteᵉ vertex-hydrocarbonᵉ
  is-finite-vertex-hydrocarbonᵉ =
    is-finite-vertex-Undirected-Graph-𝔽ᵉ finite-graph-hydrocarbonᵉ

  unordered-pair-vertices-hydrocarbonᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ)
  unordered-pair-vertices-hydrocarbonᵉ = unordered-pairᵉ vertex-hydrocarbonᵉ

  edge-hydrocarbon-𝔽ᵉ : unordered-pair-vertices-hydrocarbonᵉ → 𝔽ᵉ l2ᵉ
  edge-hydrocarbon-𝔽ᵉ = pr2ᵉ finite-graph-hydrocarbonᵉ

  edge-hydrocarbonᵉ : unordered-pair-vertices-hydrocarbonᵉ → UUᵉ l2ᵉ
  edge-hydrocarbonᵉ = edge-Undirected-Graph-𝔽ᵉ finite-graph-hydrocarbonᵉ

  is-finite-edge-hydrocarbonᵉ :
    (pᵉ : unordered-pair-vertices-hydrocarbonᵉ) → is-finiteᵉ (edge-hydrocarbonᵉ pᵉ)
  is-finite-edge-hydrocarbonᵉ =
    is-finite-edge-Undirected-Graph-𝔽ᵉ finite-graph-hydrocarbonᵉ

  carbon-atom-hydrocarbonᵉ :
    vertex-hydrocarbonᵉ → tetrahedron-in-3-spaceᵉ
  carbon-atom-hydrocarbonᵉ = pr1ᵉ (pr2ᵉ Hᵉ)

  electron-carbon-atom-hydrocarbonᵉ :
    (cᵉ : vertex-hydrocarbonᵉ) → UUᵉ lzero
  electron-carbon-atom-hydrocarbonᵉ cᵉ =
    vertex-tetrahedron-in-3-spaceᵉ (carbon-atom-hydrocarbonᵉ cᵉ)

  emb-bonding-hydrocarbonᵉ :
    (cᵉ : vertex-hydrocarbonᵉ) →
    Σᵉ vertex-hydrocarbonᵉ
      ( λ c'ᵉ → edge-hydrocarbonᵉ (standard-unordered-pairᵉ cᵉ c'ᵉ)) ↪ᵉ
    electron-carbon-atom-hydrocarbonᵉ cᵉ
  emb-bonding-hydrocarbonᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ Hᵉ))

  bonding-hydrocarbonᵉ :
    {cᵉ c'ᵉ : vertex-hydrocarbonᵉ} →
    edge-hydrocarbonᵉ (standard-unordered-pairᵉ cᵉ c'ᵉ) →
    electron-carbon-atom-hydrocarbonᵉ cᵉ
  bonding-hydrocarbonᵉ {cᵉ} {c'ᵉ} bᵉ =
    map-embᵉ (emb-bonding-hydrocarbonᵉ cᵉ) (pairᵉ c'ᵉ bᵉ)
```