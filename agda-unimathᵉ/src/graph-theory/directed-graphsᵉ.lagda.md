# Directed graphs

```agda
module graph-theory.directed-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **directedᵉ graph**ᵉ consistsᵉ ofᵉ aᵉ typeᵉ ofᵉ verticesᵉ equippedᵉ with aᵉ binary,ᵉ typeᵉ
valuedᵉ relationᵉ ofᵉ edges.ᵉ Alternatively,ᵉ oneᵉ canᵉ defineᵉ aᵉ directedᵉ graphᵉ to
consistᵉ ofᵉ aᵉ typeᵉ `V`ᵉ ofᵉ **vertices**,ᵉ aᵉ typeᵉ `E`ᵉ ofᵉ **edges**,ᵉ andᵉ aᵉ mapᵉ
`Eᵉ → Vᵉ ×ᵉ V`ᵉ determiningᵉ theᵉ **source**ᵉ andᵉ **target**ᵉ ofᵉ eachᵉ edge.ᵉ

Toᵉ seeᵉ thatᵉ theseᵉ twoᵉ definitionsᵉ areᵉ
[equivalent](foundation-core.equivalences.md),ᵉ recallᵉ thatᵉ
[$\Sigma$-types](foundation.dependent-pair-types.mdᵉ) preserveᵉ equivalencesᵉ andᵉ aᵉ
typeᵉ familyᵉ $Aᵉ \toᵉ U$ᵉ isᵉ equivalentᵉ to $\sum_{(Cᵉ : Uᵉ)} Cᵉ \toᵉ A$ᵉ byᵉ
[typeᵉ duality](foundation.type-duality.md).ᵉ Usingᵉ theseᵉ twoᵉ observationsᵉ weᵉ makeᵉ
theᵉ followingᵉ calculationᵉ:

$$ᵉ
\begin{equationᵉ}
\begin{splitᵉ}
\sum_{(V\,:\,\mathcal{Uᵉ})} (Vᵉ \toᵉ Vᵉ \toᵉ \mathcal{Uᵉ}) &ᵉ \simeqᵉ \sum_{(V\,:\,\mathcal{Uᵉ})}
 (Vᵉ \timesᵉ Vᵉ \toᵉ \mathcal{Uᵉ}) \\ᵉ
 &\simeqᵉ \sum_{(V,E\,:\,\mathcal{Uᵉ})} (Eᵉ \toᵉ (Vᵉ \timesᵉ Vᵉ)) \\ᵉ
&\simeqᵉ  \sum_{(V,E\,:\,\mathcal{Uᵉ})} ((Eᵉ \toᵉ Vᵉ) \timesᵉ (Eᵉ \toᵉ Vᵉ))
\end{splitᵉ}
\end{equationᵉ}
$$ᵉ

## Definition

```agda
Directed-Graphᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Directed-Graphᵉ l1ᵉ l2ᵉ = Σᵉ (UUᵉ l1ᵉ) (λ Vᵉ → Vᵉ → Vᵉ → UUᵉ l2ᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  vertex-Directed-Graphᵉ : UUᵉ l1ᵉ
  vertex-Directed-Graphᵉ = pr1ᵉ Gᵉ

  edge-Directed-Graphᵉ : (xᵉ yᵉ : vertex-Directed-Graphᵉ) → UUᵉ l2ᵉ
  edge-Directed-Graphᵉ = pr2ᵉ Gᵉ

  total-edge-Directed-Graphᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  total-edge-Directed-Graphᵉ =
    Σᵉ ( vertex-Directed-Graphᵉ)
      ( λ xᵉ → Σᵉ vertex-Directed-Graphᵉ (edge-Directed-Graphᵉ xᵉ))

  source-total-edge-Directed-Graphᵉ :
    total-edge-Directed-Graphᵉ → vertex-Directed-Graphᵉ
  source-total-edge-Directed-Graphᵉ = pr1ᵉ

  target-total-edge-Directed-Graphᵉ :
    total-edge-Directed-Graphᵉ → vertex-Directed-Graphᵉ
  target-total-edge-Directed-Graphᵉ eᵉ = pr1ᵉ (pr2ᵉ eᵉ)

  edge-total-edge-Directed-Graphᵉ :
    (eᵉ : total-edge-Directed-Graphᵉ) →
    edge-Directed-Graphᵉ
      ( source-total-edge-Directed-Graphᵉ eᵉ)
      ( target-total-edge-Directed-Graphᵉ eᵉ)
  edge-total-edge-Directed-Graphᵉ eᵉ = pr2ᵉ (pr2ᵉ eᵉ)

  direct-predecessor-Directed-Graphᵉ :
    vertex-Directed-Graphᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  direct-predecessor-Directed-Graphᵉ xᵉ =
    Σᵉ vertex-Directed-Graphᵉ (λ yᵉ → edge-Directed-Graphᵉ yᵉ xᵉ)

  direct-successor-Directed-Graphᵉ :
    vertex-Directed-Graphᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  direct-successor-Directed-Graphᵉ xᵉ =
    Σᵉ vertex-Directed-Graphᵉ (edge-Directed-Graphᵉ xᵉ)
```

### Alternative definition

```agda
module alternativeᵉ where

  Directed-Graph'ᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
  Directed-Graph'ᵉ l1ᵉ l2ᵉ = Σᵉ (UUᵉ l1ᵉ) λ Vᵉ → Σᵉ (UUᵉ l2ᵉ) (λ Eᵉ → (Eᵉ → Vᵉ) ×ᵉ (Eᵉ → Vᵉ))

  module _
    {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graph'ᵉ l1ᵉ l2ᵉ)
    where

    vertex-Directed-Graph'ᵉ : UUᵉ l1ᵉ
    vertex-Directed-Graph'ᵉ = pr1ᵉ Gᵉ

    edge-Directed-Graph'ᵉ : UUᵉ l2ᵉ
    edge-Directed-Graph'ᵉ = pr1ᵉ (pr2ᵉ Gᵉ)

    source-edge-Directed-Graphᵉ : edge-Directed-Graph'ᵉ ->ᵉ vertex-Directed-Graph'ᵉ
    source-edge-Directed-Graphᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ Gᵉ))

    target-edge-Directed-Graphᵉ : edge-Directed-Graph'ᵉ ->ᵉ vertex-Directed-Graph'ᵉ
    target-edge-Directed-Graphᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ Gᵉ))
```

```agda
module equivᵉ {l1ᵉ l2ᵉ : Level} where
  open alternativeᵉ

  Directed-Graph-to-Directed-Graph'ᵉ :
    Directed-Graphᵉ l1ᵉ l2ᵉ ->ᵉ Directed-Graph'ᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (Directed-Graph-to-Directed-Graph'ᵉ Gᵉ) = vertex-Directed-Graphᵉ Gᵉ
  pr1ᵉ (pr2ᵉ (Directed-Graph-to-Directed-Graph'ᵉ Gᵉ)) =
    Σᵉ ( vertex-Directed-Graphᵉ Gᵉ)
      ( λ xᵉ → Σᵉ (vertex-Directed-Graphᵉ Gᵉ) λ yᵉ → edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ)
  pr1ᵉ (pr2ᵉ (pr2ᵉ (Directed-Graph-to-Directed-Graph'ᵉ Gᵉ))) = pr1ᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (Directed-Graph-to-Directed-Graph'ᵉ Gᵉ))) = pr1ᵉ ∘ᵉ pr2ᵉ

  Directed-Graph'-to-Directed-Graphᵉ :
    Directed-Graph'ᵉ l1ᵉ l2ᵉ ->ᵉ Directed-Graphᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (Directed-Graph'-to-Directed-Graphᵉ (Vᵉ ,ᵉ Eᵉ ,ᵉ stᵉ ,ᵉ tgᵉ)) = Vᵉ
  pr2ᵉ (Directed-Graph'-to-Directed-Graphᵉ (Vᵉ ,ᵉ Eᵉ ,ᵉ stᵉ ,ᵉ tgᵉ)) xᵉ yᵉ =
    Σᵉ Eᵉ (λ eᵉ → (Idᵉ (stᵉ eᵉ) xᵉ) ×ᵉ (Idᵉ (tgᵉ eᵉ) yᵉ))
```

## External links

-ᵉ [Digraph](https://ncatlab.org/nlab/show/digraphᵉ) atᵉ $n$Labᵉ
-ᵉ [Directedᵉ graph](https://ncatlab.org/nlab/show/directed+graphᵉ) atᵉ $n$Labᵉ
-ᵉ [Directedᵉ graph](https://www.wikidata.org/entity/Q1137726ᵉ) onᵉ Wikidataᵉ
-ᵉ [Directedᵉ graph](https://en.wikipedia.org/wiki/Directed_graphᵉ) atᵉ Wikipediaᵉ
-ᵉ [Directedᵉ graph](https://mathworld.wolfram.com/DirectedGraph.htmlᵉ) atᵉ Wolframᵉ
  Mathworldᵉ