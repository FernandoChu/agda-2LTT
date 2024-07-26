# Ethane

```agda
module organic-chemistry.ethaneᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbersᵉ

open import finite-group-theory.tetrahedra-in-3-spaceᵉ

open import foundation.coproduct-typesᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import graph-theory.finite-graphsᵉ
open import graph-theory.walks-undirected-graphsᵉ

open import organic-chemistry.alkanesᵉ
open import organic-chemistry.hydrocarbonsᵉ

open import univalent-combinatorics.2-element-typesᵉ
open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

**Ethane**ᵉ isᵉ theᵉ uniqueᵉ alkaneᵉ with twoᵉ carbons.ᵉ

## Definition

```agda
module _
  (tᵉ : tetrahedron-in-3-spaceᵉ) (vᵉ : vertex-tetrahedron-in-3-spaceᵉ tᵉ)
  where

  vertex-ethane-𝔽ᵉ : 𝔽ᵉ lzero
  vertex-ethane-𝔽ᵉ = Fin-𝔽ᵉ 2

  vertex-ethaneᵉ : UUᵉ lzero
  vertex-ethaneᵉ = type-𝔽ᵉ vertex-ethane-𝔽ᵉ

  edge-ethane-Propᵉ : unordered-pairᵉ vertex-ethaneᵉ → Propᵉ lzero
  edge-ethane-Propᵉ pᵉ =
    product-Propᵉ
      ( is-in-unordered-pair-Propᵉ pᵉ (zero-Finᵉ 1ᵉ))
      ( is-in-unordered-pair-Propᵉ pᵉ (one-Finᵉ 1ᵉ))

  edge-ethaneᵉ : unordered-pairᵉ vertex-ethaneᵉ → UUᵉ lzero
  edge-ethaneᵉ pᵉ = type-Propᵉ (edge-ethane-Propᵉ pᵉ)

  abstract
    is-prop-edge-ethaneᵉ :
      (pᵉ : unordered-pairᵉ vertex-ethaneᵉ) → is-propᵉ (edge-ethaneᵉ pᵉ)
    is-prop-edge-ethaneᵉ pᵉ = is-prop-type-Propᵉ (edge-ethane-Propᵉ pᵉ)

  standard-edge-ethane-Propᵉ : (cᵉ c'ᵉ : vertex-ethaneᵉ) → Propᵉ lzero
  standard-edge-ethane-Propᵉ cᵉ c'ᵉ =
    edge-ethane-Propᵉ (standard-unordered-pairᵉ cᵉ c'ᵉ)

  standard-edge-ethaneᵉ : (cᵉ c'ᵉ : vertex-ethaneᵉ) → UUᵉ lzero
  standard-edge-ethaneᵉ cᵉ c'ᵉ = type-Propᵉ (standard-edge-ethane-Propᵉ cᵉ c'ᵉ)

  abstract
    is-prop-standard-edge-ethaneᵉ :
      (cᵉ c'ᵉ : vertex-ethaneᵉ) → is-propᵉ (standard-edge-ethaneᵉ cᵉ c'ᵉ)
    is-prop-standard-edge-ethaneᵉ cᵉ c'ᵉ =
      is-prop-type-Propᵉ (standard-edge-ethane-Propᵉ cᵉ c'ᵉ)

  abstract
    is-decidable-edge-ethane-eq-Fin-twoᵉ :
      (pᵉ : unordered-pairᵉ vertex-ethaneᵉ) →
      type-unordered-pairᵉ pᵉ ＝ᵉ Finᵉ 2 →
      is-decidableᵉ (edge-ethaneᵉ pᵉ)
    is-decidable-edge-ethane-eq-Fin-twoᵉ pᵉ reflᵉ with
      is-zero-or-one-Fin-two-ℕᵉ (element-unordered-pairᵉ pᵉ (zero-Finᵉ 1ᵉ)) |
      is-zero-or-one-Fin-two-ℕᵉ (element-unordered-pairᵉ pᵉ (one-Finᵉ 1ᵉ))
    ... | inlᵉ is-zeroᵉ | inlᵉ is-zero'ᵉ =
      inrᵉ
        ( λ Pᵉ →
          apply-universal-property-trunc-Propᵉ (pr2ᵉ Pᵉ) empty-Propᵉ
            ( λ where
              ( inlᵉ (inrᵉ _) ,ᵉ is-oneᵉ) → neq-inl-inrᵉ (invᵉ is-zeroᵉ ∙ᵉ is-oneᵉ)
              ( inrᵉ _ ,ᵉ is-oneᵉ) → neq-inl-inrᵉ (invᵉ is-zero'ᵉ ∙ᵉ is-oneᵉ)))
    ... | inlᵉ is-zeroᵉ | inrᵉ is-one'ᵉ =
      inlᵉ
        ( pairᵉ
          ( unit-trunc-Propᵉ (zero-Finᵉ 1 ,ᵉ is-zeroᵉ))
          ( unit-trunc-Propᵉ (one-Finᵉ 1 ,ᵉ is-one'ᵉ)))
    ... | inrᵉ is-oneᵉ | inlᵉ is-zero'ᵉ =
      inlᵉ
        ( pairᵉ
          ( unit-trunc-Propᵉ (one-Finᵉ 1 ,ᵉ is-zero'ᵉ))
          ( unit-trunc-Propᵉ (zero-Finᵉ 1 ,ᵉ is-oneᵉ)))
    ... | inrᵉ is-oneᵉ | inrᵉ is-one'ᵉ =
      inrᵉ
        ( λ Pᵉ →
          apply-universal-property-trunc-Propᵉ (pr1ᵉ Pᵉ) empty-Propᵉ
            ( λ where
              ( inlᵉ (inrᵉ _) ,ᵉ is-zeroᵉ) → neq-inl-inrᵉ (invᵉ is-zeroᵉ ∙ᵉ is-oneᵉ)
              ( inrᵉ _ ,ᵉ is-zeroᵉ) → neq-inl-inrᵉ (invᵉ is-zeroᵉ ∙ᵉ is-one'ᵉ)))

  is-decidable-standard-edge-ethaneᵉ :
    (cᵉ c'ᵉ : vertex-ethaneᵉ) → is-decidableᵉ (standard-edge-ethaneᵉ cᵉ c'ᵉ)
  is-decidable-standard-edge-ethaneᵉ cᵉ c'ᵉ =
    is-decidable-edge-ethane-eq-Fin-twoᵉ (standard-unordered-pairᵉ cᵉ c'ᵉ) reflᵉ

  abstract
    is-finite-edge-ethaneᵉ :
      (pᵉ : unordered-pairᵉ vertex-ethaneᵉ) → is-finiteᵉ (edge-ethaneᵉ pᵉ)
    is-finite-edge-ethaneᵉ pᵉ =
      apply-universal-property-trunc-Propᵉ
        ( has-two-elements-type-unordered-pairᵉ pᵉ)
        ( is-finite-Propᵉ (edge-ethaneᵉ pᵉ))
        ( λ eᵉ →
          is-finite-is-decidable-Propᵉ
            ( edge-ethane-Propᵉ pᵉ)
            ( is-decidable-edge-ethane-eq-Fin-twoᵉ pᵉ (invᵉ (eq-equivᵉ eᵉ))))

  edge-ethane-𝔽ᵉ : unordered-pairᵉ vertex-ethaneᵉ → 𝔽ᵉ lzero
  pr1ᵉ (edge-ethane-𝔽ᵉ pᵉ) = edge-ethaneᵉ pᵉ
  pr2ᵉ (edge-ethane-𝔽ᵉ pᵉ) = is-finite-edge-ethaneᵉ pᵉ

  finite-graph-ethaneᵉ : Undirected-Graph-𝔽ᵉ lzero lzero
  pr1ᵉ finite-graph-ethaneᵉ = vertex-ethane-𝔽ᵉ
  pr2ᵉ finite-graph-ethaneᵉ = edge-ethane-𝔽ᵉ

  bonding-ethaneᵉ :
    (cᵉ : vertex-ethaneᵉ) →
    Σᵉ (vertex-ethaneᵉ) (λ c'ᵉ → standard-edge-ethaneᵉ cᵉ c'ᵉ) →
    vertex-tetrahedron-in-3-spaceᵉ tᵉ
  bonding-ethaneᵉ cᵉ eᵉ = vᵉ

  abstract
    is-torsorial-standard-edge-ethaneᵉ :
      (cᵉ : vertex-ethaneᵉ) → is-torsorialᵉ (λ c'ᵉ → standard-edge-ethaneᵉ cᵉ c'ᵉ)
    pr1ᵉ (pr1ᵉ (is-torsorial-standard-edge-ethaneᵉ (inlᵉ (inrᵉ _)))) = one-Finᵉ 1
    pr1ᵉ (pr2ᵉ (pr1ᵉ (is-torsorial-standard-edge-ethaneᵉ (inlᵉ (inrᵉ _))))) =
      unit-trunc-Propᵉ (zero-Finᵉ 1 ,ᵉ reflᵉ)
    pr2ᵉ (pr2ᵉ (pr1ᵉ (is-torsorial-standard-edge-ethaneᵉ (inlᵉ (inrᵉ _))))) =
      unit-trunc-Propᵉ (one-Finᵉ 1 ,ᵉ reflᵉ)
    pr2ᵉ (is-torsorial-standard-edge-ethaneᵉ (inlᵉ (inrᵉ _))) (inlᵉ (inrᵉ _) ,ᵉ Pᵉ) =
      ex-falsoᵉ
        ( apply-universal-property-trunc-Propᵉ (pr2ᵉ Pᵉ) empty-Propᵉ
          ( λ where
            ( inlᵉ (inrᵉ _) ,ᵉ is-oneᵉ) → neq-inl-inrᵉ is-oneᵉ
            ( inrᵉ _ ,ᵉ is-oneᵉ) → neq-inl-inrᵉ is-oneᵉ))
    pr2ᵉ (is-torsorial-standard-edge-ethaneᵉ (inlᵉ (inrᵉ _))) (inrᵉ _ ,ᵉ Pᵉ) =
      eq-pair-eq-fiberᵉ
        ( eq-is-propᵉ
          ( is-prop-edge-ethaneᵉ
            ( standard-unordered-pairᵉ (inlᵉ (inrᵉ _)) (inrᵉ _))))
    pr1ᵉ (pr1ᵉ (is-torsorial-standard-edge-ethaneᵉ (inrᵉ _))) = zero-Finᵉ 1
    pr1ᵉ (pr2ᵉ (pr1ᵉ (is-torsorial-standard-edge-ethaneᵉ (inrᵉ _)))) =
      unit-trunc-Propᵉ (one-Finᵉ 1 ,ᵉ reflᵉ)
    pr2ᵉ (pr2ᵉ (pr1ᵉ (is-torsorial-standard-edge-ethaneᵉ (inrᵉ _)))) =
      unit-trunc-Propᵉ (zero-Finᵉ 1 ,ᵉ reflᵉ)
    pr2ᵉ (is-torsorial-standard-edge-ethaneᵉ (inrᵉ _)) (inlᵉ (inrᵉ _) ,ᵉ Pᵉ) =
      eq-pair-eq-fiberᵉ
        ( eq-is-propᵉ
          ( is-prop-edge-ethaneᵉ
            ( standard-unordered-pairᵉ (inrᵉ starᵉ) (inlᵉ (inrᵉ starᵉ)))))
    pr2ᵉ (is-torsorial-standard-edge-ethaneᵉ (inrᵉ _)) (inrᵉ _ ,ᵉ Pᵉ) =
      ex-falsoᵉ
        ( apply-universal-property-trunc-Propᵉ (pr1ᵉ Pᵉ) empty-Propᵉ
          ( λ where
            ( inlᵉ (inrᵉ _) ,ᵉ is-zeroᵉ) → neq-inr-inlᵉ is-zeroᵉ
            ( inrᵉ _ ,ᵉ is-zeroᵉ) → neq-inr-inlᵉ is-zeroᵉ))

  abstract
    is-emb-bonding-ethaneᵉ : (cᵉ : vertex-ethaneᵉ) → is-embᵉ (bonding-ethaneᵉ cᵉ)
    is-emb-bonding-ethaneᵉ cᵉ =
      is-emb-is-injectiveᵉ
        ( is-set-type-UU-Finᵉ 4 (pr1ᵉ tᵉ))
        ( is-injective-is-contrᵉ (λ eᵉ → vᵉ) (is-torsorial-standard-edge-ethaneᵉ cᵉ))

  emb-bonding-ethaneᵉ :
    (cᵉ : vertex-ethaneᵉ) →
    Σᵉ (vertex-ethaneᵉ) (λ c'ᵉ → standard-edge-ethaneᵉ cᵉ c'ᵉ) ↪ᵉ
    vertex-tetrahedron-in-3-spaceᵉ tᵉ
  pr1ᵉ (emb-bonding-ethaneᵉ cᵉ) = bonding-ethaneᵉ cᵉ
  pr2ᵉ (emb-bonding-ethaneᵉ cᵉ) = is-emb-bonding-ethaneᵉ cᵉ

  count-standard-edge-ethaneᵉ :
    (cᵉ c'ᵉ : vertex-ethaneᵉ) → countᵉ (standard-edge-ethaneᵉ cᵉ c'ᵉ)
  count-standard-edge-ethaneᵉ cᵉ c'ᵉ =
    count-is-decidable-Propᵉ
      ( standard-edge-ethane-Propᵉ cᵉ c'ᵉ)
      ( is-decidable-standard-edge-ethaneᵉ cᵉ c'ᵉ)

  abstract
    number-of-elements-count-standard-edge-ethane-leq-3ᵉ :
      (cᵉ c'ᵉ : vertex-ethaneᵉ) →
      number-of-elements-countᵉ (count-standard-edge-ethaneᵉ cᵉ c'ᵉ) ≤-ℕᵉ 3
    number-of-elements-count-standard-edge-ethane-leq-3ᵉ
      (inlᵉ (inrᵉ _)) (inlᵉ (inrᵉ _)) =
      starᵉ
    number-of-elements-count-standard-edge-ethane-leq-3ᵉ
      (inlᵉ (inrᵉ _)) (inrᵉ _) =
      starᵉ
    number-of-elements-count-standard-edge-ethane-leq-3ᵉ
      (inrᵉ _) (inlᵉ (inrᵉ _)) =
      starᵉ
    number-of-elements-count-standard-edge-ethane-leq-3ᵉ
      (inrᵉ _) (inrᵉ _) = starᵉ

  ethaneᵉ : hydrocarbonᵉ lzero lzero
  pr1ᵉ ethaneᵉ = finite-graph-ethaneᵉ
  pr1ᵉ (pr2ᵉ ethaneᵉ) cᵉ = tᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ ethaneᵉ)) = emb-bonding-ethaneᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ethaneᵉ))) (inlᵉ (inrᵉ _)) Pᵉ =
    apply-universal-property-trunc-Propᵉ (pr2ᵉ Pᵉ) empty-Propᵉ
      ( λ where
        ( inlᵉ (inrᵉ _) ,ᵉ is-oneᵉ) → neq-inl-inrᵉ is-oneᵉ
        ( inrᵉ _ ,ᵉ is-oneᵉ) → neq-inl-inrᵉ is-oneᵉ)
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ethaneᵉ))) (inrᵉ _) Pᵉ =
    apply-universal-property-trunc-Propᵉ (pr1ᵉ Pᵉ) empty-Propᵉ
      ( λ where
        ( inlᵉ (inrᵉ _) ,ᵉ is-zeroᵉ) → neq-inr-inlᵉ is-zeroᵉ
        ( inrᵉ _ ,ᵉ is-zeroᵉ) → neq-inr-inlᵉ is-zeroᵉ)
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ethaneᵉ)))) cᵉ c'ᵉ =
    concatenate-eq-leq-ℕᵉ 3
      ( invᵉ
        ( compute-number-of-elements-is-finiteᵉ
          ( count-standard-edge-ethaneᵉ cᵉ c'ᵉ)
          ( is-finite-edge-ethaneᵉ (standard-unordered-pairᵉ cᵉ c'ᵉ))))
      (number-of-elements-count-standard-edge-ethane-leq-3ᵉ cᵉ c'ᵉ)
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ethaneᵉ)))) (inlᵉ (inrᵉ _)) (inlᵉ (inrᵉ _)) =
    unit-trunc-Propᵉ refl-walk-Undirected-Graphᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ethaneᵉ)))) (inlᵉ (inrᵉ _)) (inrᵉ _) =
    unit-trunc-Propᵉ
      ( trᵉ
        ( λ xᵉ →
          walk-Undirected-Graphᵉ
            ( undirected-graph-Undirected-Graph-𝔽ᵉ finite-graph-ethaneᵉ)
            ( zero-Finᵉ 1ᵉ)
            ( element-standard-unordered-pairᵉ (zero-Finᵉ 1ᵉ) (one-Finᵉ 1ᵉ) xᵉ))
        ( compute-swap-2-Element-Typeᵉ
          ( Fin-UU-Fin'ᵉ 2ᵉ)
          ( zero-Finᵉ 1ᵉ)
          ( one-Finᵉ 1ᵉ)
          ( neq-inl-inrᵉ))
        ( cons-walk-Undirected-Graphᵉ
          ( standard-unordered-pairᵉ (zero-Finᵉ 1ᵉ) (one-Finᵉ 1ᵉ))
          ( ( unit-trunc-Propᵉ (zero-Finᵉ 1 ,ᵉ reflᵉ)) ,ᵉ
            ( unit-trunc-Propᵉ (one-Finᵉ 1 ,ᵉ reflᵉ)))
          { zero-Finᵉ 1ᵉ}
          ( refl-walk-Undirected-Graphᵉ)))
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ethaneᵉ)))) (inrᵉ _) (inlᵉ (inrᵉ _)) =
    unit-trunc-Propᵉ
      ( trᵉ
        ( λ xᵉ →
          walk-Undirected-Graphᵉ
            ( undirected-graph-Undirected-Graph-𝔽ᵉ finite-graph-ethaneᵉ)
            ( one-Finᵉ 1ᵉ)
            ( element-standard-unordered-pairᵉ (one-Finᵉ 1ᵉ) (zero-Finᵉ 1ᵉ) xᵉ))
        ( compute-swap-2-Element-Typeᵉ
          ( Fin-UU-Fin'ᵉ 2ᵉ)
          ( zero-Finᵉ 1ᵉ)
          ( one-Finᵉ 1ᵉ)
          ( neq-inl-inrᵉ))
        ( cons-walk-Undirected-Graphᵉ
          ( standard-unordered-pairᵉ (one-Finᵉ 1ᵉ) (zero-Finᵉ 1ᵉ))
          ( ( unit-trunc-Propᵉ (one-Finᵉ 1 ,ᵉ reflᵉ)) ,ᵉ
            ( unit-trunc-Propᵉ (zero-Finᵉ 1 ,ᵉ reflᵉ)))
          { zero-Finᵉ 1ᵉ}
          ( refl-walk-Undirected-Graphᵉ)))
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ethaneᵉ)))) (inrᵉ _) (inrᵉ _) =
    unit-trunc-Propᵉ refl-walk-Undirected-Graphᵉ

  is-alkane-ethaneᵉ : is-alkane-hydrocarbonᵉ ethaneᵉ
  is-alkane-ethaneᵉ = is-prop-standard-edge-ethaneᵉ
```