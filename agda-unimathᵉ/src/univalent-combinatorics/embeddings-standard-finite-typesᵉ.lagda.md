# Embeddings between standard finite types

```agda
module univalent-combinatorics.embeddings-standard-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.repeating-element-standard-finite-typeᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Anᵉ embeddingᵉ betweenᵉ standardᵉ finiteᵉ typesᵉ isᵉ anᵉ embeddingᵉ `Finᵉ kᵉ ↪ᵉ Finᵉ l`.ᵉ

## Definitions

```agda
emb-Finᵉ : (kᵉ lᵉ : ℕᵉ) → UUᵉ lzero
emb-Finᵉ kᵉ lᵉ = Finᵉ kᵉ ↪ᵉ Finᵉ lᵉ
```

## Properties

### Given an embedding `f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)`, we obtain an embedding `Fin k ↪ Fin l`

```agda
cases-map-reduce-emb-Finᵉ :
  (kᵉ lᵉ : ℕᵉ) (fᵉ : emb-Finᵉ (succ-ℕᵉ kᵉ) (succ-ℕᵉ lᵉ)) →
  is-decidableᵉ (is-inl-Finᵉ lᵉ (map-embᵉ fᵉ (inrᵉ starᵉ))) → (xᵉ : Finᵉ kᵉ) →
  is-decidableᵉ (is-inl-Finᵉ lᵉ (map-embᵉ fᵉ (inlᵉ xᵉ))) → Finᵉ lᵉ
cases-map-reduce-emb-Finᵉ kᵉ lᵉ fᵉ (inlᵉ (pairᵉ tᵉ pᵉ)) xᵉ dᵉ =
  repeat-Finᵉ lᵉ tᵉ (map-embᵉ fᵉ (inlᵉ xᵉ))
cases-map-reduce-emb-Finᵉ kᵉ lᵉ fᵉ (inrᵉ gᵉ) xᵉ (inlᵉ (pairᵉ yᵉ pᵉ)) = yᵉ
cases-map-reduce-emb-Finᵉ kᵉ lᵉ fᵉ (inrᵉ gᵉ) xᵉ (inrᵉ hᵉ) =
  ex-falsoᵉ (Eq-Fin-eqᵉ (succ-ℕᵉ kᵉ) (is-injective-embᵉ fᵉ (pᵉ ∙ᵉ invᵉ qᵉ)))
  where
  pᵉ : is-neg-one-Finᵉ (succ-ℕᵉ lᵉ) (map-embᵉ fᵉ (inrᵉ starᵉ))
  pᵉ = is-neg-one-is-not-inl-Finᵉ lᵉ (map-embᵉ fᵉ (inrᵉ starᵉ)) gᵉ
  qᵉ : is-neg-one-Finᵉ (succ-ℕᵉ lᵉ) (map-embᵉ fᵉ (inlᵉ xᵉ))
  qᵉ = is-neg-one-is-not-inl-Finᵉ lᵉ (map-embᵉ fᵉ (inlᵉ xᵉ)) hᵉ

map-reduce-emb-Finᵉ :
  (kᵉ lᵉ : ℕᵉ) (fᵉ : Finᵉ (succ-ℕᵉ kᵉ) ↪ᵉ Finᵉ (succ-ℕᵉ lᵉ)) → Finᵉ kᵉ → Finᵉ lᵉ
map-reduce-emb-Finᵉ kᵉ lᵉ fᵉ xᵉ =
  cases-map-reduce-emb-Finᵉ kᵉ lᵉ fᵉ
    ( is-decidable-is-inl-Finᵉ lᵉ (map-embᵉ fᵉ (inrᵉ starᵉ)))
    ( xᵉ)
    ( is-decidable-is-inl-Finᵉ lᵉ (map-embᵉ fᵉ (inlᵉ xᵉ)))

abstract
  is-injective-cases-map-reduce-emb-Finᵉ :
    (kᵉ lᵉ : ℕᵉ) (fᵉ : Finᵉ (succ-ℕᵉ kᵉ) ↪ᵉ Finᵉ (succ-ℕᵉ lᵉ))
    (dᵉ : is-decidableᵉ (is-inl-Finᵉ lᵉ (map-embᵉ fᵉ (inrᵉ starᵉ))))
    (xᵉ : Finᵉ kᵉ) (eᵉ : is-decidableᵉ (is-inl-Finᵉ lᵉ (map-embᵉ fᵉ (inlᵉ xᵉ))))
    (x'ᵉ : Finᵉ kᵉ) (e'ᵉ : is-decidableᵉ (is-inl-Finᵉ lᵉ (map-embᵉ fᵉ (inlᵉ x'ᵉ)))) →
    Idᵉ
      ( cases-map-reduce-emb-Finᵉ kᵉ lᵉ fᵉ dᵉ xᵉ eᵉ)
      ( cases-map-reduce-emb-Finᵉ kᵉ lᵉ fᵉ dᵉ x'ᵉ e'ᵉ) →
    Idᵉ xᵉ x'ᵉ
  is-injective-cases-map-reduce-emb-Finᵉ kᵉ lᵉ fᵉ (inlᵉ (pairᵉ tᵉ qᵉ)) xᵉ eᵉ x'ᵉ e'ᵉ pᵉ =
    is-injective-inlᵉ
      ( is-injective-is-embᵉ
        ( is-emb-map-embᵉ fᵉ)
        ( is-almost-injective-repeat-Finᵉ lᵉ tᵉ
          ( λ αᵉ → Eq-Fin-eqᵉ (succ-ℕᵉ kᵉ) (is-injective-embᵉ fᵉ ((invᵉ qᵉ) ∙ᵉ αᵉ)))
          ( λ αᵉ → Eq-Fin-eqᵉ (succ-ℕᵉ kᵉ) (is-injective-embᵉ fᵉ ((invᵉ qᵉ) ∙ᵉ αᵉ)))
          ( pᵉ)))
  is-injective-cases-map-reduce-emb-Finᵉ
    kᵉ lᵉ fᵉ (inrᵉ gᵉ) xᵉ (inlᵉ (pairᵉ yᵉ qᵉ)) x'ᵉ (inlᵉ (pairᵉ y'ᵉ q'ᵉ)) pᵉ =
    is-injective-inlᵉ (is-injective-embᵉ fᵉ ((invᵉ qᵉ) ∙ᵉ (apᵉ inlᵉ pᵉ ∙ᵉ q'ᵉ)))
  is-injective-cases-map-reduce-emb-Finᵉ
    kᵉ lᵉ fᵉ (inrᵉ gᵉ) xᵉ (inlᵉ (pairᵉ yᵉ qᵉ)) x'ᵉ (inrᵉ hᵉ) pᵉ =
    ex-falsoᵉ
    ( Eq-Fin-eqᵉ (succ-ℕᵉ kᵉ)
      ( is-injective-embᵉ fᵉ
        ( ( is-neg-one-is-not-inl-Finᵉ lᵉ (pr1ᵉ fᵉ (inrᵉ starᵉ)) gᵉ) ∙ᵉ
          ( invᵉ (is-neg-one-is-not-inl-Finᵉ lᵉ (pr1ᵉ fᵉ (inlᵉ x'ᵉ)) hᵉ)))))
  is-injective-cases-map-reduce-emb-Finᵉ
    kᵉ lᵉ fᵉ (inrᵉ gᵉ) xᵉ (inrᵉ hᵉ) x'ᵉ (inlᵉ (pairᵉ y'ᵉ q'ᵉ)) pᵉ =
    ex-falsoᵉ
      ( Eq-Fin-eqᵉ (succ-ℕᵉ kᵉ)
        ( is-injective-embᵉ fᵉ
          ( ( is-neg-one-is-not-inl-Finᵉ lᵉ (pr1ᵉ fᵉ (inrᵉ starᵉ)) gᵉ) ∙ᵉ
            ( invᵉ (is-neg-one-is-not-inl-Finᵉ lᵉ (pr1ᵉ fᵉ (inlᵉ xᵉ)) hᵉ)))))
  is-injective-cases-map-reduce-emb-Finᵉ kᵉ lᵉ fᵉ (inrᵉ gᵉ) xᵉ (inrᵉ hᵉ) x'ᵉ (inrᵉ mᵉ) pᵉ =
    ex-falsoᵉ
      ( Eq-Fin-eqᵉ (succ-ℕᵉ kᵉ)
        ( is-injective-embᵉ fᵉ
          ( ( is-neg-one-is-not-inl-Finᵉ lᵉ (pr1ᵉ fᵉ (inrᵉ starᵉ)) gᵉ) ∙ᵉ
            ( invᵉ (is-neg-one-is-not-inl-Finᵉ lᵉ (pr1ᵉ fᵉ (inlᵉ xᵉ)) hᵉ)))))

abstract
  is-injective-map-reduce-emb-Finᵉ :
    (kᵉ lᵉ : ℕᵉ) (fᵉ : Finᵉ (succ-ℕᵉ kᵉ) ↪ᵉ Finᵉ (succ-ℕᵉ lᵉ)) →
    is-injectiveᵉ (map-reduce-emb-Finᵉ kᵉ lᵉ fᵉ)
  is-injective-map-reduce-emb-Finᵉ kᵉ lᵉ fᵉ {xᵉ} {yᵉ} =
    is-injective-cases-map-reduce-emb-Finᵉ kᵉ lᵉ fᵉ
      ( is-decidable-is-inl-Finᵉ lᵉ (map-embᵉ fᵉ (inrᵉ starᵉ)))
      ( xᵉ)
      ( is-decidable-is-inl-Finᵉ lᵉ (map-embᵉ fᵉ (inlᵉ xᵉ)))
      ( yᵉ)
      ( is-decidable-is-inl-Finᵉ lᵉ (map-embᵉ fᵉ (inlᵉ yᵉ)))

abstract
  is-emb-map-reduce-emb-Finᵉ :
    (kᵉ lᵉ : ℕᵉ) (fᵉ : Finᵉ (succ-ℕᵉ kᵉ) ↪ᵉ Finᵉ (succ-ℕᵉ lᵉ)) →
    is-embᵉ (map-reduce-emb-Finᵉ kᵉ lᵉ fᵉ)
  is-emb-map-reduce-emb-Finᵉ kᵉ lᵉ fᵉ =
    is-emb-is-injectiveᵉ (is-set-Finᵉ lᵉ) (is-injective-map-reduce-emb-Finᵉ kᵉ lᵉ fᵉ)

reduce-emb-Finᵉ :
  (kᵉ lᵉ : ℕᵉ) → emb-Finᵉ (succ-ℕᵉ kᵉ) (succ-ℕᵉ lᵉ) → emb-Finᵉ kᵉ lᵉ
pr1ᵉ (reduce-emb-Finᵉ kᵉ lᵉ fᵉ) = map-reduce-emb-Finᵉ kᵉ lᵉ fᵉ
pr2ᵉ (reduce-emb-Finᵉ kᵉ lᵉ fᵉ) = is-emb-map-reduce-emb-Finᵉ kᵉ lᵉ fᵉ
```

## To do

-ᵉ Anyᵉ embeddingᵉ fromᵉ `Finᵉ k`ᵉ intoᵉ itselfᵉ isᵉ surjectiveᵉ