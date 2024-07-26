# Injective maps

```agda
module univalent-combinatorics.embeddingsᵉ where

open import foundation.embeddingsᵉ public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.decidable-embeddingsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.injective-mapsᵉ
open import univalent-combinatorics.retracts-of-finite-typesᵉ
```

</details>

## Idea

Embeddingsᵉ in theᵉ presenceᵉ ofᵉ finiteᵉ typesᵉ enjoyᵉ furtherᵉ properties.ᵉ

## Properties

```agda
is-decidable-is-emb-is-finiteᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-finiteᵉ Aᵉ → is-finiteᵉ Bᵉ → is-decidableᵉ (is-embᵉ fᵉ)
is-decidable-is-emb-is-finiteᵉ fᵉ HAᵉ HBᵉ =
  is-decidable-iffᵉ
    ( is-emb-is-injectiveᵉ (is-set-is-finiteᵉ HBᵉ))
    ( is-injective-is-embᵉ)
    ( is-decidable-is-injective-is-finiteᵉ fᵉ HAᵉ HBᵉ)
```

### If `A` can be count, then `trunc-Prop A ↪ᵈ A`

```agda
decidable-emb-trunc-Prop-countᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
  countᵉ Aᵉ → type-trunc-Propᵉ (Aᵉ) ↪ᵈᵉ Aᵉ
decidable-emb-trunc-Prop-countᵉ (zero-ℕᵉ ,ᵉ empty-Aᵉ) =
  decidable-emb-is-emptyᵉ (is-empty-type-trunc-Propᵉ ( map-inv-equivᵉ empty-Aᵉ))
decidable-emb-trunc-Prop-countᵉ {Aᵉ = Aᵉ} (succ-ℕᵉ nᵉ ,ᵉ eᵉ) =
  decidable-emb-retract-countᵉ
    ( succ-ℕᵉ nᵉ ,ᵉ eᵉ)
    ( λ _ → map-equivᵉ eᵉ (inrᵉ starᵉ))
    ((λ xᵉ → unit-trunc-Propᵉ xᵉ) ,ᵉ (λ xᵉ → eq-is-propᵉ is-prop-type-trunc-Propᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Pᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  decidable-emb-tot-trunc-Prop-countᵉ :
    ((aᵉ : Aᵉ) → countᵉ (Pᵉ aᵉ)) → (Σᵉ Aᵉ (λ aᵉ → type-trunc-Propᵉ (Pᵉ aᵉ)) ↪ᵈᵉ Σᵉ Aᵉ Pᵉ)
  decidable-emb-tot-trunc-Prop-countᵉ cᵉ =
    decidable-emb-totᵉ ( λ aᵉ → decidable-emb-trunc-Prop-countᵉ (cᵉ aᵉ))
```