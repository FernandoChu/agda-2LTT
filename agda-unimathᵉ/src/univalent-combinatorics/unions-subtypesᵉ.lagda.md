# Unions of finite subtypes

```agda
module univalent-combinatorics.unions-subtypesᵉ where

open import foundation.unions-subtypesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-equalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.coproduct-typesᵉ
open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.counting-decidable-subtypesᵉ
open import univalent-combinatorics.counting-dependent-pair-typesᵉ
open import univalent-combinatorics.embeddingsᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Properties

### If `A` has decidable equalities, `P` and `Q` are subtypes of A equipped with a counting, then `P ∪ Q` is equipped with a counting

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : subtypeᵉ l2ᵉ Aᵉ) (Qᵉ : subtypeᵉ l3ᵉ Aᵉ)
  where

  count-union-subtypes-count-has-decidable-equalitiesᵉ :
    has-decidable-equalityᵉ Aᵉ → countᵉ (type-subtypeᵉ Pᵉ) →
    countᵉ (type-subtypeᵉ Qᵉ) → countᵉ (type-subtypeᵉ (union-subtypeᵉ Pᵉ Qᵉ))
  count-union-subtypes-count-has-decidable-equalitiesᵉ dec-Aᵉ count-Pᵉ count-Qᵉ =
    count-decidable-embᵉ
      ( decidable-emb-tot-trunc-Prop-countᵉ
        ( count-fiber-count-Σᵉ dec-Aᵉ (count-Σ-coproductᵉ count-Pᵉ count-Qᵉ)))
      ( count-Σ-coproductᵉ count-Pᵉ count-Qᵉ)
```

### If `A` has decidable equalities and `P` and `Q` are both finite, then `P ∪ Q` is also finite

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : subtypeᵉ l2ᵉ Aᵉ) (Qᵉ : subtypeᵉ l3ᵉ Aᵉ)
  where

  finite-union-subtypes-finite-has-decidable-equalitiesᵉ :
    has-decidable-equalityᵉ Aᵉ → is-finiteᵉ (type-subtypeᵉ Pᵉ) →
    is-finiteᵉ (type-subtypeᵉ Qᵉ) → is-finiteᵉ (type-subtypeᵉ (union-subtypeᵉ Pᵉ Qᵉ))
  finite-union-subtypes-finite-has-decidable-equalitiesᵉ dec-Aᵉ fin-Pᵉ fin-Qᵉ =
    apply-twice-universal-property-trunc-Propᵉ
      ( fin-Pᵉ)
      ( fin-Qᵉ)
      ( is-finite-Propᵉ (type-subtypeᵉ (union-subtypeᵉ Pᵉ Qᵉ)))
      ( λ count-Pᵉ count-Qᵉ →
        unit-trunc-Propᵉ
          ( count-union-subtypes-count-has-decidable-equalitiesᵉ
            Pᵉ
            Qᵉ
            dec-Aᵉ
            count-Pᵉ
            count-Qᵉ))
```