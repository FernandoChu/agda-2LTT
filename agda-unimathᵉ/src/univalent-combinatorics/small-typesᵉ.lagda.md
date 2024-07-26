# Small types

```agda
module univalent-combinatorics.small-typesᵉ where

open import foundation.small-typesᵉ public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Propositions

Everyᵉ finiteᵉ typeᵉ isᵉ small.ᵉ

```agda
is-small-Finᵉ :
  (lᵉ : Level) → (kᵉ : ℕᵉ) → is-smallᵉ lᵉ (Finᵉ kᵉ)
pr1ᵉ (is-small-Finᵉ lᵉ kᵉ) = raise-Finᵉ lᵉ kᵉ
pr2ᵉ (is-small-Finᵉ lᵉ kᵉ) = compute-raise-Finᵉ lᵉ kᵉ

is-small-is-finiteᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → (Aᵉ : 𝔽ᵉ l1ᵉ) → is-smallᵉ l2ᵉ (type-𝔽ᵉ Aᵉ)
is-small-is-finiteᵉ l2ᵉ Aᵉ =
  apply-universal-property-trunc-Propᵉ
    ( is-finite-type-𝔽ᵉ Aᵉ)
    ( is-smallᵉ l2ᵉ (type-𝔽ᵉ Aᵉ) ,ᵉ is-prop-is-smallᵉ l2ᵉ (type-𝔽ᵉ Aᵉ))
    ( λ pᵉ → is-small-equiv'ᵉ (Finᵉ (pr1ᵉ pᵉ)) (pr2ᵉ pᵉ) (is-small-Finᵉ l2ᵉ (pr1ᵉ pᵉ)))
```