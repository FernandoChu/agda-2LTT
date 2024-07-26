# Decidable propositions

```agda
module univalent-combinatorics.decidable-propositionsᵉ where

open import foundation.decidable-propositionsᵉ public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

### Propositions have countings if and only if they are decidable

```agda
is-decidable-countᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → countᵉ Xᵉ → is-decidableᵉ Xᵉ
is-decidable-countᵉ (pairᵉ zero-ℕᵉ eᵉ) =
  inrᵉ (is-empty-is-zero-number-of-elements-countᵉ (pairᵉ zero-ℕᵉ eᵉ) reflᵉ)
is-decidable-countᵉ (pairᵉ (succ-ℕᵉ kᵉ) eᵉ) =
  inlᵉ (map-equivᵉ eᵉ (zero-Finᵉ kᵉ))

count-is-decidable-is-propᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-propᵉ Aᵉ → is-decidableᵉ Aᵉ → countᵉ Aᵉ
count-is-decidable-is-propᵉ Hᵉ (inlᵉ xᵉ) =
  count-is-contrᵉ (is-proof-irrelevant-is-propᵉ Hᵉ xᵉ)
count-is-decidable-is-propᵉ Hᵉ (inrᵉ fᵉ) = count-is-emptyᵉ fᵉ

count-Decidable-Propᵉ :
  {l1ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) →
  is-decidableᵉ (type-Propᵉ Pᵉ) → countᵉ (type-Propᵉ Pᵉ)
count-Decidable-Propᵉ Pᵉ (inlᵉ pᵉ) =
  count-is-contrᵉ (is-proof-irrelevant-is-propᵉ (is-prop-type-Propᵉ Pᵉ) pᵉ)
count-Decidable-Propᵉ Pᵉ (inrᵉ fᵉ) = count-is-emptyᵉ fᵉ
```

### We can count the elements of an identity type of a type that has decidable equality

```agda
cases-count-eqᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (dᵉ : has-decidable-equalityᵉ Xᵉ) {xᵉ yᵉ : Xᵉ}
  (eᵉ : is-decidableᵉ (Idᵉ xᵉ yᵉ)) → countᵉ (Idᵉ xᵉ yᵉ)
cases-count-eqᵉ dᵉ {xᵉ} {yᵉ} (inlᵉ pᵉ) =
  count-is-contrᵉ
    ( is-proof-irrelevant-is-propᵉ (is-set-has-decidable-equalityᵉ dᵉ xᵉ yᵉ) pᵉ)
cases-count-eqᵉ dᵉ (inrᵉ fᵉ) =
  count-is-emptyᵉ fᵉ

count-eqᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → has-decidable-equalityᵉ Xᵉ → (xᵉ yᵉ : Xᵉ) → countᵉ (Idᵉ xᵉ yᵉ)
count-eqᵉ dᵉ xᵉ yᵉ = cases-count-eqᵉ dᵉ (dᵉ xᵉ yᵉ)

cases-number-of-elements-count-eq'ᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Xᵉ} →
  is-decidableᵉ (Idᵉ xᵉ yᵉ) → ℕᵉ
cases-number-of-elements-count-eq'ᵉ (inlᵉ pᵉ) = 1
cases-number-of-elements-count-eq'ᵉ (inrᵉ fᵉ) = 0

number-of-elements-count-eq'ᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (dᵉ : has-decidable-equalityᵉ Xᵉ) (xᵉ yᵉ : Xᵉ) → ℕᵉ
number-of-elements-count-eq'ᵉ dᵉ xᵉ yᵉ =
  cases-number-of-elements-count-eq'ᵉ (dᵉ xᵉ yᵉ)

cases-number-of-elements-count-eqᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (dᵉ : has-decidable-equalityᵉ Xᵉ) {xᵉ yᵉ : Xᵉ}
  (eᵉ : is-decidableᵉ (Idᵉ xᵉ yᵉ)) →
  Idᵉ
    ( number-of-elements-countᵉ (cases-count-eqᵉ dᵉ eᵉ))
    ( cases-number-of-elements-count-eq'ᵉ eᵉ)
cases-number-of-elements-count-eqᵉ dᵉ (inlᵉ pᵉ) = reflᵉ
cases-number-of-elements-count-eqᵉ dᵉ (inrᵉ fᵉ) = reflᵉ

abstract
  number-of-elements-count-eqᵉ :
    {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (dᵉ : has-decidable-equalityᵉ Xᵉ) (xᵉ yᵉ : Xᵉ) →
    Idᵉ ( number-of-elements-countᵉ (count-eqᵉ dᵉ xᵉ yᵉ))
      ( number-of-elements-count-eq'ᵉ dᵉ xᵉ yᵉ)
  number-of-elements-count-eqᵉ dᵉ xᵉ yᵉ =
    cases-number-of-elements-count-eqᵉ dᵉ (dᵉ xᵉ yᵉ)
```