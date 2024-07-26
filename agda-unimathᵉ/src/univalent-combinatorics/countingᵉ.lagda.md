# Counting in type theory

```agda
module univalent-combinatorics.countingᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ elementsᵉ ofᵉ aᵉ typeᵉ `X`ᵉ canᵉ beᵉ countedᵉ byᵉ establishingᵉ anᵉ equivalenceᵉ
`Finᵉ nᵉ ≃ᵉ X`.ᵉ

## Definition

```agda
countᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
countᵉ Xᵉ = Σᵉ ℕᵉ (λ kᵉ → Finᵉ kᵉ ≃ᵉ Xᵉ)

module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Xᵉ)
  where

  number-of-elements-countᵉ : ℕᵉ
  number-of-elements-countᵉ = pr1ᵉ eᵉ

  equiv-countᵉ : Finᵉ number-of-elements-countᵉ ≃ᵉ Xᵉ
  equiv-countᵉ = pr2ᵉ eᵉ

  map-equiv-countᵉ : Finᵉ number-of-elements-countᵉ → Xᵉ
  map-equiv-countᵉ = map-equivᵉ equiv-countᵉ

  map-inv-equiv-countᵉ : Xᵉ → Finᵉ number-of-elements-countᵉ
  map-inv-equiv-countᵉ = map-inv-equivᵉ equiv-countᵉ

  is-section-map-inv-equiv-countᵉ : (map-equiv-countᵉ ∘ᵉ map-inv-equiv-countᵉ) ~ᵉ idᵉ
  is-section-map-inv-equiv-countᵉ = is-section-map-inv-equivᵉ equiv-countᵉ

  is-retraction-map-inv-equiv-countᵉ :
    (map-inv-equiv-countᵉ ∘ᵉ map-equiv-countᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-equiv-countᵉ = is-retraction-map-inv-equivᵉ equiv-countᵉ

  inv-equiv-countᵉ : Xᵉ ≃ᵉ Finᵉ number-of-elements-countᵉ
  inv-equiv-countᵉ = inv-equivᵉ equiv-countᵉ

  is-set-countᵉ : is-setᵉ Xᵉ
  is-set-countᵉ =
    is-set-equiv'ᵉ
      ( Finᵉ number-of-elements-countᵉ)
      ( equiv-countᵉ)
      ( is-set-Finᵉ number-of-elements-countᵉ)
```

## Properties

### The elements of the standard finite types can be counted

```agda
count-Finᵉ : (kᵉ : ℕᵉ) → countᵉ (Finᵉ kᵉ)
pr1ᵉ (count-Finᵉ kᵉ) = kᵉ
pr2ᵉ (count-Finᵉ kᵉ) = id-equivᵉ
```

### Types equipped with countings are closed under equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  where

  abstract
    equiv-count-equivᵉ :
      (eᵉ : Xᵉ ≃ᵉ Yᵉ) (fᵉ : countᵉ Xᵉ) → Finᵉ (number-of-elements-countᵉ fᵉ) ≃ᵉ Yᵉ
    equiv-count-equivᵉ eᵉ fᵉ = eᵉ ∘eᵉ (equiv-countᵉ fᵉ)

  count-equivᵉ : Xᵉ ≃ᵉ Yᵉ → countᵉ Xᵉ → countᵉ Yᵉ
  pr1ᵉ (count-equivᵉ eᵉ fᵉ) = number-of-elements-countᵉ fᵉ
  pr2ᵉ (count-equivᵉ eᵉ fᵉ) = equiv-count-equivᵉ eᵉ fᵉ

  abstract
    equiv-count-equiv'ᵉ :
      (eᵉ : Xᵉ ≃ᵉ Yᵉ) (fᵉ : countᵉ Yᵉ) → Finᵉ (number-of-elements-countᵉ fᵉ) ≃ᵉ Xᵉ
    equiv-count-equiv'ᵉ eᵉ fᵉ = inv-equivᵉ eᵉ ∘eᵉ (equiv-countᵉ fᵉ)

  count-equiv'ᵉ : Xᵉ ≃ᵉ Yᵉ → countᵉ Yᵉ → countᵉ Xᵉ
  pr1ᵉ (count-equiv'ᵉ eᵉ fᵉ) = number-of-elements-countᵉ fᵉ
  pr2ᵉ (count-equiv'ᵉ eᵉ fᵉ) = equiv-count-equiv'ᵉ eᵉ fᵉ

  count-is-equivᵉ : {fᵉ : Xᵉ → Yᵉ} → is-equivᵉ fᵉ → countᵉ Xᵉ → countᵉ Yᵉ
  count-is-equivᵉ Hᵉ = count-equivᵉ (pairᵉ _ Hᵉ)

  count-is-equiv'ᵉ :
    {fᵉ : Xᵉ → Yᵉ} → is-equivᵉ fᵉ → countᵉ Yᵉ → countᵉ Xᵉ
  count-is-equiv'ᵉ Hᵉ = count-equiv'ᵉ (pairᵉ _ Hᵉ)
```

### A type as 0 elements if and only if it is empty

```agda
abstract
  is-empty-is-zero-number-of-elements-countᵉ :
    {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Xᵉ) →
    is-zero-ℕᵉ (number-of-elements-countᵉ eᵉ) → is-emptyᵉ Xᵉ
  is-empty-is-zero-number-of-elements-countᵉ (pairᵉ .zero-ℕᵉ eᵉ) reflᵉ xᵉ =
    map-inv-equivᵉ eᵉ xᵉ

abstract
  is-zero-number-of-elements-count-is-emptyᵉ :
    {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Xᵉ) →
    is-emptyᵉ Xᵉ → is-zero-ℕᵉ (number-of-elements-countᵉ eᵉ)
  is-zero-number-of-elements-count-is-emptyᵉ (pairᵉ zero-ℕᵉ eᵉ) Hᵉ = reflᵉ
  is-zero-number-of-elements-count-is-emptyᵉ (pairᵉ (succ-ℕᵉ kᵉ) eᵉ) Hᵉ =
    ex-falsoᵉ (Hᵉ (map-equivᵉ eᵉ (zero-Finᵉ kᵉ)))

count-is-emptyᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → is-emptyᵉ Xᵉ → countᵉ Xᵉ
pr1ᵉ (count-is-emptyᵉ Hᵉ) = zero-ℕᵉ
pr2ᵉ (count-is-emptyᵉ Hᵉ) = inv-equivᵉ (pairᵉ Hᵉ (is-equiv-is-empty'ᵉ Hᵉ))

count-emptyᵉ : countᵉ emptyᵉ
count-emptyᵉ = count-Finᵉ zero-ℕᵉ
```

### A type has 1 element if and only if it is contractible

```agda
count-is-contrᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → is-contrᵉ Xᵉ → countᵉ Xᵉ
pr1ᵉ (count-is-contrᵉ Hᵉ) = 1
pr2ᵉ (count-is-contrᵉ Hᵉ) = equiv-is-contrᵉ is-contr-Fin-one-ℕᵉ Hᵉ

abstract
  is-contr-is-one-number-of-elements-countᵉ :
    {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Xᵉ) →
    is-one-ℕᵉ (number-of-elements-countᵉ eᵉ) → is-contrᵉ Xᵉ
  is-contr-is-one-number-of-elements-countᵉ (pairᵉ .(succ-ℕᵉ zero-ℕᵉ) eᵉ) reflᵉ =
    is-contr-equiv'ᵉ (Finᵉ 1ᵉ) eᵉ is-contr-Fin-one-ℕᵉ

abstract
  is-one-number-of-elements-count-is-contrᵉ :
    {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Xᵉ) →
    is-contrᵉ Xᵉ → is-one-ℕᵉ (number-of-elements-countᵉ eᵉ)
  is-one-number-of-elements-count-is-contrᵉ (pairᵉ zero-ℕᵉ eᵉ) Hᵉ =
    ex-falsoᵉ (map-inv-equivᵉ eᵉ (centerᵉ Hᵉ))
  is-one-number-of-elements-count-is-contrᵉ (pairᵉ (succ-ℕᵉ zero-ℕᵉ) eᵉ) Hᵉ =
    reflᵉ
  is-one-number-of-elements-count-is-contrᵉ (pairᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) eᵉ) Hᵉ =
    ex-falsoᵉ
      ( Eq-Fin-eqᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ))
        ( is-injective-equivᵉ eᵉ
          ( eq-is-contr'ᵉ Hᵉ
            ( map-equivᵉ eᵉ (zero-Finᵉ (succ-ℕᵉ kᵉ)))
            ( map-equivᵉ eᵉ (neg-one-Finᵉ (succ-ℕᵉ kᵉ))))))

count-unitᵉ : countᵉ unitᵉ
count-unitᵉ = count-is-contrᵉ is-contr-unitᵉ
```

### Types with a count have decidable equality

```agda
has-decidable-equality-countᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → countᵉ Xᵉ → has-decidable-equalityᵉ Xᵉ
has-decidable-equality-countᵉ (pairᵉ kᵉ eᵉ) =
  has-decidable-equality-equiv'ᵉ eᵉ (has-decidable-equality-Finᵉ kᵉ)
```

### This with a count are either inhabited or empty

```agda
is-inhabited-or-empty-countᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → countᵉ Aᵉ → is-inhabited-or-emptyᵉ Aᵉ
is-inhabited-or-empty-countᵉ (pairᵉ zero-ℕᵉ eᵉ) =
  inrᵉ (is-empty-is-zero-number-of-elements-countᵉ (pairᵉ zero-ℕᵉ eᵉ) reflᵉ)
is-inhabited-or-empty-countᵉ (pairᵉ (succ-ℕᵉ kᵉ) eᵉ) =
  inlᵉ (unit-trunc-Propᵉ (map-equivᵉ eᵉ (zero-Finᵉ kᵉ)))
```

### If the elements of a type can be counted, then the elements of its propositional truncation can be counted

```agda
count-type-trunc-Propᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → countᵉ Aᵉ → countᵉ (type-trunc-Propᵉ Aᵉ)
count-type-trunc-Propᵉ (pairᵉ zero-ℕᵉ eᵉ) =
  count-is-emptyᵉ
    ( is-empty-type-trunc-Propᵉ
      ( is-empty-is-zero-number-of-elements-countᵉ (pairᵉ zero-ℕᵉ eᵉ) reflᵉ))
count-type-trunc-Propᵉ (pairᵉ (succ-ℕᵉ kᵉ) eᵉ) =
  count-is-contrᵉ
    ( is-proof-irrelevant-is-propᵉ
      ( is-prop-type-trunc-Propᵉ)
      ( unit-trunc-Propᵉ (map-equivᵉ eᵉ (zero-Finᵉ kᵉ))))
```