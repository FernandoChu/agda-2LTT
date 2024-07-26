# Coinhabited pairs of types

```agda
module foundation.coinhabited-pairs-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.inhabited-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.propositionsᵉ
```

</details>

## Idea

Twoᵉ typesᵉ `A`ᵉ andᵉ `B`ᵉ areᵉ saidᵉ to beᵉ
{{#conceptᵉ "coinhabited"ᵉ Agda=is-coinhabitedᵉ}} ifᵉ `A`ᵉ isᵉ
[inhabited](foundation.inhabited-types.mdᵉ)
[ifᵉ andᵉ onlyᵉ if](foundation.logical-equivalences.mdᵉ) `B`ᵉ is.ᵉ

## Definitions

### The predicate of being coinhabited

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  is-coinhabited-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-coinhabited-Propᵉ = iff-Propᵉ (is-inhabited-Propᵉ Aᵉ) (is-inhabited-Propᵉ Bᵉ)

  is-coinhabitedᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-coinhabitedᵉ = type-Propᵉ is-coinhabited-Propᵉ
```

### Forward and backward implications of coinhabited types

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  forward-implication-is-coinhabitedᵉ :
    is-coinhabitedᵉ Aᵉ Bᵉ → is-inhabitedᵉ Aᵉ → is-inhabitedᵉ Bᵉ
  forward-implication-is-coinhabitedᵉ = forward-implicationᵉ

  forward-implication-is-coinhabited'ᵉ : is-coinhabitedᵉ Aᵉ Bᵉ → Aᵉ → is-inhabitedᵉ Bᵉ
  forward-implication-is-coinhabited'ᵉ eᵉ aᵉ =
    forward-implicationᵉ eᵉ (unit-trunc-Propᵉ aᵉ)

  backward-implication-is-coinhabitedᵉ :
    is-coinhabitedᵉ Aᵉ Bᵉ → is-inhabitedᵉ Bᵉ → is-inhabitedᵉ Aᵉ
  backward-implication-is-coinhabitedᵉ = backward-implicationᵉ

  backward-implication-is-coinhabited'ᵉ : is-coinhabitedᵉ Aᵉ Bᵉ → Bᵉ → is-inhabitedᵉ Aᵉ
  backward-implication-is-coinhabited'ᵉ eᵉ bᵉ =
    backward-implicationᵉ eᵉ (unit-trunc-Propᵉ bᵉ)
```

### Every type is coinhabited with itself

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  is-reflexive-is-coinhabitedᵉ : is-coinhabitedᵉ Aᵉ Aᵉ
  is-reflexive-is-coinhabitedᵉ = id-iffᵉ
```

### Coinhabitedness is a transitive relation

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  is-transitive-is-coinhabitedᵉ :
    is-coinhabitedᵉ Bᵉ Cᵉ → is-coinhabitedᵉ Aᵉ Bᵉ → is-coinhabitedᵉ Aᵉ Cᵉ
  is-transitive-is-coinhabitedᵉ = _∘iffᵉ_
```

### Coinhabitedness is a symmetric relation

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-symmetric-is-coinhabitedᵉ : is-coinhabitedᵉ Aᵉ Bᵉ → is-coinhabitedᵉ Bᵉ Aᵉ
  is-symmetric-is-coinhabitedᵉ = inv-iffᵉ
```

## See also

-ᵉ [Mereᵉ logicalᵉ equivalenceᵉ ofᵉ types](foundation.mere-logical-equivalences.mdᵉ)
  isᵉ aᵉ relatedᵉ butᵉ strongerᵉ notionᵉ thanᵉ coinhabitedness.ᵉ