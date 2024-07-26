# Partial sequences

```agda
module foundation.partial-sequencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.partial-functionsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.propositionsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "partialᵉ sequence"ᵉ Agda=partial-sequenceᵉ}} ofᵉ elementsᵉ ofᵉ aᵉ typeᵉ
`A`ᵉ isᵉ aᵉ [partialᵉ function](foundation.partial-functions.mdᵉ) fromᵉ `ℕ`ᵉ to `A`.ᵉ Inᵉ
otherᵉ words,ᵉ aᵉ partialᵉ sequenceᵉ isᵉ aᵉ mapᵉ

```text
  ℕᵉ → Σᵉ (Pᵉ : Prop),ᵉ (Pᵉ → Aᵉ)
```

fromᵉ `ℕ`ᵉ intoᵉ theᵉ typeᵉ ofᵉ [partialᵉ elements](foundation.partial-elements.mdᵉ) ofᵉ
`A`.ᵉ

## Definitions

### Partial sequences

```agda
partial-sequenceᵉ : {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
partial-sequenceᵉ l2ᵉ Aᵉ = partial-functionᵉ l2ᵉ ℕᵉ Aᵉ
```

### Defined elements of partial sequences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : partial-sequenceᵉ l2ᵉ Aᵉ)
  where

  is-defined-prop-partial-sequenceᵉ : ℕᵉ → Propᵉ l2ᵉ
  is-defined-prop-partial-sequenceᵉ = is-defined-prop-partial-functionᵉ aᵉ

  is-defined-partial-sequenceᵉ : ℕᵉ → UUᵉ l2ᵉ
  is-defined-partial-sequenceᵉ = is-defined-partial-functionᵉ aᵉ
```