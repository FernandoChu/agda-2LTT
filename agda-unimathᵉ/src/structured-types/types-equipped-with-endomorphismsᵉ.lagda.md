# Types equipped with endomorphisms

```agda
module structured-types.types-equipped-with-endomorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.endomorphismsᵉ
open import foundation.function-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ typeᵉ equippedᵉ with anᵉ endomorphismᵉ consistsᵉ ofᵉ aᵉ typeᵉ `A`ᵉ equippedᵉ with aᵉ mapᵉ
`Aᵉ → A`.ᵉ

## Definitions

### Types equipped with endomorphisms

```agda
Type-With-Endomorphismᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Type-With-Endomorphismᵉ lᵉ = Σᵉ (UUᵉ lᵉ) endoᵉ

module _
  {lᵉ : Level} (Xᵉ : Type-With-Endomorphismᵉ lᵉ)
  where

  type-Type-With-Endomorphismᵉ : UUᵉ lᵉ
  type-Type-With-Endomorphismᵉ = pr1ᵉ Xᵉ

  endomorphism-Type-With-Endomorphismᵉ :
    type-Type-With-Endomorphismᵉ → type-Type-With-Endomorphismᵉ
  endomorphism-Type-With-Endomorphismᵉ = pr2ᵉ Xᵉ
```

## Example

### Unit type equipped with endomorphisms

```agda
trivial-Type-With-Endomorphismᵉ : {lᵉ : Level} → Type-With-Endomorphismᵉ lᵉ
pr1ᵉ (trivial-Type-With-Endomorphismᵉ {lᵉ}) = raise-unitᵉ lᵉ
pr2ᵉ trivial-Type-With-Endomorphismᵉ = idᵉ
```