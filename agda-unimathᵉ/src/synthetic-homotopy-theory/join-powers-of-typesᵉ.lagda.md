# Join powers of types

```agda
module synthetic-homotopy-theory.join-powers-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.empty-typesᵉ
open import foundation.iterating-functionsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.joins-of-typesᵉ
```

</details>

## Idea

Theᵉ `n`-thᵉ **joinᵉ power**ᵉ ofᵉ aᵉ typeᵉ `A`ᵉ isᵉ definedᵉ byᵉ takingᵉ theᵉ
[`n`-fold](foundation.iterating-functions.mdᵉ)
[join](synthetic-homotopy-theory.joins-of-types.mdᵉ) ofᵉ `A`ᵉ with itself.ᵉ

## Definitions

### Join powers of types

```agda
join-powerᵉ : {l1ᵉ : Level} → ℕᵉ → UUᵉ l1ᵉ → UUᵉ l1ᵉ
join-powerᵉ nᵉ Aᵉ = iterateᵉ nᵉ (joinᵉ Aᵉ) (raise-emptyᵉ _)
```

### Join powers of type families

```agda
join-power-family-of-typesᵉ :
  {l1ᵉ l2ᵉ : Level} → ℕᵉ → {Aᵉ : UUᵉ l1ᵉ} → (Aᵉ → UUᵉ l2ᵉ) → (Aᵉ → UUᵉ l2ᵉ)
join-power-family-of-typesᵉ nᵉ Bᵉ aᵉ = join-powerᵉ nᵉ (Bᵉ aᵉ)
```