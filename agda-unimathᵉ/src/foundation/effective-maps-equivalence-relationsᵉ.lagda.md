# Effective maps for equivalence relations

```agda
module foundation.effective-maps-equivalence-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalence-relationsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Considerᵉ aᵉ typeᵉ `A`ᵉ equippedᵉ with anᵉ equivalenceᵉ relationᵉ `R`,ᵉ andᵉ let
`fᵉ : Aᵉ → X`ᵉ beᵉ aᵉ map.ᵉ Thenᵉ `f`ᵉ isᵉ effectiveᵉ ifᵉ `Rᵉ xᵉ yᵉ ≃ᵉ Idᵉ (fᵉ xᵉ) (fᵉ y)`ᵉ forᵉ allᵉ
`xᵉ yᵉ : A`.ᵉ Ifᵉ `f`ᵉ isᵉ bothᵉ effectiveᵉ andᵉ surjective,ᵉ thenᵉ itᵉ followsᵉ thatᵉ `X`ᵉ
satisfiesᵉ theᵉ universalᵉ propertyᵉ ofᵉ theᵉ quotientᵉ `A/R`.ᵉ

## Definition

### Effective maps

```agda
is-effectiveᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
is-effectiveᵉ {Aᵉ = Aᵉ} Rᵉ fᵉ =
  (xᵉ yᵉ : Aᵉ) → (fᵉ xᵉ ＝ᵉ fᵉ yᵉ) ≃ᵉ sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ
```

### Maps that are effective and surjective

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  is-surjective-and-effectiveᵉ :
    {l3ᵉ : Level} {Bᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-surjective-and-effectiveᵉ fᵉ = is-surjectiveᵉ fᵉ ×ᵉ is-effectiveᵉ Rᵉ fᵉ
```