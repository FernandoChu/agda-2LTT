# Species of types

```agda
module species.species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ
```

</details>

### Idea

Aᵉ **speciesᵉ ofᵉ types**ᵉ isᵉ definedᵉ to beᵉ aᵉ mapᵉ fromᵉ aᵉ universeᵉ to aᵉ universe.ᵉ

## Definitions

### Species of types

```agda
species-typesᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
species-typesᵉ l1ᵉ l2ᵉ = UUᵉ l1ᵉ → UUᵉ l2ᵉ
```

### The predicate that a species preserves cartesian products

```agda
preserves-product-species-typesᵉ :
  {l1ᵉ l2ᵉ : Level}
  (Sᵉ : species-typesᵉ l1ᵉ l2ᵉ) →
  UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
preserves-product-species-typesᵉ {l1ᵉ} Sᵉ = (Xᵉ Yᵉ : UUᵉ l1ᵉ) → Sᵉ (Xᵉ ×ᵉ Yᵉ) ≃ᵉ (Sᵉ Xᵉ ×ᵉ Sᵉ Yᵉ)
```

### Transport in species

```agda
tr-species-typesᵉ :
  {l1ᵉ l2ᵉ : Level} (Fᵉ : species-typesᵉ l1ᵉ l2ᵉ) (Xᵉ Yᵉ : UUᵉ l1ᵉ) →
  Xᵉ ≃ᵉ Yᵉ → Fᵉ Xᵉ → Fᵉ Yᵉ
tr-species-typesᵉ Fᵉ Xᵉ Yᵉ eᵉ = trᵉ Fᵉ (eq-equivᵉ eᵉ)
```