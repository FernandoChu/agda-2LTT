# Large semigroups

```agda
module group-theory.large-semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.semigroupsᵉ
```

</details>

## Idea

Aᵉ **largeᵉ semigroup**ᵉ with universeᵉ indexingᵉ functionᵉ `αᵉ : Level → Level`ᵉ
consistsᵉ ofᵉ:

-ᵉ Forᵉ eachᵉ universeᵉ levelᵉ `l`ᵉ aᵉ setᵉ `Xᵉ lᵉ : UUᵉ (αᵉ l)`ᵉ
-ᵉ Forᵉ anyᵉ twoᵉ universeᵉ levelsᵉ `l1`ᵉ andᵉ `l2`ᵉ aᵉ binaryᵉ operationᵉ
  `μᵉ l1ᵉ l2ᵉ : Xᵉ l1ᵉ → Xᵉ l2ᵉ → Xᵉ (l1ᵉ ⊔ l2)`ᵉ satisfyingᵉ theᵉ followingᵉ associativityᵉ
  lawᵉ:

```text
  μᵉ (l1ᵉ ⊔ l2ᵉ) l3ᵉ (μᵉ l1ᵉ l2ᵉ xᵉ yᵉ) zᵉ ＝ᵉ μᵉ l1ᵉ (l2ᵉ ⊔ l3ᵉ) xᵉ (μᵉ l2ᵉ l3ᵉ yᵉ z).ᵉ
```

## Definitions

```agda
record Large-Semigroupᵉ (αᵉ : Level → Level) : UUωᵉ where
  constructor
    make-Large-Semigroupᵉ
  field
    set-Large-Semigroupᵉ :
      (lᵉ : Level) → Setᵉ (αᵉ lᵉ)
    mul-Large-Semigroupᵉ :
      {l1ᵉ l2ᵉ : Level} →
      type-Setᵉ (set-Large-Semigroupᵉ l1ᵉ) →
      type-Setᵉ (set-Large-Semigroupᵉ l2ᵉ) →
      type-Setᵉ (set-Large-Semigroupᵉ (l1ᵉ ⊔ l2ᵉ))
    associative-mul-Large-Semigroupᵉ :
      {l1ᵉ l2ᵉ l3ᵉ : Level}
      (xᵉ : type-Setᵉ (set-Large-Semigroupᵉ l1ᵉ))
      (yᵉ : type-Setᵉ (set-Large-Semigroupᵉ l2ᵉ))
      (zᵉ : type-Setᵉ (set-Large-Semigroupᵉ l3ᵉ)) →
      mul-Large-Semigroupᵉ (mul-Large-Semigroupᵉ xᵉ yᵉ) zᵉ ＝ᵉ
      mul-Large-Semigroupᵉ xᵉ (mul-Large-Semigroupᵉ yᵉ zᵉ)

open Large-Semigroupᵉ public

module _
  {αᵉ : Level → Level} (Gᵉ : Large-Semigroupᵉ αᵉ)
  where

  type-Large-Semigroupᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)
  type-Large-Semigroupᵉ lᵉ = type-Setᵉ (set-Large-Semigroupᵉ Gᵉ lᵉ)

  is-set-type-Large-Semigroupᵉ :
    {lᵉ : Level} → is-setᵉ (type-Large-Semigroupᵉ lᵉ)
  is-set-type-Large-Semigroupᵉ = is-set-type-Setᵉ (set-Large-Semigroupᵉ Gᵉ _)
```

### Small semigroups from large semigroups

```agda
module _
  {αᵉ : Level → Level} (Gᵉ : Large-Semigroupᵉ αᵉ)
  where

  semigroup-Large-Semigroupᵉ : (lᵉ : Level) → Semigroupᵉ (αᵉ lᵉ)
  pr1ᵉ (semigroup-Large-Semigroupᵉ lᵉ) = set-Large-Semigroupᵉ Gᵉ lᵉ
  pr1ᵉ (pr2ᵉ (semigroup-Large-Semigroupᵉ lᵉ)) = mul-Large-Semigroupᵉ Gᵉ
  pr2ᵉ (pr2ᵉ (semigroup-Large-Semigroupᵉ lᵉ)) = associative-mul-Large-Semigroupᵉ Gᵉ
```