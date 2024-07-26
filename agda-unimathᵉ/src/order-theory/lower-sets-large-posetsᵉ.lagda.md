# Lower sets in large posets

```agda
module order-theory.lower-sets-large-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.large-subposetsᵉ
```

</details>

## Idea

Aᵉ **lowerᵉ set**ᵉ orᵉ **downwardsᵉ closedᵉ set**ᵉ in aᵉ
[largeᵉ poset](order-theory.large-posets.mdᵉ) isᵉ aᵉ
[largeᵉ subposet](order-theory.large-subposets.mdᵉ) thatᵉ isᵉ downwardsᵉ closed,ᵉ
i.e.,ᵉ thatᵉ satisfiesᵉ theᵉ conditionᵉ thatᵉ

```text
  ∀ᵉ (xᵉ yᵉ : P),ᵉ (yᵉ ≤ᵉ xᵉ) → xᵉ ∈ᵉ Sᵉ → yᵉ ∈ᵉ S.ᵉ
```

## Definitions

### The predicate of being a lower set

```agda
module _
  {αᵉ γᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ) (Sᵉ : Large-Subposetᵉ γᵉ Pᵉ)
  where

  is-lower-set-Large-Subposetᵉ : UUωᵉ
  is-lower-set-Large-Subposetᵉ =
    {l1ᵉ l2ᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ) →
    leq-Large-Posetᵉ Pᵉ yᵉ xᵉ →
    is-in-Large-Subposetᵉ Pᵉ Sᵉ xᵉ → is-in-Large-Subposetᵉ Pᵉ Sᵉ yᵉ
```

### Lower sets of a large poset

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (γᵉ : Level → Level)
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  where

  record
    lower-set-Large-Posetᵉ : UUωᵉ
    where
    field
      large-subposet-lower-set-Large-Posetᵉ :
        Large-Subposetᵉ γᵉ Pᵉ
      is-lower-set-lower-set-Large-Posetᵉ :
        is-lower-set-Large-Subposetᵉ Pᵉ large-subposet-lower-set-Large-Posetᵉ

  open lower-set-Large-Posetᵉ public

module _
  {αᵉ γᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ) (Lᵉ : lower-set-Large-Posetᵉ γᵉ Pᵉ)
  where

  is-in-lower-set-Large-Posetᵉ :
    {lᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ lᵉ) → UUᵉ (γᵉ lᵉ)
  is-in-lower-set-Large-Posetᵉ =
    is-in-Large-Subposetᵉ Pᵉ (large-subposet-lower-set-Large-Posetᵉ Lᵉ)
```

## See also

-ᵉ [Principalᵉ lowerᵉ sets](order-theory.principal-lower-sets-large-posets.mdᵉ)
-ᵉ [Upperᵉ sets](order-theory.upper-sets-large-posets.mdᵉ)