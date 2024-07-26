# Upper sets of large posets

```agda
module order-theory.upper-sets-large-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.large-subposetsᵉ
```

</details>

## Idea

Anᵉ **upperᵉ set**ᵉ orᵉ **upwardsᵉ closedᵉ set**ᵉ in aᵉ
[largeᵉ poset](order-theory.large-posets.mdᵉ) isᵉ aᵉ
[largeᵉ subposet](order-theory.large-subposets.mdᵉ) thatᵉ isᵉ upwardsᵉ closed,ᵉ i.e.,ᵉ
thatᵉ satisfiesᵉ theᵉ conditionᵉ thatᵉ

```text
  ∀ᵉ (xᵉ yᵉ : P),ᵉ (xᵉ ≤ᵉ yᵉ) → xᵉ ∈ᵉ Sᵉ → yᵉ ∈ᵉ S.ᵉ
```

## Definitions

### The predicate of being an upper set

```agda
module _
  {αᵉ γᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ) (Sᵉ : Large-Subposetᵉ γᵉ Pᵉ)
  where

  is-upper-set-Large-Subposetᵉ : UUωᵉ
  is-upper-set-Large-Subposetᵉ =
    {l1ᵉ l2ᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ) →
    leq-Large-Posetᵉ Pᵉ xᵉ yᵉ →
    is-in-Large-Subposetᵉ Pᵉ Sᵉ xᵉ → is-in-Large-Subposetᵉ Pᵉ Sᵉ yᵉ
```

### Upper sets of a large poset

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (γᵉ : Level → Level)
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  where

  record
    upper-set-Large-Posetᵉ : UUωᵉ
    where
    field
      large-subposet-upper-set-Large-Posetᵉ :
        Large-Subposetᵉ γᵉ Pᵉ
      is-upper-set-upper-set-Large-Posetᵉ :
        is-upper-set-Large-Subposetᵉ Pᵉ large-subposet-upper-set-Large-Posetᵉ

  open upper-set-Large-Posetᵉ public
```

## See also

-ᵉ [Lowerᵉ sets](order-theory.lower-sets-large-posets.mdᵉ)
-ᵉ [Principalᵉ upperᵉ sets](order-theory.principal-upper-sets-large-posets.mdᵉ)