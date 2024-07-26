# Large subposets

```agda
module order-theory.large-subposetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.large-preordersᵉ
open import order-theory.large-subpreordersᵉ
```

</details>

## Idea

Aᵉ **largeᵉ subposet**ᵉ ofᵉ aᵉ [largeᵉ poset](order-theory.large-posets.mdᵉ) `P`ᵉ
consistsᵉ ofᵉ aᵉ subtypeᵉ `Sᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ → Propᵉ (γᵉ l1)`ᵉ forᵉ eachᵉ
universeᵉ levelᵉ `l1`ᵉ suchᵉ thatᵉ theᵉ implicationᵉ

```text
  ((xᵉ ≤ᵉ yᵉ) ∧ᵉ (yᵉ ≤ᵉ xᵉ)) → (xᵉ ∈ᵉ Sᵉ → yᵉ ∈ᵉ Sᵉ)
```

holdsᵉ forᵉ everyᵉ `xᵉ yᵉ : P`.ᵉ Noteᵉ thatᵉ forᵉ elementsᵉ ofᵉ theᵉ sameᵉ universeᵉ level,ᵉ
thisᵉ isᵉ automaticᵉ byᵉ antisymmetry.ᵉ

## Definition

### The predicate of being closed under similarity

```agda
module _
  {αᵉ γᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ) (Sᵉ : Large-Subpreorderᵉ γᵉ (large-preorder-Large-Posetᵉ Pᵉ))
  where

  is-closed-under-sim-Large-Subpreorderᵉ : UUωᵉ
  is-closed-under-sim-Large-Subpreorderᵉ =
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ) →
    leq-Large-Posetᵉ Pᵉ xᵉ yᵉ → leq-Large-Posetᵉ Pᵉ yᵉ xᵉ →
    is-in-Large-Subpreorderᵉ (large-preorder-Large-Posetᵉ Pᵉ) Sᵉ xᵉ →
    is-in-Large-Subpreorderᵉ (large-preorder-Large-Posetᵉ Pᵉ) Sᵉ yᵉ
```

### Large subposets

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (γᵉ : Level → Level)
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  where

  record
    Large-Subposetᵉ : UUωᵉ
    where
    field
      large-subpreorder-Large-Subposetᵉ :
        Large-Subpreorderᵉ γᵉ (large-preorder-Large-Posetᵉ Pᵉ)
      is-closed-under-sim-Large-Subposetᵉ :
        is-closed-under-sim-Large-Subpreorderᵉ Pᵉ large-subpreorder-Large-Subposetᵉ

  open Large-Subposetᵉ public

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level → Level}
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ) (Sᵉ : Large-Subposetᵉ γᵉ Pᵉ)
  where

  large-preorder-Large-Subposetᵉ :
    Large-Preorderᵉ (λ lᵉ → αᵉ lᵉ ⊔ γᵉ lᵉ) (λ l1ᵉ l2ᵉ → βᵉ l1ᵉ l2ᵉ)
  large-preorder-Large-Subposetᵉ =
    large-preorder-Large-Subpreorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-subpreorder-Large-Subposetᵉ Sᵉ)

  is-in-Large-Subposetᵉ :
    {l1ᵉ : Level} → type-Large-Posetᵉ Pᵉ l1ᵉ → UUᵉ (γᵉ l1ᵉ)
  is-in-Large-Subposetᵉ =
    is-in-Large-Subpreorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-subpreorder-Large-Subposetᵉ Sᵉ)

  type-Large-Subposetᵉ : (l1ᵉ : Level) → UUᵉ (αᵉ l1ᵉ ⊔ γᵉ l1ᵉ)
  type-Large-Subposetᵉ =
    type-Large-Subpreorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-subpreorder-Large-Subposetᵉ Sᵉ)

  leq-prop-Large-Subposetᵉ :
    Large-Relation-Propᵉ βᵉ type-Large-Subposetᵉ
  leq-prop-Large-Subposetᵉ =
    leq-prop-Large-Subpreorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-subpreorder-Large-Subposetᵉ Sᵉ)

  leq-Large-Subposetᵉ :
    Large-Relationᵉ βᵉ type-Large-Subposetᵉ
  leq-Large-Subposetᵉ =
    leq-Large-Subpreorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-subpreorder-Large-Subposetᵉ Sᵉ)

  is-prop-leq-Large-Subposetᵉ :
    is-prop-Large-Relationᵉ type-Large-Subposetᵉ leq-Large-Subposetᵉ
  is-prop-leq-Large-Subposetᵉ =
    is-prop-leq-Large-Subpreorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-subpreorder-Large-Subposetᵉ Sᵉ)

  refl-leq-Large-Subposetᵉ :
    is-reflexive-Large-Relationᵉ type-Large-Subposetᵉ leq-Large-Subposetᵉ
  refl-leq-Large-Subposetᵉ =
    refl-leq-Large-Subpreorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-subpreorder-Large-Subposetᵉ Sᵉ)

  transitive-leq-Large-Subposetᵉ :
    is-transitive-Large-Relationᵉ type-Large-Subposetᵉ leq-Large-Subposetᵉ
  transitive-leq-Large-Subposetᵉ =
    transitive-leq-Large-Subpreorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-subpreorder-Large-Subposetᵉ Sᵉ)

  antisymmetric-leq-Large-Subposetᵉ :
    is-antisymmetric-Large-Relationᵉ type-Large-Subposetᵉ leq-Large-Subposetᵉ
  antisymmetric-leq-Large-Subposetᵉ {l1ᵉ} (xᵉ ,ᵉ pᵉ) (yᵉ ,ᵉ qᵉ) Hᵉ Kᵉ =
    eq-type-subtypeᵉ
      ( large-subpreorder-Large-Subposetᵉ Sᵉ {l1ᵉ})
      ( antisymmetric-leq-Large-Posetᵉ Pᵉ xᵉ yᵉ Hᵉ Kᵉ)

  large-poset-Large-Subposetᵉ : Large-Posetᵉ (λ lᵉ → αᵉ lᵉ ⊔ γᵉ lᵉ) βᵉ
  large-preorder-Large-Posetᵉ
    large-poset-Large-Subposetᵉ =
    large-preorder-Large-Subposetᵉ
  antisymmetric-leq-Large-Posetᵉ
    large-poset-Large-Subposetᵉ =
    antisymmetric-leq-Large-Subposetᵉ
```

### The predicate of having the same elements

```agda
module _
  {αᵉ γSᵉ γTᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ) (Sᵉ : Large-Subposetᵉ γSᵉ Pᵉ) (Tᵉ : Large-Subposetᵉ γTᵉ Pᵉ)
  where

  has-same-elements-Large-Subposetᵉ : UUωᵉ
  has-same-elements-Large-Subposetᵉ =
    {lᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ lᵉ) →
    is-in-Large-Subposetᵉ Pᵉ Sᵉ xᵉ ↔ᵉ is-in-Large-Subposetᵉ Pᵉ Tᵉ xᵉ
```