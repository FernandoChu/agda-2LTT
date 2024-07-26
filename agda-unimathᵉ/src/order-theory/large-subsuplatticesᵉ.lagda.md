# Large subsuplattices

```agda
module order-theory.large-subsuplatticesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relationsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.large-subposetsᵉ
open import order-theory.large-suplatticesᵉ
```

</details>

## Idea

Aᵉ **largeᵉ subsuplattice**ᵉ ofᵉ aᵉ
[largeᵉ suplattice](order-theory.large-suplattices.mdᵉ) isᵉ aᵉ largeᵉ subposetᵉ whichᵉ
isᵉ closedᵉ underᵉ suprema.ᵉ

## Definition

```agda
module _
  {αᵉ γᵉ : Level → Level} {βᵉ : Level → Level → Level} {δᵉ : Level}
  (Lᵉ : Large-Suplatticeᵉ αᵉ βᵉ δᵉ)
  where

  is-closed-under-sup-Large-Subposetᵉ :
    Large-Subposetᵉ γᵉ (large-poset-Large-Suplatticeᵉ Lᵉ) → UUωᵉ
  is-closed-under-sup-Large-Subposetᵉ Sᵉ =
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Suplatticeᵉ Lᵉ l2ᵉ) →
    ((iᵉ : Iᵉ) → is-in-Large-Subposetᵉ (large-poset-Large-Suplatticeᵉ Lᵉ) Sᵉ (xᵉ iᵉ)) →
    is-in-Large-Subposetᵉ
      ( large-poset-Large-Suplatticeᵉ Lᵉ)
      ( Sᵉ)
      ( sup-Large-Suplatticeᵉ Lᵉ xᵉ)

record
  Large-Subsuplatticeᵉ
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {δᵉ : Level}
  (γᵉ : Level → Level)
  (Lᵉ : Large-Suplatticeᵉ αᵉ βᵉ δᵉ) :
  UUωᵉ
  where
  field
    large-subposet-Large-Subsuplatticeᵉ :
      Large-Subposetᵉ γᵉ (large-poset-Large-Suplatticeᵉ Lᵉ)
    is-closed-under-sup-Large-Subsuplatticeᵉ :
      is-closed-under-sup-Large-Subposetᵉ Lᵉ (large-subposet-Large-Subsuplatticeᵉ)

open Large-Subsuplatticeᵉ public

module _
  {αᵉ γᵉ : Level → Level} {βᵉ : Level → Level → Level} {δᵉ : Level}
  (Pᵉ : Large-Suplatticeᵉ αᵉ βᵉ δᵉ) (Sᵉ : Large-Subsuplatticeᵉ γᵉ Pᵉ)
  where

  large-poset-Large-Subsuplatticeᵉ :
    Large-Posetᵉ (λ lᵉ → αᵉ lᵉ ⊔ γᵉ lᵉ) (λ l1ᵉ l2ᵉ → βᵉ l1ᵉ l2ᵉ)
  large-poset-Large-Subsuplatticeᵉ =
    large-poset-Large-Subposetᵉ
      ( large-poset-Large-Suplatticeᵉ Pᵉ)
      ( large-subposet-Large-Subsuplatticeᵉ Sᵉ)

  is-in-Large-Subsuplatticeᵉ :
    {l1ᵉ : Level} → type-Large-Suplatticeᵉ Pᵉ l1ᵉ → UUᵉ (γᵉ l1ᵉ)
  is-in-Large-Subsuplatticeᵉ =
    is-in-Large-Subposetᵉ
      ( large-poset-Large-Suplatticeᵉ Pᵉ)
      ( large-subposet-Large-Subsuplatticeᵉ Sᵉ)

  type-Large-Subsuplatticeᵉ : (l1ᵉ : Level) → UUᵉ (αᵉ l1ᵉ ⊔ γᵉ l1ᵉ)
  type-Large-Subsuplatticeᵉ =
    type-Large-Subposetᵉ
      ( large-poset-Large-Suplatticeᵉ Pᵉ)
      ( large-subposet-Large-Subsuplatticeᵉ Sᵉ)

  leq-prop-Large-Subsuplatticeᵉ :
    Large-Relation-Propᵉ βᵉ type-Large-Subsuplatticeᵉ
  leq-prop-Large-Subsuplatticeᵉ =
    leq-prop-Large-Subposetᵉ
      ( large-poset-Large-Suplatticeᵉ Pᵉ)
      ( large-subposet-Large-Subsuplatticeᵉ Sᵉ)

  leq-Large-Subsuplatticeᵉ :
    Large-Relationᵉ βᵉ type-Large-Subsuplatticeᵉ
  leq-Large-Subsuplatticeᵉ =
    leq-Large-Subposetᵉ
      ( large-poset-Large-Suplatticeᵉ Pᵉ)
      ( large-subposet-Large-Subsuplatticeᵉ Sᵉ)

  is-prop-leq-Large-Subsuplatticeᵉ :
    is-prop-Large-Relationᵉ type-Large-Subsuplatticeᵉ leq-Large-Subsuplatticeᵉ
  is-prop-leq-Large-Subsuplatticeᵉ =
    is-prop-leq-Large-Subposetᵉ
      ( large-poset-Large-Suplatticeᵉ Pᵉ)
      ( large-subposet-Large-Subsuplatticeᵉ Sᵉ)

  refl-leq-Large-Subsuplatticeᵉ :
    is-reflexive-Large-Relationᵉ
      ( type-Large-Subsuplatticeᵉ)
      ( leq-Large-Subsuplatticeᵉ)
  refl-leq-Large-Subsuplatticeᵉ =
    refl-leq-Large-Subposetᵉ
      ( large-poset-Large-Suplatticeᵉ Pᵉ)
      ( large-subposet-Large-Subsuplatticeᵉ Sᵉ)

  transitive-leq-Large-Subsuplatticeᵉ :
    is-transitive-Large-Relationᵉ
      ( type-Large-Subsuplatticeᵉ)
      ( leq-Large-Subsuplatticeᵉ)
  transitive-leq-Large-Subsuplatticeᵉ =
    transitive-leq-Large-Subposetᵉ
      ( large-poset-Large-Suplatticeᵉ Pᵉ)
      ( large-subposet-Large-Subsuplatticeᵉ Sᵉ)

  antisymmetric-leq-Large-Subsuplatticeᵉ :
    is-antisymmetric-Large-Relationᵉ
      ( type-Large-Subsuplatticeᵉ)
      ( leq-Large-Subsuplatticeᵉ)
  antisymmetric-leq-Large-Subsuplatticeᵉ =
    antisymmetric-leq-Large-Subposetᵉ
      ( large-poset-Large-Suplatticeᵉ Pᵉ)
      ( large-subposet-Large-Subsuplatticeᵉ Sᵉ)

  is-closed-under-sim-Large-Subsuplatticeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Suplatticeᵉ Pᵉ l1ᵉ)
    (yᵉ : type-Large-Suplatticeᵉ Pᵉ l2ᵉ) →
    leq-Large-Suplatticeᵉ Pᵉ xᵉ yᵉ →
    leq-Large-Suplatticeᵉ Pᵉ yᵉ xᵉ →
    is-in-Large-Subsuplatticeᵉ xᵉ → is-in-Large-Subsuplatticeᵉ yᵉ
  is-closed-under-sim-Large-Subsuplatticeᵉ =
    is-closed-under-sim-Large-Subposetᵉ
      ( large-subposet-Large-Subsuplatticeᵉ Sᵉ)
```