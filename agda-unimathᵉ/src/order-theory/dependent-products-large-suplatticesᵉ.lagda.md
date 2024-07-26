# Dependent products of large suplattices

```agda
module order-theory.dependent-products-large-suplatticesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relationsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.dependent-products-large-posetsᵉ
open import order-theory.large-posetsᵉ
open import order-theory.large-suplatticesᵉ
open import order-theory.least-upper-bounds-large-posetsᵉ
```

</details>

## Idea

Familiesᵉ ofᵉ leastᵉ upperᵉ boundsᵉ ofᵉ familiesᵉ ofᵉ elementsᵉ in dependentᵉ productsᵉ ofᵉ
largeᵉ posetsᵉ areᵉ againᵉ leastᵉ upperᵉ bounds.ᵉ Thereforeᵉ itᵉ followsᵉ thatᵉ dependentᵉ
productsᵉ ofᵉ largeᵉ suplatticesᵉ areᵉ againᵉ largeᵉ suplattices.ᵉ

## Definitions

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  {l1ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (Lᵉ : Iᵉ → Large-Suplatticeᵉ αᵉ βᵉ γᵉ)
  where

  large-poset-Π-Large-Suplatticeᵉ :
    Large-Posetᵉ (λ l2ᵉ → αᵉ l2ᵉ ⊔ l1ᵉ) (λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ)
  large-poset-Π-Large-Suplatticeᵉ =
    Π-Large-Posetᵉ (λ iᵉ → large-poset-Large-Suplatticeᵉ (Lᵉ iᵉ))

  is-large-suplattice-Π-Large-Suplatticeᵉ :
    is-large-suplattice-Large-Posetᵉ γᵉ large-poset-Π-Large-Suplatticeᵉ
  sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
    ( is-large-suplattice-Π-Large-Suplatticeᵉ {l2ᵉ} {l3ᵉ} {Jᵉ} aᵉ) iᵉ =
    sup-Large-Suplatticeᵉ (Lᵉ iᵉ) (λ jᵉ → aᵉ jᵉ iᵉ)
  is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
    ( is-large-suplattice-Π-Large-Suplatticeᵉ {l2ᵉ} {l3ᵉ} {Jᵉ} aᵉ) =
    is-least-upper-bound-Π-Large-Posetᵉ
      ( λ iᵉ → large-poset-Large-Suplatticeᵉ (Lᵉ iᵉ))
      ( aᵉ)
      ( λ iᵉ → sup-Large-Suplatticeᵉ (Lᵉ iᵉ) (λ jᵉ → aᵉ jᵉ iᵉ))
      ( λ iᵉ →
        is-least-upper-bound-sup-Large-Suplatticeᵉ (Lᵉ iᵉ) (λ jᵉ → aᵉ jᵉ iᵉ))

  Π-Large-Suplatticeᵉ :
    Large-Suplatticeᵉ (λ l2ᵉ → αᵉ l2ᵉ ⊔ l1ᵉ) (λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ) γᵉ
  large-poset-Large-Suplatticeᵉ Π-Large-Suplatticeᵉ =
    large-poset-Π-Large-Suplatticeᵉ
  is-large-suplattice-Large-Suplatticeᵉ Π-Large-Suplatticeᵉ =
    is-large-suplattice-Π-Large-Suplatticeᵉ

  set-Π-Large-Suplatticeᵉ : (lᵉ : Level) → Setᵉ (αᵉ lᵉ ⊔ l1ᵉ)
  set-Π-Large-Suplatticeᵉ =
    set-Large-Suplatticeᵉ Π-Large-Suplatticeᵉ

  type-Π-Large-Suplatticeᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ ⊔ l1ᵉ)
  type-Π-Large-Suplatticeᵉ =
    type-Large-Suplatticeᵉ Π-Large-Suplatticeᵉ

  is-set-type-Π-Large-Suplatticeᵉ :
    {lᵉ : Level} → is-setᵉ (type-Π-Large-Suplatticeᵉ lᵉ)
  is-set-type-Π-Large-Suplatticeᵉ =
    is-set-type-Large-Suplatticeᵉ Π-Large-Suplatticeᵉ

  leq-prop-Π-Large-Suplatticeᵉ :
    Large-Relation-Propᵉ
      ( λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ)
      ( type-Π-Large-Suplatticeᵉ)
  leq-prop-Π-Large-Suplatticeᵉ =
    leq-prop-Large-Suplatticeᵉ Π-Large-Suplatticeᵉ

  leq-Π-Large-Suplatticeᵉ :
    {l2ᵉ l3ᵉ : Level}
    (xᵉ : type-Π-Large-Suplatticeᵉ l2ᵉ) (yᵉ : type-Π-Large-Suplatticeᵉ l3ᵉ) →
    UUᵉ (βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ)
  leq-Π-Large-Suplatticeᵉ =
    leq-Large-Suplatticeᵉ Π-Large-Suplatticeᵉ

  is-prop-leq-Π-Large-Suplatticeᵉ :
    is-prop-Large-Relationᵉ type-Π-Large-Suplatticeᵉ leq-Π-Large-Suplatticeᵉ
  is-prop-leq-Π-Large-Suplatticeᵉ =
    is-prop-leq-Large-Suplatticeᵉ Π-Large-Suplatticeᵉ

  refl-leq-Π-Large-Suplatticeᵉ :
    is-reflexive-Large-Relationᵉ type-Π-Large-Suplatticeᵉ leq-Π-Large-Suplatticeᵉ
  refl-leq-Π-Large-Suplatticeᵉ =
    refl-leq-Large-Suplatticeᵉ Π-Large-Suplatticeᵉ

  antisymmetric-leq-Π-Large-Suplatticeᵉ :
    is-antisymmetric-Large-Relationᵉ
      ( type-Π-Large-Suplatticeᵉ)
      ( leq-Π-Large-Suplatticeᵉ)
  antisymmetric-leq-Π-Large-Suplatticeᵉ =
    antisymmetric-leq-Large-Suplatticeᵉ Π-Large-Suplatticeᵉ

  transitive-leq-Π-Large-Suplatticeᵉ :
    is-transitive-Large-Relationᵉ
      ( type-Π-Large-Suplatticeᵉ)
      ( leq-Π-Large-Suplatticeᵉ)
  transitive-leq-Π-Large-Suplatticeᵉ =
    transitive-leq-Large-Suplatticeᵉ Π-Large-Suplatticeᵉ

  sup-Π-Large-Suplatticeᵉ :
    {l2ᵉ l3ᵉ : Level} {Jᵉ : UUᵉ l2ᵉ} (xᵉ : Jᵉ → type-Π-Large-Suplatticeᵉ l3ᵉ) →
    type-Π-Large-Suplatticeᵉ (γᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  sup-Π-Large-Suplatticeᵉ =
    sup-Large-Suplatticeᵉ Π-Large-Suplatticeᵉ

  is-upper-bound-family-of-elements-Π-Large-Suplatticeᵉ :
    {l2ᵉ l3ᵉ l4ᵉ : Level} {Jᵉ : UUᵉ l2ᵉ} (xᵉ : Jᵉ → type-Π-Large-Suplatticeᵉ l3ᵉ)
    (yᵉ : type-Π-Large-Suplatticeᵉ l4ᵉ) → UUᵉ (βᵉ l3ᵉ l4ᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
  is-upper-bound-family-of-elements-Π-Large-Suplatticeᵉ =
    is-upper-bound-family-of-elements-Large-Suplatticeᵉ Π-Large-Suplatticeᵉ

  is-least-upper-bound-family-of-elements-Π-Large-Suplatticeᵉ :
    {l2ᵉ l3ᵉ l4ᵉ : Level} {Jᵉ : UUᵉ l2ᵉ} (xᵉ : Jᵉ → type-Π-Large-Suplatticeᵉ l3ᵉ) →
    type-Π-Large-Suplatticeᵉ l4ᵉ → UUωᵉ
  is-least-upper-bound-family-of-elements-Π-Large-Suplatticeᵉ =
    is-least-upper-bound-family-of-elements-Large-Suplatticeᵉ Π-Large-Suplatticeᵉ

  is-least-upper-bound-sup-Π-Large-Suplatticeᵉ :
    {l2ᵉ l3ᵉ : Level} {Jᵉ : UUᵉ l2ᵉ} (xᵉ : Jᵉ → type-Π-Large-Suplatticeᵉ l3ᵉ) →
    is-least-upper-bound-family-of-elements-Π-Large-Suplatticeᵉ xᵉ
      ( sup-Π-Large-Suplatticeᵉ xᵉ)
  is-least-upper-bound-sup-Π-Large-Suplatticeᵉ =
    is-least-upper-bound-sup-Large-Suplatticeᵉ Π-Large-Suplatticeᵉ
```