# Mere equivalences of types equipped with endomorphisms

```agda
module structured-types.mere-equivalences-types-equipped-with-endomorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.equivalences-types-equipped-with-endomorphismsᵉ
open import structured-types.types-equipped-with-endomorphismsᵉ
```

</details>

## Definition

### Mere equivalences of types equipped with endomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Xᵉ : Type-With-Endomorphismᵉ l1ᵉ)
  (Yᵉ : Type-With-Endomorphismᵉ l2ᵉ)
  where

  mere-equiv-prop-Type-With-Endomorphismᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  mere-equiv-prop-Type-With-Endomorphismᵉ =
    trunc-Propᵉ (equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ)

  mere-equiv-Type-With-Endomorphismᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  mere-equiv-Type-With-Endomorphismᵉ =
    type-Propᵉ mere-equiv-prop-Type-With-Endomorphismᵉ

  is-prop-mere-equiv-Type-With-Endomorphismᵉ :
    is-propᵉ mere-equiv-Type-With-Endomorphismᵉ
  is-prop-mere-equiv-Type-With-Endomorphismᵉ =
    is-prop-type-Propᵉ mere-equiv-prop-Type-With-Endomorphismᵉ
```

### Refleivity of mere equivalences of types equipped with endomorphisms

```agda
module _
  {l1ᵉ : Level} (Xᵉ : Type-With-Endomorphismᵉ l1ᵉ)
  where

  refl-mere-equiv-Type-With-Endomorphismᵉ : mere-equiv-Type-With-Endomorphismᵉ Xᵉ Xᵉ
  refl-mere-equiv-Type-With-Endomorphismᵉ =
    unit-trunc-Propᵉ (id-equiv-Type-With-Endomorphismᵉ Xᵉ)
```

### Components of the universe of types equipped with endomorphisms

```agda
module _
  {l1ᵉ : Level} (Xᵉ : Type-With-Endomorphismᵉ l1ᵉ)
  where

  Component-Type-With-Endomorphismᵉ : UUᵉ (lsuc l1ᵉ)
  Component-Type-With-Endomorphismᵉ =
    Σᵉ (Type-With-Endomorphismᵉ l1ᵉ) (mere-equiv-Type-With-Endomorphismᵉ Xᵉ)

  endo-Component-Type-With-Endomorphismᵉ :
    Component-Type-With-Endomorphismᵉ → Type-With-Endomorphismᵉ l1ᵉ
  endo-Component-Type-With-Endomorphismᵉ = pr1ᵉ

  type-Component-Type-With-Endomorphismᵉ :
    Component-Type-With-Endomorphismᵉ → UUᵉ l1ᵉ
  type-Component-Type-With-Endomorphismᵉ =
    pr1ᵉ ∘ᵉ endo-Component-Type-With-Endomorphismᵉ

  endomorphism-Component-Type-With-Endomorphismᵉ :
    (Tᵉ : Component-Type-With-Endomorphismᵉ) →
    type-Component-Type-With-Endomorphismᵉ Tᵉ →
    type-Component-Type-With-Endomorphismᵉ Tᵉ
  endomorphism-Component-Type-With-Endomorphismᵉ Tᵉ =
    pr2ᵉ (endo-Component-Type-With-Endomorphismᵉ Tᵉ)

  mere-equiv-Component-Type-With-Endomorphismᵉ :
    (Tᵉ : Component-Type-With-Endomorphismᵉ) →
    mere-equiv-Type-With-Endomorphismᵉ Xᵉ
      ( endo-Component-Type-With-Endomorphismᵉ Tᵉ)
  mere-equiv-Component-Type-With-Endomorphismᵉ Tᵉ = pr2ᵉ Tᵉ

  canonical-Component-Type-With-Endomorphismᵉ : Component-Type-With-Endomorphismᵉ
  pr1ᵉ canonical-Component-Type-With-Endomorphismᵉ = Xᵉ
  pr2ᵉ canonical-Component-Type-With-Endomorphismᵉ =
    refl-mere-equiv-Type-With-Endomorphismᵉ Xᵉ
```

### Equivalences of types equipped with an endomorphism in a given component

```agda
module _
  {l1ᵉ : Level} (Xᵉ : Type-With-Endomorphismᵉ l1ᵉ)
  where

  equiv-Component-Type-With-Endomorphismᵉ :
    (Tᵉ Sᵉ : Component-Type-With-Endomorphismᵉ Xᵉ) → UUᵉ l1ᵉ
  equiv-Component-Type-With-Endomorphismᵉ Tᵉ Sᵉ =
    equiv-Type-With-Endomorphismᵉ
      ( endo-Component-Type-With-Endomorphismᵉ Xᵉ Tᵉ)
      ( endo-Component-Type-With-Endomorphismᵉ Xᵉ Sᵉ)

  id-equiv-Component-Type-With-Endomorphismᵉ :
    ( Tᵉ : Component-Type-With-Endomorphismᵉ Xᵉ) →
    equiv-Component-Type-With-Endomorphismᵉ Tᵉ Tᵉ
  id-equiv-Component-Type-With-Endomorphismᵉ Tᵉ =
    id-equiv-Type-With-Endomorphismᵉ (endo-Component-Type-With-Endomorphismᵉ Xᵉ Tᵉ)

  equiv-eq-Component-Type-With-Endomorphismᵉ :
    (Tᵉ Sᵉ : Component-Type-With-Endomorphismᵉ Xᵉ) →
    Tᵉ ＝ᵉ Sᵉ → equiv-Component-Type-With-Endomorphismᵉ Tᵉ Sᵉ
  equiv-eq-Component-Type-With-Endomorphismᵉ Tᵉ .Tᵉ reflᵉ =
    id-equiv-Component-Type-With-Endomorphismᵉ Tᵉ

  is-torsorial-equiv-Component-Type-With-Endomorphismᵉ :
    is-torsorialᵉ
      ( equiv-Component-Type-With-Endomorphismᵉ
        ( canonical-Component-Type-With-Endomorphismᵉ Xᵉ))
  is-torsorial-equiv-Component-Type-With-Endomorphismᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-equiv-Type-With-Endomorphismᵉ Xᵉ)
      ( λ Yᵉ → is-prop-type-trunc-Propᵉ)
      ( Xᵉ)
      ( id-equiv-Type-With-Endomorphismᵉ Xᵉ)
      ( refl-mere-equiv-Type-With-Endomorphismᵉ Xᵉ)

  is-equiv-equiv-eq-Component-Type-With-Endomorphismᵉ :
    (Tᵉ : Component-Type-With-Endomorphismᵉ Xᵉ) →
    is-equivᵉ
      ( equiv-eq-Component-Type-With-Endomorphismᵉ
        ( canonical-Component-Type-With-Endomorphismᵉ Xᵉ)
        ( Tᵉ))
  is-equiv-equiv-eq-Component-Type-With-Endomorphismᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-equiv-Component-Type-With-Endomorphismᵉ)
      ( equiv-eq-Component-Type-With-Endomorphismᵉ
        ( canonical-Component-Type-With-Endomorphismᵉ Xᵉ))
```