# Inhabited subtypes

```agda
module foundation.inhabited-subtypesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Anᵉ inhabitedᵉ subtypeᵉ ofᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ subtypeᵉ `P`ᵉ ofᵉ `A`ᵉ suchᵉ thatᵉ theᵉ
underlyingᵉ typeᵉ ofᵉ `P`ᵉ isᵉ inhabited.ᵉ

```agda
is-inhabited-subtype-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → subtypeᵉ l2ᵉ Aᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-inhabited-subtype-Propᵉ Pᵉ = is-inhabited-Propᵉ (type-subtypeᵉ Pᵉ)

is-inhabited-subtypeᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → subtypeᵉ l2ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-inhabited-subtypeᵉ Pᵉ = type-Propᵉ (is-inhabited-subtype-Propᵉ Pᵉ)

inhabited-subtypeᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
inhabited-subtypeᵉ l2ᵉ Aᵉ = type-subtypeᵉ (is-inhabited-subtype-Propᵉ {l2ᵉ = l2ᵉ} {Aᵉ})

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : inhabited-subtypeᵉ l2ᵉ Aᵉ)
  where

  subtype-inhabited-subtypeᵉ : subtypeᵉ l2ᵉ Aᵉ
  subtype-inhabited-subtypeᵉ = pr1ᵉ Pᵉ

  is-inhabited-subtype-inhabited-subtypeᵉ :
    is-inhabited-subtypeᵉ subtype-inhabited-subtypeᵉ
  is-inhabited-subtype-inhabited-subtypeᵉ = pr2ᵉ Pᵉ

  type-inhabited-subtypeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-inhabited-subtypeᵉ = type-subtypeᵉ subtype-inhabited-subtypeᵉ

  inhabited-type-inhabited-subtypeᵉ : Inhabited-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ inhabited-type-inhabited-subtypeᵉ = type-inhabited-subtypeᵉ
  pr2ᵉ inhabited-type-inhabited-subtypeᵉ =
    is-inhabited-subtype-inhabited-subtypeᵉ

  is-in-inhabited-subtypeᵉ : Aᵉ → UUᵉ l2ᵉ
  is-in-inhabited-subtypeᵉ = is-in-subtypeᵉ subtype-inhabited-subtypeᵉ

  is-prop-is-in-inhabited-subtypeᵉ :
    (xᵉ : Aᵉ) → is-propᵉ (is-in-inhabited-subtypeᵉ xᵉ)
  is-prop-is-in-inhabited-subtypeᵉ =
    is-prop-is-in-subtypeᵉ subtype-inhabited-subtypeᵉ

  inclusion-inhabited-subtypeᵉ : type-inhabited-subtypeᵉ → Aᵉ
  inclusion-inhabited-subtypeᵉ = inclusion-subtypeᵉ subtype-inhabited-subtypeᵉ

  ap-inclusion-inhabited-subtypeᵉ :
    (xᵉ yᵉ : type-inhabited-subtypeᵉ) →
    xᵉ ＝ᵉ yᵉ → (inclusion-inhabited-subtypeᵉ xᵉ ＝ᵉ inclusion-inhabited-subtypeᵉ yᵉ)
  ap-inclusion-inhabited-subtypeᵉ =
    ap-inclusion-subtypeᵉ subtype-inhabited-subtypeᵉ

  is-in-inhabited-subtype-inclusion-inhabited-subtypeᵉ :
    (xᵉ : type-inhabited-subtypeᵉ) →
    is-in-inhabited-subtypeᵉ (inclusion-inhabited-subtypeᵉ xᵉ)
  is-in-inhabited-subtype-inclusion-inhabited-subtypeᵉ =
    is-in-subtype-inclusion-subtypeᵉ subtype-inhabited-subtypeᵉ
```

## Properties

### Characterization of equality of inhabited subtypes

```agda
has-same-elements-inhabited-subtype-Propᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  inhabited-subtypeᵉ l2ᵉ Aᵉ → inhabited-subtypeᵉ l3ᵉ Aᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
has-same-elements-inhabited-subtype-Propᵉ Pᵉ Qᵉ =
  has-same-elements-subtype-Propᵉ
    ( subtype-inhabited-subtypeᵉ Pᵉ)
    ( subtype-inhabited-subtypeᵉ Qᵉ)

has-same-elements-inhabited-subtypeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  inhabited-subtypeᵉ l2ᵉ Aᵉ → inhabited-subtypeᵉ l3ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
has-same-elements-inhabited-subtypeᵉ Pᵉ Qᵉ =
  type-Propᵉ (has-same-elements-inhabited-subtype-Propᵉ Pᵉ Qᵉ)

is-prop-has-same-elements-inhabited-subtypeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  (Pᵉ : inhabited-subtypeᵉ l2ᵉ Aᵉ) (Qᵉ : inhabited-subtypeᵉ l3ᵉ Aᵉ) →
  is-propᵉ (has-same-elements-inhabited-subtypeᵉ Pᵉ Qᵉ)
is-prop-has-same-elements-inhabited-subtypeᵉ Pᵉ Qᵉ =
  is-prop-type-Propᵉ (has-same-elements-inhabited-subtype-Propᵉ Pᵉ Qᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : inhabited-subtypeᵉ l2ᵉ Aᵉ)
  where

  refl-has-same-elements-inhabited-subtypeᵉ :
    has-same-elements-inhabited-subtypeᵉ Pᵉ Pᵉ
  refl-has-same-elements-inhabited-subtypeᵉ =
    refl-has-same-elements-subtypeᵉ (subtype-inhabited-subtypeᵉ Pᵉ)

  is-torsorial-has-same-elements-inhabited-subtypeᵉ :
    is-torsorialᵉ (has-same-elements-inhabited-subtypeᵉ Pᵉ)
  is-torsorial-has-same-elements-inhabited-subtypeᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-has-same-elements-subtypeᵉ
        ( subtype-inhabited-subtypeᵉ Pᵉ))
      ( λ Qᵉ → is-prop-type-trunc-Propᵉ)
      ( subtype-inhabited-subtypeᵉ Pᵉ)
      ( refl-has-same-elements-inhabited-subtypeᵉ)
      ( is-inhabited-subtype-inhabited-subtypeᵉ Pᵉ)

  extensionality-inhabited-subtypeᵉ :
    (Qᵉ : inhabited-subtypeᵉ l2ᵉ Aᵉ) → (Pᵉ ＝ᵉ Qᵉ) ≃ᵉ
    has-same-elements-inhabited-subtypeᵉ Pᵉ Qᵉ
  extensionality-inhabited-subtypeᵉ Qᵉ =
    ( extensionality-subtypeᵉ
      ( subtype-inhabited-subtypeᵉ Pᵉ)
      ( subtype-inhabited-subtypeᵉ Qᵉ)) ∘eᵉ
    ( extensionality-type-subtype'ᵉ is-inhabited-subtype-Propᵉ Pᵉ Qᵉ)

  has-same-elements-eq-inhabited-subtypeᵉ :
    (Qᵉ : inhabited-subtypeᵉ l2ᵉ Aᵉ) →
    (Pᵉ ＝ᵉ Qᵉ) → has-same-elements-inhabited-subtypeᵉ Pᵉ Qᵉ
  has-same-elements-eq-inhabited-subtypeᵉ Qᵉ =
    map-equivᵉ (extensionality-inhabited-subtypeᵉ Qᵉ)

  eq-has-same-elements-inhabited-subtypeᵉ :
    (Qᵉ : inhabited-subtypeᵉ l2ᵉ Aᵉ) →
    has-same-elements-inhabited-subtypeᵉ Pᵉ Qᵉ → Pᵉ ＝ᵉ Qᵉ
  eq-has-same-elements-inhabited-subtypeᵉ Qᵉ =
    map-inv-equivᵉ (extensionality-inhabited-subtypeᵉ Qᵉ)

  refl-extensionality-inhabited-subtypeᵉ :
    map-equivᵉ (extensionality-inhabited-subtypeᵉ Pᵉ) reflᵉ ＝ᵉ
    refl-has-same-elements-inhabited-subtypeᵉ
  refl-extensionality-inhabited-subtypeᵉ = reflᵉ
```