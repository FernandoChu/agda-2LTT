# Subsets of monoids

```agda
module group-theory.subsets-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.monoidsᵉ
```

</details>

## Idea

Aᵉ subsetᵉ ofᵉ aᵉ monoidᵉ `M`ᵉ isᵉ aᵉ subsetᵉ ofᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `M`.ᵉ

## Definitions

### Subsets of monoids

```agda
subset-Monoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Mᵉ : Monoidᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
subset-Monoidᵉ l2ᵉ Mᵉ = subtypeᵉ l2ᵉ (type-Monoidᵉ Mᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Pᵉ : subset-Monoidᵉ l2ᵉ Mᵉ)
  where

  is-in-subset-Monoidᵉ : type-Monoidᵉ Mᵉ → UUᵉ l2ᵉ
  is-in-subset-Monoidᵉ = is-in-subtypeᵉ Pᵉ

  is-prop-is-in-subset-Monoidᵉ :
    (xᵉ : type-Monoidᵉ Mᵉ) → is-propᵉ (is-in-subset-Monoidᵉ xᵉ)
  is-prop-is-in-subset-Monoidᵉ = is-prop-is-in-subtypeᵉ Pᵉ

  type-subset-Monoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-subset-Monoidᵉ = type-subtypeᵉ Pᵉ

  is-set-type-subset-Monoidᵉ : is-setᵉ type-subset-Monoidᵉ
  is-set-type-subset-Monoidᵉ =
    is-set-type-subtypeᵉ Pᵉ (is-set-type-Monoidᵉ Mᵉ)

  set-subset-Monoidᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-subset-Monoidᵉ = set-subsetᵉ (set-Monoidᵉ Mᵉ) Pᵉ

  inclusion-subset-Monoidᵉ : type-subset-Monoidᵉ → type-Monoidᵉ Mᵉ
  inclusion-subset-Monoidᵉ = inclusion-subtypeᵉ Pᵉ

  ap-inclusion-subset-Monoidᵉ :
    (xᵉ yᵉ : type-subset-Monoidᵉ) →
    xᵉ ＝ᵉ yᵉ → (inclusion-subset-Monoidᵉ xᵉ ＝ᵉ inclusion-subset-Monoidᵉ yᵉ)
  ap-inclusion-subset-Monoidᵉ = ap-inclusion-subtypeᵉ Pᵉ

  is-in-subset-inclusion-subset-Monoidᵉ :
    (xᵉ : type-subset-Monoidᵉ) →
    is-in-subset-Monoidᵉ (inclusion-subset-Monoidᵉ xᵉ)
  is-in-subset-inclusion-subset-Monoidᵉ =
    is-in-subtype-inclusion-subtypeᵉ Pᵉ
```

### The condition that a subset contains the unit

```agda
  contains-unit-prop-subset-Monoidᵉ : Propᵉ l2ᵉ
  contains-unit-prop-subset-Monoidᵉ = Pᵉ (unit-Monoidᵉ Mᵉ)

  contains-unit-subset-Monoidᵉ : UUᵉ l2ᵉ
  contains-unit-subset-Monoidᵉ = type-Propᵉ contains-unit-prop-subset-Monoidᵉ
```

### The condition that a subset is closed under multiplication

```agda
  is-closed-under-multiplication-prop-subset-Monoidᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-multiplication-prop-subset-Monoidᵉ =
    Π-Propᵉ
      ( type-Monoidᵉ Mᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( type-Monoidᵉ Mᵉ)
          ( λ yᵉ → hom-Propᵉ (Pᵉ xᵉ) (hom-Propᵉ (Pᵉ yᵉ) (Pᵉ (mul-Monoidᵉ Mᵉ xᵉ yᵉ)))))

  is-closed-under-multiplication-subset-Monoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-multiplication-subset-Monoidᵉ =
    type-Propᵉ is-closed-under-multiplication-prop-subset-Monoidᵉ
```