# Submonoids

```agda
module group-theory.submonoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.subsets-monoidsᵉ
```

</details>

## Idea

Aᵉ submonoidᵉ ofᵉ aᵉ monoidᵉ `M`ᵉ isᵉ aᵉ subsetᵉ ofᵉ `M`ᵉ thatᵉ containsᵉ theᵉ unitᵉ ofᵉ `M`ᵉ andᵉ
isᵉ closedᵉ underᵉ multiplication.ᵉ

## Definitions

### Submonoids

```agda
is-submonoid-prop-subset-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Pᵉ : subset-Monoidᵉ l2ᵉ Mᵉ) →
  Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-submonoid-prop-subset-Monoidᵉ Mᵉ Pᵉ =
  product-Propᵉ
    ( contains-unit-prop-subset-Monoidᵉ Mᵉ Pᵉ)
    ( is-closed-under-multiplication-prop-subset-Monoidᵉ Mᵉ Pᵉ)

is-submonoid-subset-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Pᵉ : subset-Monoidᵉ l2ᵉ Mᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-submonoid-subset-Monoidᵉ Mᵉ Pᵉ =
  type-Propᵉ (is-submonoid-prop-subset-Monoidᵉ Mᵉ Pᵉ)

Submonoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Mᵉ : Monoidᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Submonoidᵉ l2ᵉ Mᵉ =
  type-subtypeᵉ (is-submonoid-prop-subset-Monoidᵉ {l2ᵉ = l2ᵉ} Mᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Pᵉ : Submonoidᵉ l2ᵉ Mᵉ)
  where

  subset-Submonoidᵉ : subtypeᵉ l2ᵉ (type-Monoidᵉ Mᵉ)
  subset-Submonoidᵉ =
    inclusion-subtypeᵉ (is-submonoid-prop-subset-Monoidᵉ Mᵉ) Pᵉ

  is-submonoid-Submonoidᵉ : is-submonoid-subset-Monoidᵉ Mᵉ subset-Submonoidᵉ
  is-submonoid-Submonoidᵉ = pr2ᵉ Pᵉ

  is-in-Submonoidᵉ : type-Monoidᵉ Mᵉ → UUᵉ l2ᵉ
  is-in-Submonoidᵉ = is-in-subtypeᵉ subset-Submonoidᵉ

  is-prop-is-in-Submonoidᵉ :
    (xᵉ : type-Monoidᵉ Mᵉ) → is-propᵉ (is-in-Submonoidᵉ xᵉ)
  is-prop-is-in-Submonoidᵉ =
    is-prop-is-in-subtypeᵉ subset-Submonoidᵉ

  is-closed-under-eq-Submonoidᵉ :
    {xᵉ yᵉ : type-Monoidᵉ Mᵉ} → is-in-Submonoidᵉ xᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-Submonoidᵉ yᵉ
  is-closed-under-eq-Submonoidᵉ = is-closed-under-eq-subtypeᵉ subset-Submonoidᵉ

  is-closed-under-eq-Submonoid'ᵉ :
    {xᵉ yᵉ : type-Monoidᵉ Mᵉ} → is-in-Submonoidᵉ yᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-Submonoidᵉ xᵉ
  is-closed-under-eq-Submonoid'ᵉ = is-closed-under-eq-subtype'ᵉ subset-Submonoidᵉ

  type-Submonoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Submonoidᵉ = type-subtypeᵉ subset-Submonoidᵉ

  is-set-type-Submonoidᵉ : is-setᵉ type-Submonoidᵉ
  is-set-type-Submonoidᵉ =
    is-set-type-subset-Monoidᵉ Mᵉ subset-Submonoidᵉ

  set-Submonoidᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-Submonoidᵉ =
    set-subset-Monoidᵉ Mᵉ subset-Submonoidᵉ

  inclusion-Submonoidᵉ :
    type-Submonoidᵉ → type-Monoidᵉ Mᵉ
  inclusion-Submonoidᵉ =
    inclusion-subtypeᵉ subset-Submonoidᵉ

  ap-inclusion-Submonoidᵉ :
    (xᵉ yᵉ : type-Submonoidᵉ) → xᵉ ＝ᵉ yᵉ →
    inclusion-Submonoidᵉ xᵉ ＝ᵉ inclusion-Submonoidᵉ yᵉ
  ap-inclusion-Submonoidᵉ =
    ap-inclusion-subtypeᵉ subset-Submonoidᵉ

  is-in-submonoid-inclusion-Submonoidᵉ :
    (xᵉ : type-Submonoidᵉ) →
    is-in-Submonoidᵉ (inclusion-Submonoidᵉ xᵉ)
  is-in-submonoid-inclusion-Submonoidᵉ =
    is-in-subtype-inclusion-subtypeᵉ subset-Submonoidᵉ

  contains-unit-Submonoidᵉ : is-in-Submonoidᵉ (unit-Monoidᵉ Mᵉ)
  contains-unit-Submonoidᵉ = pr1ᵉ (pr2ᵉ Pᵉ)

  unit-Submonoidᵉ : type-Submonoidᵉ
  pr1ᵉ unit-Submonoidᵉ = unit-Monoidᵉ Mᵉ
  pr2ᵉ unit-Submonoidᵉ = contains-unit-Submonoidᵉ

  is-closed-under-multiplication-Submonoidᵉ :
    {xᵉ yᵉ : type-Monoidᵉ Mᵉ} →
    is-in-Submonoidᵉ xᵉ → is-in-Submonoidᵉ yᵉ →
    is-in-Submonoidᵉ (mul-Monoidᵉ Mᵉ xᵉ yᵉ)
  is-closed-under-multiplication-Submonoidᵉ {xᵉ} {yᵉ} = pr2ᵉ (pr2ᵉ Pᵉ) xᵉ yᵉ

  mul-Submonoidᵉ : (xᵉ yᵉ : type-Submonoidᵉ) → type-Submonoidᵉ
  pr1ᵉ (mul-Submonoidᵉ xᵉ yᵉ) =
    mul-Monoidᵉ Mᵉ (inclusion-Submonoidᵉ xᵉ) (inclusion-Submonoidᵉ yᵉ)
  pr2ᵉ (mul-Submonoidᵉ xᵉ yᵉ) =
    is-closed-under-multiplication-Submonoidᵉ
      ( is-in-submonoid-inclusion-Submonoidᵉ xᵉ)
      ( is-in-submonoid-inclusion-Submonoidᵉ yᵉ)

  associative-mul-Submonoidᵉ :
    (xᵉ yᵉ zᵉ : type-Submonoidᵉ) →
    (mul-Submonoidᵉ (mul-Submonoidᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    (mul-Submonoidᵉ xᵉ (mul-Submonoidᵉ yᵉ zᵉ))
  associative-mul-Submonoidᵉ xᵉ yᵉ zᵉ =
    eq-type-subtypeᵉ
      ( subset-Submonoidᵉ)
      ( associative-mul-Monoidᵉ Mᵉ
        ( inclusion-Submonoidᵉ xᵉ)
        ( inclusion-Submonoidᵉ yᵉ)
        ( inclusion-Submonoidᵉ zᵉ))

  semigroup-Submonoidᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ semigroup-Submonoidᵉ = set-Submonoidᵉ
  pr1ᵉ (pr2ᵉ semigroup-Submonoidᵉ) = mul-Submonoidᵉ
  pr2ᵉ (pr2ᵉ semigroup-Submonoidᵉ) = associative-mul-Submonoidᵉ

  left-unit-law-mul-Submonoidᵉ :
    (xᵉ : type-Submonoidᵉ) → mul-Submonoidᵉ unit-Submonoidᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Submonoidᵉ xᵉ =
    eq-type-subtypeᵉ
      ( subset-Submonoidᵉ)
      ( left-unit-law-mul-Monoidᵉ Mᵉ (inclusion-Submonoidᵉ xᵉ))

  right-unit-law-mul-Submonoidᵉ :
    (xᵉ : type-Submonoidᵉ) → mul-Submonoidᵉ xᵉ unit-Submonoidᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Submonoidᵉ xᵉ =
    eq-type-subtypeᵉ
      ( subset-Submonoidᵉ)
      ( right-unit-law-mul-Monoidᵉ Mᵉ (inclusion-Submonoidᵉ xᵉ))

  monoid-Submonoidᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ monoid-Submonoidᵉ = semigroup-Submonoidᵉ
  pr1ᵉ (pr2ᵉ monoid-Submonoidᵉ) = unit-Submonoidᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ monoid-Submonoidᵉ)) = left-unit-law-mul-Submonoidᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ monoid-Submonoidᵉ)) = right-unit-law-mul-Submonoidᵉ

  preserves-unit-inclusion-Submonoidᵉ :
    inclusion-Submonoidᵉ unit-Submonoidᵉ ＝ᵉ unit-Monoidᵉ Mᵉ
  preserves-unit-inclusion-Submonoidᵉ = reflᵉ

  preserves-mul-inclusion-Submonoidᵉ :
    {xᵉ yᵉ : type-Submonoidᵉ} →
    inclusion-Submonoidᵉ (mul-Submonoidᵉ xᵉ yᵉ) ＝ᵉ
    mul-Monoidᵉ Mᵉ (inclusion-Submonoidᵉ xᵉ) (inclusion-Submonoidᵉ yᵉ)
  preserves-mul-inclusion-Submonoidᵉ = reflᵉ

  hom-inclusion-Submonoidᵉ :
    hom-Monoidᵉ monoid-Submonoidᵉ Mᵉ
  pr1ᵉ (pr1ᵉ hom-inclusion-Submonoidᵉ) =
    inclusion-Submonoidᵉ
  pr2ᵉ (pr1ᵉ hom-inclusion-Submonoidᵉ) {xᵉ} {yᵉ} =
    preserves-mul-inclusion-Submonoidᵉ {xᵉ} {yᵉ}
  pr2ᵉ hom-inclusion-Submonoidᵉ = preserves-unit-inclusion-Submonoidᵉ
```

## Properties

### Extensionality of the type of all submonoids

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Submonoidᵉ l2ᵉ Mᵉ)
  where

  has-same-elements-Submonoidᵉ :
    {l3ᵉ : Level} → Submonoidᵉ l3ᵉ Mᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-Submonoidᵉ Kᵉ =
    has-same-elements-subtypeᵉ (subset-Submonoidᵉ Mᵉ Nᵉ) (subset-Submonoidᵉ Mᵉ Kᵉ)

  extensionality-Submonoidᵉ :
    (Kᵉ : Submonoidᵉ l2ᵉ Mᵉ) → (Nᵉ ＝ᵉ Kᵉ) ≃ᵉ has-same-elements-Submonoidᵉ Kᵉ
  extensionality-Submonoidᵉ =
    extensionality-type-subtypeᵉ
      ( is-submonoid-prop-subset-Monoidᵉ Mᵉ)
      ( is-submonoid-Submonoidᵉ Mᵉ Nᵉ)
      ( λ xᵉ → pairᵉ idᵉ idᵉ)
      ( extensionality-subtypeᵉ (subset-Submonoidᵉ Mᵉ Nᵉ))
```