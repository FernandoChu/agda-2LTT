# Abstract groups

```agda
module group-theory.groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-embeddingsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.involutionsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.invertible-elements-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.products-of-elements-monoidsᵉ
open import group-theory.semigroupsᵉ

open import lists.concatenation-listsᵉ
open import lists.listsᵉ

open import structured-types.h-spacesᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.pointed-types-equipped-with-automorphismsᵉ
```

</details>

## Idea

Anᵉ **abstractᵉ group**ᵉ isᵉ aᵉ groupᵉ in theᵉ usualᵉ algebraicᵉ sense,ᵉ i.e.,ᵉ itᵉ consistsᵉ
ofᵉ aᵉ setᵉ equippedᵉ with aᵉ unitᵉ elementᵉ `e`,ᵉ aᵉ binaryᵉ operationᵉ `x,ᵉ yᵉ ↦ᵉ xy`,ᵉ andᵉ
anᵉ inverseᵉ operationᵉ `xᵉ ↦ᵉ x⁻¹`ᵉ satisfyingᵉ theᵉ groupᵉ lawsᵉ

```text
  (xy)zᵉ = x(yzᵉ)      (associativityᵉ)
     exᵉ = xᵉ          (leftᵉ unitᵉ lawᵉ)
     xeᵉ = xᵉ          (rightᵉ unitᵉ lawᵉ)
   x⁻¹xᵉ = eᵉ          (leftᵉ inverseᵉ lawᵉ)
   xx⁻¹ᵉ = eᵉ          (rightᵉ inverseᵉ lawᵉ)
```

## Definition

### The condition that a semigroup is a group

```agda
is-group-is-unital-Semigroupᵉ :
  {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ) → is-unital-Semigroupᵉ Gᵉ → UUᵉ lᵉ
is-group-is-unital-Semigroupᵉ Gᵉ is-unital-Semigroup-Gᵉ =
  Σᵉ ( type-Semigroupᵉ Gᵉ → type-Semigroupᵉ Gᵉ)
    ( λ iᵉ →
      ( (xᵉ : type-Semigroupᵉ Gᵉ) →
        Idᵉ (mul-Semigroupᵉ Gᵉ (iᵉ xᵉ) xᵉ) (pr1ᵉ is-unital-Semigroup-Gᵉ)) ×ᵉ
      ( (xᵉ : type-Semigroupᵉ Gᵉ) →
        Idᵉ (mul-Semigroupᵉ Gᵉ xᵉ (iᵉ xᵉ)) (pr1ᵉ is-unital-Semigroup-Gᵉ)))

is-group-Semigroupᵉ :
  {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ) → UUᵉ lᵉ
is-group-Semigroupᵉ Gᵉ =
  Σᵉ (is-unital-Semigroupᵉ Gᵉ) (is-group-is-unital-Semigroupᵉ Gᵉ)
```

### The type of groups

```agda
Groupᵉ :
  (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Groupᵉ lᵉ = Σᵉ (Semigroupᵉ lᵉ) is-group-Semigroupᵉ

module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  semigroup-Groupᵉ : Semigroupᵉ lᵉ
  semigroup-Groupᵉ = pr1ᵉ Gᵉ

  set-Groupᵉ : Setᵉ lᵉ
  set-Groupᵉ = pr1ᵉ semigroup-Groupᵉ

  type-Groupᵉ : UUᵉ lᵉ
  type-Groupᵉ = pr1ᵉ set-Groupᵉ

  is-set-type-Groupᵉ : is-setᵉ type-Groupᵉ
  is-set-type-Groupᵉ = pr2ᵉ set-Groupᵉ

  has-associative-mul-Groupᵉ : has-associative-mulᵉ type-Groupᵉ
  has-associative-mul-Groupᵉ = pr2ᵉ semigroup-Groupᵉ

  mul-Groupᵉ : type-Groupᵉ → type-Groupᵉ → type-Groupᵉ
  mul-Groupᵉ = pr1ᵉ has-associative-mul-Groupᵉ

  ap-mul-Groupᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Groupᵉ} (pᵉ : Idᵉ xᵉ x'ᵉ) (qᵉ : Idᵉ yᵉ y'ᵉ) →
    Idᵉ (mul-Groupᵉ xᵉ yᵉ) (mul-Groupᵉ x'ᵉ y'ᵉ)
  ap-mul-Groupᵉ pᵉ qᵉ = ap-binaryᵉ mul-Groupᵉ pᵉ qᵉ

  mul-Group'ᵉ : type-Groupᵉ → type-Groupᵉ → type-Groupᵉ
  mul-Group'ᵉ xᵉ yᵉ = mul-Groupᵉ yᵉ xᵉ

  associative-mul-Groupᵉ :
    (xᵉ yᵉ zᵉ : type-Groupᵉ) →
    Idᵉ (mul-Groupᵉ (mul-Groupᵉ xᵉ yᵉ) zᵉ) (mul-Groupᵉ xᵉ (mul-Groupᵉ yᵉ zᵉ))
  associative-mul-Groupᵉ = pr2ᵉ has-associative-mul-Groupᵉ

  is-group-Groupᵉ : is-group-Semigroupᵉ semigroup-Groupᵉ
  is-group-Groupᵉ = pr2ᵉ Gᵉ

  is-unital-Groupᵉ : is-unital-Semigroupᵉ semigroup-Groupᵉ
  is-unital-Groupᵉ = pr1ᵉ is-group-Groupᵉ

  monoid-Groupᵉ : Monoidᵉ lᵉ
  pr1ᵉ monoid-Groupᵉ = semigroup-Groupᵉ
  pr2ᵉ monoid-Groupᵉ = is-unital-Groupᵉ

  unit-Groupᵉ : type-Groupᵉ
  unit-Groupᵉ = pr1ᵉ is-unital-Groupᵉ

  is-unit-Groupᵉ : type-Groupᵉ → UUᵉ lᵉ
  is-unit-Groupᵉ xᵉ = xᵉ ＝ᵉ unit-Groupᵉ

  is-unit-Group'ᵉ : type-Groupᵉ → UUᵉ lᵉ
  is-unit-Group'ᵉ xᵉ = unit-Groupᵉ ＝ᵉ xᵉ

  is-prop-is-unit-Groupᵉ : (xᵉ : type-Groupᵉ) → is-propᵉ (is-unit-Groupᵉ xᵉ)
  is-prop-is-unit-Groupᵉ xᵉ = is-set-type-Groupᵉ xᵉ unit-Groupᵉ

  is-prop-is-unit-Group'ᵉ : (xᵉ : type-Groupᵉ) → is-propᵉ (is-unit-Group'ᵉ xᵉ)
  is-prop-is-unit-Group'ᵉ xᵉ = is-set-type-Groupᵉ unit-Groupᵉ xᵉ

  is-unit-prop-Groupᵉ : type-Groupᵉ → Propᵉ lᵉ
  pr1ᵉ (is-unit-prop-Groupᵉ xᵉ) = is-unit-Groupᵉ xᵉ
  pr2ᵉ (is-unit-prop-Groupᵉ xᵉ) = is-prop-is-unit-Groupᵉ xᵉ

  is-unit-prop-Group'ᵉ : type-Groupᵉ → Propᵉ lᵉ
  pr1ᵉ (is-unit-prop-Group'ᵉ xᵉ) = is-unit-Group'ᵉ xᵉ
  pr2ᵉ (is-unit-prop-Group'ᵉ xᵉ) = is-prop-is-unit-Group'ᵉ xᵉ

  left-unit-law-mul-Groupᵉ :
    (xᵉ : type-Groupᵉ) → Idᵉ (mul-Groupᵉ unit-Groupᵉ xᵉ) xᵉ
  left-unit-law-mul-Groupᵉ = pr1ᵉ (pr2ᵉ is-unital-Groupᵉ)

  right-unit-law-mul-Groupᵉ :
    (xᵉ : type-Groupᵉ) → Idᵉ (mul-Groupᵉ xᵉ unit-Groupᵉ) xᵉ
  right-unit-law-mul-Groupᵉ = pr2ᵉ (pr2ᵉ is-unital-Groupᵉ)

  coherence-unit-laws-mul-Groupᵉ :
    left-unit-law-mul-Groupᵉ unit-Groupᵉ ＝ᵉ right-unit-law-mul-Groupᵉ unit-Groupᵉ
  coherence-unit-laws-mul-Groupᵉ =
    eq-is-propᵉ (is-set-type-Groupᵉ _ _)

  pointed-type-Groupᵉ : Pointed-Typeᵉ lᵉ
  pr1ᵉ pointed-type-Groupᵉ = type-Groupᵉ
  pr2ᵉ pointed-type-Groupᵉ = unit-Groupᵉ

  h-space-Groupᵉ : H-Spaceᵉ lᵉ
  pr1ᵉ h-space-Groupᵉ = pointed-type-Groupᵉ
  pr1ᵉ (pr2ᵉ h-space-Groupᵉ) = mul-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ h-space-Groupᵉ)) = left-unit-law-mul-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ h-space-Groupᵉ))) = right-unit-law-mul-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ h-space-Groupᵉ))) = coherence-unit-laws-mul-Groupᵉ

  has-inverses-Groupᵉ :
    is-group-is-unital-Semigroupᵉ semigroup-Groupᵉ is-unital-Groupᵉ
  has-inverses-Groupᵉ = pr2ᵉ is-group-Groupᵉ

  inv-Groupᵉ : type-Groupᵉ → type-Groupᵉ
  inv-Groupᵉ = pr1ᵉ has-inverses-Groupᵉ

  left-inverse-law-mul-Groupᵉ :
    (xᵉ : type-Groupᵉ) → Idᵉ (mul-Groupᵉ (inv-Groupᵉ xᵉ) xᵉ) unit-Groupᵉ
  left-inverse-law-mul-Groupᵉ = pr1ᵉ (pr2ᵉ has-inverses-Groupᵉ)

  right-inverse-law-mul-Groupᵉ :
    (xᵉ : type-Groupᵉ) → Idᵉ (mul-Groupᵉ xᵉ (inv-Groupᵉ xᵉ)) unit-Groupᵉ
  right-inverse-law-mul-Groupᵉ = pr2ᵉ (pr2ᵉ has-inverses-Groupᵉ)

  is-invertible-element-Groupᵉ :
    (xᵉ : type-Groupᵉ) → is-invertible-element-Monoidᵉ monoid-Groupᵉ xᵉ
  pr1ᵉ (is-invertible-element-Groupᵉ xᵉ) = inv-Groupᵉ xᵉ
  pr1ᵉ (pr2ᵉ (is-invertible-element-Groupᵉ xᵉ)) = right-inverse-law-mul-Groupᵉ xᵉ
  pr2ᵉ (pr2ᵉ (is-invertible-element-Groupᵉ xᵉ)) = left-inverse-law-mul-Groupᵉ xᵉ

  inv-unit-Groupᵉ :
    Idᵉ (inv-Groupᵉ unit-Groupᵉ) unit-Groupᵉ
  inv-unit-Groupᵉ =
    ( invᵉ (left-unit-law-mul-Groupᵉ (inv-Groupᵉ unit-Groupᵉ))) ∙ᵉ
    ( right-inverse-law-mul-Groupᵉ unit-Groupᵉ)

  left-swap-mul-Groupᵉ :
    {xᵉ yᵉ zᵉ : type-Groupᵉ} → mul-Groupᵉ xᵉ yᵉ ＝ᵉ mul-Groupᵉ yᵉ xᵉ →
    mul-Groupᵉ xᵉ (mul-Groupᵉ yᵉ zᵉ) ＝ᵉ
    mul-Groupᵉ yᵉ (mul-Groupᵉ xᵉ zᵉ)
  left-swap-mul-Groupᵉ =
    left-swap-mul-Semigroupᵉ semigroup-Groupᵉ

  right-swap-mul-Groupᵉ :
    {xᵉ yᵉ zᵉ : type-Groupᵉ} → mul-Groupᵉ yᵉ zᵉ ＝ᵉ mul-Groupᵉ zᵉ yᵉ →
    mul-Groupᵉ (mul-Groupᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Groupᵉ (mul-Groupᵉ xᵉ zᵉ) yᵉ
  right-swap-mul-Groupᵉ =
    right-swap-mul-Semigroupᵉ semigroup-Groupᵉ

  interchange-mul-mul-Groupᵉ :
    {xᵉ yᵉ zᵉ wᵉ : type-Groupᵉ} → mul-Groupᵉ yᵉ zᵉ ＝ᵉ mul-Groupᵉ zᵉ yᵉ →
    mul-Groupᵉ (mul-Groupᵉ xᵉ yᵉ) (mul-Groupᵉ zᵉ wᵉ) ＝ᵉ
    mul-Groupᵉ (mul-Groupᵉ xᵉ zᵉ) (mul-Groupᵉ yᵉ wᵉ)
  interchange-mul-mul-Groupᵉ =
    interchange-mul-mul-Semigroupᵉ semigroup-Groupᵉ
```

### The structure of a group

```agda
structure-groupᵉ :
  {l1ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l1ᵉ
structure-groupᵉ Xᵉ =
  Σᵉ ( structure-semigroupᵉ Xᵉ)
    ( λ pᵉ → is-group-Semigroupᵉ (semigroup-structure-semigroupᵉ Xᵉ pᵉ))

group-structure-groupᵉ :
  {l1ᵉ : Level} → (Xᵉ : UUᵉ l1ᵉ) → structure-groupᵉ Xᵉ → Groupᵉ l1ᵉ
pr1ᵉ (group-structure-groupᵉ Xᵉ (pᵉ ,ᵉ qᵉ)) = semigroup-structure-semigroupᵉ Xᵉ pᵉ
pr2ᵉ (group-structure-groupᵉ Xᵉ (pᵉ ,ᵉ qᵉ)) = qᵉ
```

## Properties

### Multiplication by `x` from the left is an equivalence

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  left-div-Groupᵉ : type-Groupᵉ Gᵉ → type-Groupᵉ Gᵉ → type-Groupᵉ Gᵉ
  left-div-Groupᵉ xᵉ =
    left-div-is-invertible-element-Monoidᵉ
      ( monoid-Groupᵉ Gᵉ)
      ( is-invertible-element-Groupᵉ Gᵉ xᵉ)

  ap-left-div-Groupᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Groupᵉ Gᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ →
    left-div-Groupᵉ xᵉ yᵉ ＝ᵉ left-div-Groupᵉ x'ᵉ y'ᵉ
  ap-left-div-Groupᵉ pᵉ qᵉ = ap-binaryᵉ left-div-Groupᵉ pᵉ qᵉ

  is-section-left-div-Groupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) → (mul-Groupᵉ Gᵉ xᵉ ∘ᵉ left-div-Groupᵉ xᵉ) ~ᵉ idᵉ
  is-section-left-div-Groupᵉ xᵉ =
    is-section-left-div-is-invertible-element-Monoidᵉ
      ( monoid-Groupᵉ Gᵉ)
      ( is-invertible-element-Groupᵉ Gᵉ xᵉ)

  is-retraction-left-div-Groupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) → (left-div-Groupᵉ xᵉ ∘ᵉ mul-Groupᵉ Gᵉ xᵉ) ~ᵉ idᵉ
  is-retraction-left-div-Groupᵉ xᵉ =
    is-retraction-left-div-is-invertible-element-Monoidᵉ
      ( monoid-Groupᵉ Gᵉ)
      ( is-invertible-element-Groupᵉ Gᵉ xᵉ)

  is-equiv-mul-Groupᵉ : (xᵉ : type-Groupᵉ Gᵉ) → is-equivᵉ (mul-Groupᵉ Gᵉ xᵉ)
  is-equiv-mul-Groupᵉ xᵉ =
    is-equiv-mul-is-invertible-element-Monoidᵉ
      ( monoid-Groupᵉ Gᵉ)
      ( is-invertible-element-Groupᵉ Gᵉ xᵉ)

  equiv-mul-Groupᵉ : (xᵉ : type-Groupᵉ Gᵉ) → type-Groupᵉ Gᵉ ≃ᵉ type-Groupᵉ Gᵉ
  pr1ᵉ (equiv-mul-Groupᵉ xᵉ) = mul-Groupᵉ Gᵉ xᵉ
  pr2ᵉ (equiv-mul-Groupᵉ xᵉ) = is-equiv-mul-Groupᵉ xᵉ

  is-equiv-left-div-Groupᵉ : (xᵉ : type-Groupᵉ Gᵉ) → is-equivᵉ (left-div-Groupᵉ xᵉ)
  is-equiv-left-div-Groupᵉ xᵉ =
    is-equiv-is-invertibleᵉ
      ( mul-Groupᵉ Gᵉ xᵉ)
      ( is-retraction-left-div-Groupᵉ xᵉ)
      ( is-section-left-div-Groupᵉ xᵉ)

  equiv-left-div-Groupᵉ : (xᵉ : type-Groupᵉ Gᵉ) → type-Groupᵉ Gᵉ ≃ᵉ type-Groupᵉ Gᵉ
  pr1ᵉ (equiv-left-div-Groupᵉ xᵉ) = left-div-Groupᵉ xᵉ
  pr2ᵉ (equiv-left-div-Groupᵉ xᵉ) = is-equiv-left-div-Groupᵉ xᵉ
```

### Multiplication by `x` from the right is an equivalence

```agda
  right-div-Groupᵉ : type-Groupᵉ Gᵉ → type-Groupᵉ Gᵉ → type-Groupᵉ Gᵉ
  right-div-Groupᵉ xᵉ yᵉ =
    right-div-is-invertible-element-Monoidᵉ
      ( monoid-Groupᵉ Gᵉ)
      ( is-invertible-element-Groupᵉ Gᵉ yᵉ)
      ( xᵉ)

  ap-right-div-Groupᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Groupᵉ Gᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ →
    right-div-Groupᵉ xᵉ yᵉ ＝ᵉ right-div-Groupᵉ x'ᵉ y'ᵉ
  ap-right-div-Groupᵉ pᵉ qᵉ = ap-binaryᵉ right-div-Groupᵉ pᵉ qᵉ

  is-section-right-div-Groupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) → (mul-Group'ᵉ Gᵉ xᵉ ∘ᵉ (λ yᵉ → right-div-Groupᵉ yᵉ xᵉ)) ~ᵉ idᵉ
  is-section-right-div-Groupᵉ xᵉ =
    is-section-right-div-is-invertible-element-Monoidᵉ
      ( monoid-Groupᵉ Gᵉ)
      ( is-invertible-element-Groupᵉ Gᵉ xᵉ)

  is-retraction-right-div-Groupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) → ((λ yᵉ → right-div-Groupᵉ yᵉ xᵉ) ∘ᵉ mul-Group'ᵉ Gᵉ xᵉ) ~ᵉ idᵉ
  is-retraction-right-div-Groupᵉ xᵉ =
    is-retraction-right-div-is-invertible-element-Monoidᵉ
      ( monoid-Groupᵉ Gᵉ)
      ( is-invertible-element-Groupᵉ Gᵉ xᵉ)

  is-equiv-mul-Group'ᵉ : (xᵉ : type-Groupᵉ Gᵉ) → is-equivᵉ (mul-Group'ᵉ Gᵉ xᵉ)
  is-equiv-mul-Group'ᵉ xᵉ =
    is-equiv-is-invertibleᵉ
      ( λ yᵉ → right-div-Groupᵉ yᵉ xᵉ)
      ( is-section-right-div-Groupᵉ xᵉ)
      ( is-retraction-right-div-Groupᵉ xᵉ)

  equiv-mul-Group'ᵉ : (xᵉ : type-Groupᵉ Gᵉ) → type-Groupᵉ Gᵉ ≃ᵉ type-Groupᵉ Gᵉ
  pr1ᵉ (equiv-mul-Group'ᵉ xᵉ) = mul-Group'ᵉ Gᵉ xᵉ
  pr2ᵉ (equiv-mul-Group'ᵉ xᵉ) = is-equiv-mul-Group'ᵉ xᵉ

  is-equiv-right-div-Groupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) → is-equivᵉ (λ yᵉ → right-div-Groupᵉ yᵉ xᵉ)
  is-equiv-right-div-Groupᵉ xᵉ =
    is-equiv-is-invertibleᵉ
      ( mul-Group'ᵉ Gᵉ xᵉ)
      ( is-retraction-right-div-Groupᵉ xᵉ)
      ( is-section-right-div-Groupᵉ xᵉ)

  equiv-right-div-Groupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) → type-Groupᵉ Gᵉ ≃ᵉ type-Groupᵉ Gᵉ
  pr1ᵉ (equiv-right-div-Groupᵉ xᵉ) yᵉ = right-div-Groupᵉ yᵉ xᵉ
  pr2ᵉ (equiv-right-div-Groupᵉ xᵉ) = is-equiv-right-div-Groupᵉ xᵉ
```

### Multiplication is a binary equivalence and a binary embedding

```agda
  is-binary-equiv-mul-Groupᵉ : is-binary-equivᵉ (mul-Groupᵉ Gᵉ)
  pr1ᵉ is-binary-equiv-mul-Groupᵉ = is-equiv-mul-Group'ᵉ
  pr2ᵉ is-binary-equiv-mul-Groupᵉ = is-equiv-mul-Groupᵉ

  is-binary-emb-mul-Groupᵉ : is-binary-embᵉ (mul-Groupᵉ Gᵉ)
  is-binary-emb-mul-Groupᵉ =
    is-binary-emb-is-binary-equivᵉ is-binary-equiv-mul-Groupᵉ

  is-emb-mul-Groupᵉ : (xᵉ : type-Groupᵉ Gᵉ) → is-embᵉ (mul-Groupᵉ Gᵉ xᵉ)
  is-emb-mul-Groupᵉ xᵉ = is-emb-is-equivᵉ (is-equiv-mul-Groupᵉ xᵉ)

  is-emb-mul-Group'ᵉ : (xᵉ : type-Groupᵉ Gᵉ) → is-embᵉ (mul-Group'ᵉ Gᵉ xᵉ)
  is-emb-mul-Group'ᵉ xᵉ = is-emb-is-equivᵉ (is-equiv-mul-Group'ᵉ xᵉ)

  is-injective-mul-Groupᵉ : (xᵉ : type-Groupᵉ Gᵉ) → is-injectiveᵉ (mul-Groupᵉ Gᵉ xᵉ)
  is-injective-mul-Groupᵉ xᵉ = is-injective-is-equivᵉ (is-equiv-mul-Groupᵉ xᵉ)

  is-injective-mul-Group'ᵉ : (xᵉ : type-Groupᵉ Gᵉ) → is-injectiveᵉ (mul-Group'ᵉ Gᵉ xᵉ)
  is-injective-mul-Group'ᵉ xᵉ = is-injective-is-equivᵉ (is-equiv-mul-Group'ᵉ xᵉ)
```

### Transposition laws for equalities in groups

```agda
  transpose-eq-mul-Groupᵉ :
    {xᵉ yᵉ zᵉ : type-Groupᵉ Gᵉ} → mul-Groupᵉ Gᵉ xᵉ yᵉ ＝ᵉ zᵉ → xᵉ ＝ᵉ right-div-Groupᵉ zᵉ yᵉ
  transpose-eq-mul-Groupᵉ {xᵉ} {yᵉ} {zᵉ} reflᵉ =
    invᵉ (is-retraction-right-div-Groupᵉ yᵉ xᵉ)

  inv-transpose-eq-mul-Groupᵉ :
    {xᵉ yᵉ zᵉ : type-Groupᵉ Gᵉ} → xᵉ ＝ᵉ right-div-Groupᵉ zᵉ yᵉ → mul-Groupᵉ Gᵉ xᵉ yᵉ ＝ᵉ zᵉ
  inv-transpose-eq-mul-Groupᵉ {.ᵉ_} {yᵉ} {zᵉ} reflᵉ =
    is-section-right-div-Groupᵉ yᵉ zᵉ

  transpose-eq-mul-Group'ᵉ :
    {xᵉ yᵉ zᵉ : type-Groupᵉ Gᵉ} → mul-Groupᵉ Gᵉ xᵉ yᵉ ＝ᵉ zᵉ → yᵉ ＝ᵉ left-div-Groupᵉ xᵉ zᵉ
  transpose-eq-mul-Group'ᵉ {xᵉ} {yᵉ} {zᵉ} reflᵉ =
    invᵉ (is-retraction-left-div-Groupᵉ xᵉ yᵉ)

  inv-transpose-eq-mul-Group'ᵉ :
    {xᵉ yᵉ zᵉ : type-Groupᵉ Gᵉ} → yᵉ ＝ᵉ left-div-Groupᵉ xᵉ zᵉ → mul-Groupᵉ Gᵉ xᵉ yᵉ ＝ᵉ zᵉ
  inv-transpose-eq-mul-Group'ᵉ {xᵉ} {yᵉ} {.ᵉ_} reflᵉ =
    is-section-left-div-Groupᵉ xᵉ _

  double-transpose-eq-mul-Groupᵉ :
    {xᵉ yᵉ zᵉ wᵉ : type-Groupᵉ Gᵉ} →
    mul-Groupᵉ Gᵉ yᵉ wᵉ ＝ᵉ mul-Groupᵉ Gᵉ xᵉ zᵉ →
    left-div-Groupᵉ xᵉ yᵉ ＝ᵉ right-div-Groupᵉ zᵉ wᵉ
  double-transpose-eq-mul-Groupᵉ pᵉ =
    invᵉ
      ( transpose-eq-mul-Group'ᵉ
        ( invᵉ (transpose-eq-mul-Groupᵉ pᵉ ∙ᵉ associative-mul-Groupᵉ Gᵉ _ _ _)))

  double-transpose-eq-mul-Group'ᵉ :
    {xᵉ yᵉ zᵉ wᵉ : type-Groupᵉ Gᵉ} →
    mul-Groupᵉ Gᵉ zᵉ xᵉ ＝ᵉ mul-Groupᵉ Gᵉ wᵉ yᵉ →
    right-div-Groupᵉ xᵉ yᵉ ＝ᵉ left-div-Groupᵉ zᵉ wᵉ
  double-transpose-eq-mul-Group'ᵉ pᵉ =
    invᵉ (double-transpose-eq-mul-Groupᵉ (invᵉ pᵉ))
```

### Distributivity of inverses over multiplication

```agda
  distributive-inv-mul-Groupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    inv-Groupᵉ Gᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ) ＝ᵉ
    mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ yᵉ) (inv-Groupᵉ Gᵉ xᵉ)
  distributive-inv-mul-Groupᵉ {xᵉ} {yᵉ} =
    transpose-eq-mul-Groupᵉ
      ( ( transpose-eq-mul-Groupᵉ
          ( ( associative-mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ)) xᵉ yᵉ) ∙ᵉ
            ( left-inverse-law-mul-Groupᵉ Gᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ)))) ∙ᵉ
        ( left-unit-law-mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ yᵉ)))

  distributive-inv-mul-Group'ᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → mul-Groupᵉ Gᵉ xᵉ yᵉ ＝ᵉ mul-Groupᵉ Gᵉ yᵉ xᵉ →
    inv-Groupᵉ Gᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ) ＝ᵉ mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ) (inv-Groupᵉ Gᵉ yᵉ)
  distributive-inv-mul-Group'ᵉ xᵉ yᵉ Hᵉ =
    ( distributive-inv-mul-Groupᵉ) ∙ᵉ
    ( invᵉ (double-transpose-eq-mul-Groupᵉ (double-transpose-eq-mul-Groupᵉ Hᵉ)))
```

### Inverting elements of a group is an involution

```agda
  inv-inv-Groupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) → Idᵉ (inv-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ)) xᵉ
  inv-inv-Groupᵉ xᵉ =
    is-injective-mul-Groupᵉ
      ( inv-Groupᵉ Gᵉ xᵉ)
      ( ( right-inverse-law-mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ)) ∙ᵉ
        ( invᵉ (left-inverse-law-mul-Groupᵉ Gᵉ xᵉ)))

  transpose-eq-inv-Groupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    inv-Groupᵉ Gᵉ xᵉ ＝ᵉ yᵉ → xᵉ ＝ᵉ inv-Groupᵉ Gᵉ yᵉ
  transpose-eq-inv-Groupᵉ reflᵉ = invᵉ (inv-inv-Groupᵉ _)

  transpose-eq-inv-Group'ᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    xᵉ ＝ᵉ inv-Groupᵉ Gᵉ yᵉ → inv-Groupᵉ Gᵉ xᵉ ＝ᵉ yᵉ
  transpose-eq-inv-Group'ᵉ reflᵉ = inv-inv-Groupᵉ _
```

### Inverting elements of a group is an equivalence

```agda
  is-equiv-inv-Groupᵉ : is-equivᵉ (inv-Groupᵉ Gᵉ)
  is-equiv-inv-Groupᵉ = is-equiv-is-involutionᵉ inv-inv-Groupᵉ

  equiv-equiv-inv-Groupᵉ : type-Groupᵉ Gᵉ ≃ᵉ type-Groupᵉ Gᵉ
  pr1ᵉ equiv-equiv-inv-Groupᵉ = inv-Groupᵉ Gᵉ
  pr2ᵉ equiv-equiv-inv-Groupᵉ = is-equiv-inv-Groupᵉ
```

### Two elements `x` and `y` are equal iff `x⁻¹y=1`

```agda
  eq-is-unit-left-div-Groupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} → is-unit-Groupᵉ Gᵉ (left-div-Groupᵉ xᵉ yᵉ) → xᵉ ＝ᵉ yᵉ
  eq-is-unit-left-div-Groupᵉ {xᵉ} {yᵉ} Hᵉ =
    ( invᵉ (right-unit-law-mul-Groupᵉ Gᵉ xᵉ)) ∙ᵉ
    ( inv-transpose-eq-mul-Group'ᵉ (invᵉ Hᵉ))

  is-unit-left-div-eq-Groupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} → xᵉ ＝ᵉ yᵉ → is-unit-Groupᵉ Gᵉ (left-div-Groupᵉ xᵉ yᵉ)
  is-unit-left-div-eq-Groupᵉ reflᵉ = left-inverse-law-mul-Groupᵉ Gᵉ _
```

### Two elements `x` and `y` are equal iff `xy⁻¹=1`

```agda
  eq-is-unit-right-div-Groupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} → is-unit-Groupᵉ Gᵉ (right-div-Groupᵉ xᵉ yᵉ) → xᵉ ＝ᵉ yᵉ
  eq-is-unit-right-div-Groupᵉ Hᵉ =
    invᵉ (inv-transpose-eq-mul-Groupᵉ (invᵉ Hᵉ)) ∙ᵉ left-unit-law-mul-Groupᵉ Gᵉ _

  is-unit-right-div-eq-Groupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} → xᵉ ＝ᵉ yᵉ → is-unit-Groupᵉ Gᵉ (right-div-Groupᵉ xᵉ yᵉ)
  is-unit-right-div-eq-Groupᵉ reflᵉ = right-inverse-law-mul-Groupᵉ Gᵉ _
```

### The inverse of `x⁻¹y` is `y⁻¹x`

```agda
  inv-left-div-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    inv-Groupᵉ Gᵉ (left-div-Groupᵉ xᵉ yᵉ) ＝ᵉ left-div-Groupᵉ yᵉ xᵉ
  inv-left-div-Groupᵉ xᵉ yᵉ =
    equational-reasoningᵉ
      inv-Groupᵉ Gᵉ (left-div-Groupᵉ xᵉ yᵉ)
      ＝ᵉ left-div-Groupᵉ yᵉ (inv-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ))
        byᵉ distributive-inv-mul-Groupᵉ
      ＝ᵉ left-div-Groupᵉ yᵉ xᵉ
        byᵉ apᵉ (left-div-Groupᵉ yᵉ) (inv-inv-Groupᵉ xᵉ)
```

### The inverse of `xy⁻¹` is `yx⁻¹`

```agda
  inv-right-div-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    inv-Groupᵉ Gᵉ (right-div-Groupᵉ xᵉ yᵉ) ＝ᵉ right-div-Groupᵉ yᵉ xᵉ
  inv-right-div-Groupᵉ xᵉ yᵉ =
    equational-reasoningᵉ
      inv-Groupᵉ Gᵉ (right-div-Groupᵉ xᵉ yᵉ)
      ＝ᵉ right-div-Groupᵉ (inv-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ yᵉ)) xᵉ
        byᵉ distributive-inv-mul-Groupᵉ
      ＝ᵉ right-div-Groupᵉ yᵉ xᵉ
        byᵉ apᵉ (mul-Group'ᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ)) (inv-inv-Groupᵉ yᵉ)
```

### The product of `x⁻¹y` and `y⁻¹z` is `x⁻¹z`

```agda
  mul-left-div-Groupᵉ :
    (xᵉ yᵉ zᵉ : type-Groupᵉ Gᵉ) →
    mul-Groupᵉ Gᵉ (left-div-Groupᵉ xᵉ yᵉ) (left-div-Groupᵉ yᵉ zᵉ) ＝ᵉ left-div-Groupᵉ xᵉ zᵉ
  mul-left-div-Groupᵉ xᵉ yᵉ zᵉ =
    equational-reasoningᵉ
      mul-Groupᵉ Gᵉ (left-div-Groupᵉ xᵉ yᵉ) (left-div-Groupᵉ yᵉ zᵉ)
      ＝ᵉ mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ) (mul-Groupᵉ Gᵉ yᵉ (left-div-Groupᵉ yᵉ zᵉ))
        byᵉ associative-mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ) yᵉ (left-div-Groupᵉ yᵉ zᵉ)
      ＝ᵉ left-div-Groupᵉ xᵉ zᵉ
        byᵉ apᵉ (left-div-Groupᵉ xᵉ) (is-section-left-div-Groupᵉ yᵉ zᵉ)
```

### The product of `xy⁻¹` and `yz⁻¹` is `xz⁻¹`

```agda
  mul-right-div-Groupᵉ :
    (xᵉ yᵉ zᵉ : type-Groupᵉ Gᵉ) →
    mul-Groupᵉ Gᵉ (right-div-Groupᵉ xᵉ yᵉ) (right-div-Groupᵉ yᵉ zᵉ) ＝ᵉ
    right-div-Groupᵉ xᵉ zᵉ
  mul-right-div-Groupᵉ xᵉ yᵉ zᵉ =
    equational-reasoningᵉ
      mul-Groupᵉ Gᵉ (right-div-Groupᵉ xᵉ yᵉ) (right-div-Groupᵉ yᵉ zᵉ)
      ＝ᵉ mul-Groupᵉ Gᵉ xᵉ (mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ yᵉ) (right-div-Groupᵉ yᵉ zᵉ))
        byᵉ associative-mul-Groupᵉ Gᵉ xᵉ (inv-Groupᵉ Gᵉ yᵉ) (right-div-Groupᵉ yᵉ zᵉ)
      ＝ᵉ right-div-Groupᵉ xᵉ zᵉ
        byᵉ apᵉ (mul-Groupᵉ Gᵉ xᵉ) (is-retraction-left-div-Groupᵉ yᵉ (inv-Groupᵉ Gᵉ zᵉ))
```

### For any semigroup, being a group is a property

```agda
abstract
  all-elements-equal-is-group-Semigroupᵉ :
    {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ) (eᵉ : is-unital-Semigroupᵉ Gᵉ) →
    all-elements-equalᵉ (is-group-is-unital-Semigroupᵉ Gᵉ eᵉ)
  all-elements-equal-is-group-Semigroupᵉ
    ( pairᵉ Gᵉ (pairᵉ μᵉ associative-Gᵉ))
    ( pairᵉ eᵉ (pairᵉ left-unit-Gᵉ right-unit-Gᵉ))
    ( pairᵉ iᵉ (pairᵉ left-inv-iᵉ right-inv-iᵉ))
    ( pairᵉ i'ᵉ (pairᵉ left-inv-i'ᵉ right-inv-i'ᵉ)) =
    eq-type-subtypeᵉ
      ( λ iᵉ →
        product-Propᵉ
          ( Π-Propᵉ (type-Setᵉ Gᵉ) (λ xᵉ → Id-Propᵉ Gᵉ (μᵉ (iᵉ xᵉ) xᵉ) eᵉ))
          ( Π-Propᵉ (type-Setᵉ Gᵉ) (λ xᵉ → Id-Propᵉ Gᵉ (μᵉ xᵉ (iᵉ xᵉ)) eᵉ)))
      ( eq-htpyᵉ
        ( λ xᵉ →
          equational-reasoningᵉ
          iᵉ xᵉ
          ＝ᵉ μᵉ eᵉ (iᵉ xᵉ)
            byᵉ invᵉ (left-unit-Gᵉ (iᵉ xᵉ))
          ＝ᵉ μᵉ (μᵉ (i'ᵉ xᵉ) xᵉ) (iᵉ xᵉ)
            byᵉ apᵉ (λ yᵉ → μᵉ yᵉ (iᵉ xᵉ)) (invᵉ (left-inv-i'ᵉ xᵉ))
          ＝ᵉ μᵉ (i'ᵉ xᵉ) (μᵉ xᵉ (iᵉ xᵉ))
            byᵉ associative-Gᵉ (i'ᵉ xᵉ) xᵉ (iᵉ xᵉ)
          ＝ᵉ μᵉ (i'ᵉ xᵉ) eᵉ
            byᵉ apᵉ (μᵉ (i'ᵉ xᵉ)) (right-inv-iᵉ xᵉ)
          ＝ᵉ i'ᵉ xᵉ
            byᵉ right-unit-Gᵉ (i'ᵉ xᵉ)))

abstract
  is-prop-is-group-Semigroupᵉ :
    {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ) → is-propᵉ (is-group-Semigroupᵉ Gᵉ)
  is-prop-is-group-Semigroupᵉ Gᵉ =
    is-prop-Σᵉ
      ( is-prop-is-unital-Semigroupᵉ Gᵉ)
      ( λ eᵉ →
        is-prop-all-elements-equalᵉ (all-elements-equal-is-group-Semigroupᵉ Gᵉ eᵉ))

is-group-prop-Semigroupᵉ : {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ) → Propᵉ lᵉ
pr1ᵉ (is-group-prop-Semigroupᵉ Gᵉ) = is-group-Semigroupᵉ Gᵉ
pr2ᵉ (is-group-prop-Semigroupᵉ Gᵉ) = is-prop-is-group-Semigroupᵉ Gᵉ
```

### Any idempotent element in a group is the unit

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  is-idempotent-Groupᵉ : type-Groupᵉ Gᵉ → UUᵉ lᵉ
  is-idempotent-Groupᵉ xᵉ = Idᵉ (mul-Groupᵉ Gᵉ xᵉ xᵉ) xᵉ

  is-unit-is-idempotent-Groupᵉ :
    {xᵉ : type-Groupᵉ Gᵉ} → is-idempotent-Groupᵉ xᵉ → is-unit-Groupᵉ Gᵉ xᵉ
  is-unit-is-idempotent-Groupᵉ {xᵉ} pᵉ =
    is-injective-mul-Groupᵉ Gᵉ xᵉ (pᵉ ∙ᵉ invᵉ (right-unit-law-mul-Groupᵉ Gᵉ xᵉ))
```

### Multiplication of a list of elements in a group

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  mul-list-Groupᵉ : listᵉ (type-Groupᵉ Gᵉ) → type-Groupᵉ Gᵉ
  mul-list-Groupᵉ = mul-list-Monoidᵉ (monoid-Groupᵉ Gᵉ)

  preserves-concat-mul-list-Groupᵉ :
    (l1ᵉ l2ᵉ : listᵉ (type-Groupᵉ Gᵉ)) →
    Idᵉ
      ( mul-list-Groupᵉ (concat-listᵉ l1ᵉ l2ᵉ))
      ( mul-Groupᵉ Gᵉ (mul-list-Groupᵉ l1ᵉ) (mul-list-Groupᵉ l2ᵉ))
  preserves-concat-mul-list-Groupᵉ =
    distributive-mul-concat-list-Monoidᵉ (monoid-Groupᵉ Gᵉ)
```

### Any group element yields a type equipped with an automorphism

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ) (gᵉ : type-Groupᵉ Gᵉ)
  where

  pointed-type-with-aut-Groupᵉ : Pointed-Type-With-Autᵉ lᵉ
  pr1ᵉ pointed-type-with-aut-Groupᵉ = pointed-type-Groupᵉ Gᵉ
  pr2ᵉ pointed-type-with-aut-Groupᵉ = equiv-mul-Groupᵉ Gᵉ gᵉ
```