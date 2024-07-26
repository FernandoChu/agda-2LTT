# Monoids

```agda
module group-theory.monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.unit-typeᵉ
open import foundation.unital-binary-operationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.semigroupsᵉ

open import structured-types.h-spacesᵉ
open import structured-types.wild-monoidsᵉ
```

</details>

## Idea

**Monoids**ᵉ areᵉ [unital](foundation.unital-binary-operations.mdᵉ)
[semigroups](group-theory.semigroups.md).ᵉ

## Definition

```agda
is-unital-Semigroupᵉ :
  {lᵉ : Level} → Semigroupᵉ lᵉ → UUᵉ lᵉ
is-unital-Semigroupᵉ Gᵉ = is-unitalᵉ (mul-Semigroupᵉ Gᵉ)

Monoidᵉ :
  (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Monoidᵉ lᵉ = Σᵉ (Semigroupᵉ lᵉ) is-unital-Semigroupᵉ

module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  semigroup-Monoidᵉ : Semigroupᵉ lᵉ
  semigroup-Monoidᵉ = pr1ᵉ Mᵉ

  is-unital-Monoidᵉ : is-unital-Semigroupᵉ semigroup-Monoidᵉ
  is-unital-Monoidᵉ = pr2ᵉ Mᵉ

  type-Monoidᵉ : UUᵉ lᵉ
  type-Monoidᵉ = type-Semigroupᵉ semigroup-Monoidᵉ

  set-Monoidᵉ : Setᵉ lᵉ
  set-Monoidᵉ = set-Semigroupᵉ semigroup-Monoidᵉ

  is-set-type-Monoidᵉ : is-setᵉ type-Monoidᵉ
  is-set-type-Monoidᵉ = is-set-type-Semigroupᵉ semigroup-Monoidᵉ

  mul-Monoidᵉ : type-Monoidᵉ → type-Monoidᵉ → type-Monoidᵉ
  mul-Monoidᵉ = mul-Semigroupᵉ semigroup-Monoidᵉ

  mul-Monoid'ᵉ : type-Monoidᵉ → type-Monoidᵉ → type-Monoidᵉ
  mul-Monoid'ᵉ yᵉ xᵉ = mul-Monoidᵉ xᵉ yᵉ

  ap-mul-Monoidᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Monoidᵉ} →
    xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → mul-Monoidᵉ xᵉ yᵉ ＝ᵉ mul-Monoidᵉ x'ᵉ y'ᵉ
  ap-mul-Monoidᵉ = ap-mul-Semigroupᵉ semigroup-Monoidᵉ

  associative-mul-Monoidᵉ :
    (xᵉ yᵉ zᵉ : type-Monoidᵉ) →
    mul-Monoidᵉ (mul-Monoidᵉ xᵉ yᵉ) zᵉ ＝ᵉ mul-Monoidᵉ xᵉ (mul-Monoidᵉ yᵉ zᵉ)
  associative-mul-Monoidᵉ = associative-mul-Semigroupᵉ semigroup-Monoidᵉ

  has-unit-Monoidᵉ : is-unitalᵉ mul-Monoidᵉ
  has-unit-Monoidᵉ = pr2ᵉ Mᵉ

  unit-Monoidᵉ : type-Monoidᵉ
  unit-Monoidᵉ = pr1ᵉ has-unit-Monoidᵉ

  left-unit-law-mul-Monoidᵉ : (xᵉ : type-Monoidᵉ) → mul-Monoidᵉ unit-Monoidᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Monoidᵉ = pr1ᵉ (pr2ᵉ has-unit-Monoidᵉ)

  right-unit-law-mul-Monoidᵉ : (xᵉ : type-Monoidᵉ) → mul-Monoidᵉ xᵉ unit-Monoidᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Monoidᵉ = pr2ᵉ (pr2ᵉ has-unit-Monoidᵉ)

  left-swap-mul-Monoidᵉ :
    {xᵉ yᵉ zᵉ : type-Monoidᵉ} → mul-Monoidᵉ xᵉ yᵉ ＝ᵉ mul-Monoidᵉ yᵉ xᵉ →
    mul-Monoidᵉ xᵉ (mul-Monoidᵉ yᵉ zᵉ) ＝ᵉ
    mul-Monoidᵉ yᵉ (mul-Monoidᵉ xᵉ zᵉ)
  left-swap-mul-Monoidᵉ =
    left-swap-mul-Semigroupᵉ semigroup-Monoidᵉ

  right-swap-mul-Monoidᵉ :
    {xᵉ yᵉ zᵉ : type-Monoidᵉ} → mul-Monoidᵉ yᵉ zᵉ ＝ᵉ mul-Monoidᵉ zᵉ yᵉ →
    mul-Monoidᵉ (mul-Monoidᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Monoidᵉ (mul-Monoidᵉ xᵉ zᵉ) yᵉ
  right-swap-mul-Monoidᵉ =
    right-swap-mul-Semigroupᵉ semigroup-Monoidᵉ

  interchange-mul-mul-Monoidᵉ :
    {xᵉ yᵉ zᵉ wᵉ : type-Monoidᵉ} → mul-Monoidᵉ yᵉ zᵉ ＝ᵉ mul-Monoidᵉ zᵉ yᵉ →
    mul-Monoidᵉ (mul-Monoidᵉ xᵉ yᵉ) (mul-Monoidᵉ zᵉ wᵉ) ＝ᵉ
    mul-Monoidᵉ (mul-Monoidᵉ xᵉ zᵉ) (mul-Monoidᵉ yᵉ wᵉ)
  interchange-mul-mul-Monoidᵉ =
    interchange-mul-mul-Semigroupᵉ semigroup-Monoidᵉ
```

## Properties

### For any semigroup `G`, being unital is a property

```agda
abstract
  all-elements-equal-is-unital-Semigroupᵉ :
    {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ) → all-elements-equalᵉ (is-unital-Semigroupᵉ Gᵉ)
  all-elements-equal-is-unital-Semigroupᵉ
    ( Xᵉ ,ᵉ μᵉ ,ᵉ associative-μᵉ)
    ( eᵉ ,ᵉ left-unit-eᵉ ,ᵉ right-unit-eᵉ)
    ( e'ᵉ ,ᵉ left-unit-e'ᵉ ,ᵉ right-unit-e'ᵉ) =
    eq-type-subtypeᵉ
      ( λ eᵉ →
        product-Propᵉ
          ( Π-Propᵉ (type-Setᵉ Xᵉ) (λ yᵉ → Id-Propᵉ Xᵉ (μᵉ eᵉ yᵉ) yᵉ))
          ( Π-Propᵉ (type-Setᵉ Xᵉ) (λ xᵉ → Id-Propᵉ Xᵉ (μᵉ xᵉ eᵉ) xᵉ)))
      ( (invᵉ (left-unit-e'ᵉ eᵉ)) ∙ᵉ (right-unit-eᵉ e'ᵉ))

abstract
  is-prop-is-unital-Semigroupᵉ :
    {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ) → is-propᵉ (is-unital-Semigroupᵉ Gᵉ)
  is-prop-is-unital-Semigroupᵉ Gᵉ =
    is-prop-all-elements-equalᵉ (all-elements-equal-is-unital-Semigroupᵉ Gᵉ)

is-unital-prop-Semigroupᵉ : {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ) → Propᵉ lᵉ
pr1ᵉ (is-unital-prop-Semigroupᵉ Gᵉ) = is-unital-Semigroupᵉ Gᵉ
pr2ᵉ (is-unital-prop-Semigroupᵉ Gᵉ) = is-prop-is-unital-Semigroupᵉ Gᵉ
```

### Monoids are H-spaces

```agda
h-space-Monoidᵉ : {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ) → H-Spaceᵉ lᵉ
pr1ᵉ (pr1ᵉ (h-space-Monoidᵉ Mᵉ)) = type-Monoidᵉ Mᵉ
pr2ᵉ (pr1ᵉ (h-space-Monoidᵉ Mᵉ)) = unit-Monoidᵉ Mᵉ
pr1ᵉ (pr2ᵉ (h-space-Monoidᵉ Mᵉ)) = mul-Monoidᵉ Mᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (h-space-Monoidᵉ Mᵉ))) = left-unit-law-mul-Monoidᵉ Mᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (h-space-Monoidᵉ Mᵉ)))) = right-unit-law-mul-Monoidᵉ Mᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (h-space-Monoidᵉ Mᵉ)))) =
  eq-is-propᵉ (is-set-type-Monoidᵉ Mᵉ _ _)
```

### Monoids are wild monoids

```agda
wild-monoid-Monoidᵉ : {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ) → Wild-Monoidᵉ lᵉ
pr1ᵉ (wild-monoid-Monoidᵉ Mᵉ) = h-space-Monoidᵉ Mᵉ
pr1ᵉ (pr2ᵉ (wild-monoid-Monoidᵉ Mᵉ)) = associative-mul-Monoidᵉ Mᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (wild-monoid-Monoidᵉ Mᵉ))) yᵉ zᵉ =
  eq-is-propᵉ (is-set-type-Monoidᵉ Mᵉ _ _)
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (wild-monoid-Monoidᵉ Mᵉ)))) xᵉ zᵉ =
  eq-is-propᵉ (is-set-type-Monoidᵉ Mᵉ _ _)
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (wild-monoid-Monoidᵉ Mᵉ))))) xᵉ yᵉ =
  eq-is-propᵉ (is-set-type-Monoidᵉ Mᵉ _ _)
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (wild-monoid-Monoidᵉ Mᵉ))))) = starᵉ
```

## See also

-ᵉ Inᵉ [oneᵉ objectᵉ precategories](category-theory.one-object-precategories.md),ᵉ weᵉ
  showᵉ thatᵉ monoidsᵉ areᵉ precategoriesᵉ whoseᵉ typeᵉ ofᵉ objectsᵉ isᵉ contractible.ᵉ