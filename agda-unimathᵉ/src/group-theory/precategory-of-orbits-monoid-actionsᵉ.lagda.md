# The precategory of orbits of a monoid action

```agda
module group-theory.precategory-of-orbits-monoid-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategoriesᵉ

open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.monoid-actionsᵉ
open import group-theory.monoidsᵉ
```

</details>

## Idea

Theᵉ [precategory](category-theory.precategories.mdᵉ) ofᵉ **orbits**ᵉ ofᵉ aᵉ
[monoidᵉ action](group-theory.monoid-actions.mdᵉ) ofᵉ `M`ᵉ onᵉ `X`ᵉ consistsᵉ ofᵉ theᵉ
elementsᵉ ofᵉ theᵉ [set](foundation-core.sets.mdᵉ) `X`ᵉ asᵉ theᵉ objects,ᵉ andᵉ aᵉ
morphismᵉ fromᵉ `x`ᵉ to `y`ᵉ isᵉ anᵉ elementᵉ `m`ᵉ ofᵉ theᵉ
[monoid](group-theory.monoids.mdᵉ) `M`ᵉ suchᵉ thatᵉ `mxᵉ = y`.ᵉ

## Definition

### The precategory of orbits of a monoid action

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Xᵉ : action-Monoidᵉ l2ᵉ Mᵉ)
  where

  hom-orbit-action-Monoidᵉ : (xᵉ yᵉ : type-action-Monoidᵉ Mᵉ Xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-orbit-action-Monoidᵉ xᵉ yᵉ =
    Σᵉ (type-Monoidᵉ Mᵉ) ( λ mᵉ → Idᵉ (mul-action-Monoidᵉ Mᵉ Xᵉ mᵉ xᵉ) yᵉ)

  element-hom-orbit-action-Monoidᵉ :
    {xᵉ yᵉ : type-action-Monoidᵉ Mᵉ Xᵉ} → hom-orbit-action-Monoidᵉ xᵉ yᵉ → type-Monoidᵉ Mᵉ
  element-hom-orbit-action-Monoidᵉ fᵉ = pr1ᵉ fᵉ

  eq-hom-orbit-action-Monoidᵉ :
    {xᵉ yᵉ : type-action-Monoidᵉ Mᵉ Xᵉ} (fᵉ : hom-orbit-action-Monoidᵉ xᵉ yᵉ) →
    Idᵉ (mul-action-Monoidᵉ Mᵉ Xᵉ (element-hom-orbit-action-Monoidᵉ fᵉ) xᵉ) yᵉ
  eq-hom-orbit-action-Monoidᵉ fᵉ = pr2ᵉ fᵉ

  htpy-hom-orbit-action-Monoidᵉ :
    {xᵉ yᵉ : type-action-Monoidᵉ Mᵉ Xᵉ} (fᵉ gᵉ : hom-orbit-action-Monoidᵉ xᵉ yᵉ) →
    UUᵉ l1ᵉ
  htpy-hom-orbit-action-Monoidᵉ {xᵉ} {yᵉ} fᵉ gᵉ =
    Idᵉ
      ( element-hom-orbit-action-Monoidᵉ fᵉ)
      ( element-hom-orbit-action-Monoidᵉ gᵉ)

  refl-htpy-hom-orbit-action-Monoidᵉ :
    {xᵉ yᵉ : type-action-Monoidᵉ Mᵉ Xᵉ} (fᵉ : hom-orbit-action-Monoidᵉ xᵉ yᵉ) →
    htpy-hom-orbit-action-Monoidᵉ fᵉ fᵉ
  refl-htpy-hom-orbit-action-Monoidᵉ fᵉ = reflᵉ

  htpy-eq-hom-orbit-action-Monoidᵉ :
    {xᵉ yᵉ : type-action-Monoidᵉ Mᵉ Xᵉ} (fᵉ gᵉ : hom-orbit-action-Monoidᵉ xᵉ yᵉ) →
    Idᵉ fᵉ gᵉ → htpy-hom-orbit-action-Monoidᵉ fᵉ gᵉ
  htpy-eq-hom-orbit-action-Monoidᵉ fᵉ .fᵉ reflᵉ =
    refl-htpy-hom-orbit-action-Monoidᵉ fᵉ

  is-torsorial-htpy-hom-orbit-action-Monoidᵉ :
    {xᵉ yᵉ : type-action-Monoidᵉ Mᵉ Xᵉ} (fᵉ : hom-orbit-action-Monoidᵉ xᵉ yᵉ) →
    is-torsorialᵉ (htpy-hom-orbit-action-Monoidᵉ fᵉ)
  is-torsorial-htpy-hom-orbit-action-Monoidᵉ {xᵉ} {yᵉ} fᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-Idᵉ (element-hom-orbit-action-Monoidᵉ fᵉ))
      ( λ uᵉ →
        is-set-type-action-Monoidᵉ Mᵉ Xᵉ (mul-action-Monoidᵉ Mᵉ Xᵉ uᵉ xᵉ) yᵉ)
      ( element-hom-orbit-action-Monoidᵉ fᵉ)
      ( reflᵉ)
      ( eq-hom-orbit-action-Monoidᵉ fᵉ)

  is-equiv-htpy-eq-hom-orbit-action-Monoidᵉ :
    {xᵉ yᵉ : type-action-Monoidᵉ Mᵉ Xᵉ} (fᵉ gᵉ : hom-orbit-action-Monoidᵉ xᵉ yᵉ) →
    is-equivᵉ (htpy-eq-hom-orbit-action-Monoidᵉ fᵉ gᵉ)
  is-equiv-htpy-eq-hom-orbit-action-Monoidᵉ fᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-hom-orbit-action-Monoidᵉ fᵉ)
      ( htpy-eq-hom-orbit-action-Monoidᵉ fᵉ)

  extensionality-hom-orbit-action-Monoidᵉ :
    {xᵉ yᵉ : type-action-Monoidᵉ Mᵉ Xᵉ} (fᵉ gᵉ : hom-orbit-action-Monoidᵉ xᵉ yᵉ) →
    Idᵉ fᵉ gᵉ ≃ᵉ htpy-hom-orbit-action-Monoidᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-hom-orbit-action-Monoidᵉ fᵉ gᵉ) =
    htpy-eq-hom-orbit-action-Monoidᵉ fᵉ gᵉ
  pr2ᵉ (extensionality-hom-orbit-action-Monoidᵉ fᵉ gᵉ) =
    is-equiv-htpy-eq-hom-orbit-action-Monoidᵉ fᵉ gᵉ

  eq-htpy-hom-orbit-action-Monoidᵉ :
    {xᵉ yᵉ : type-action-Monoidᵉ Mᵉ Xᵉ} {fᵉ gᵉ : hom-orbit-action-Monoidᵉ xᵉ yᵉ} →
    htpy-hom-orbit-action-Monoidᵉ fᵉ gᵉ → Idᵉ fᵉ gᵉ
  eq-htpy-hom-orbit-action-Monoidᵉ {xᵉ} {yᵉ} {fᵉ} {gᵉ} =
    map-inv-is-equivᵉ (is-equiv-htpy-eq-hom-orbit-action-Monoidᵉ fᵉ gᵉ)

  is-prop-htpy-hom-orbit-action-Monoidᵉ :
    {xᵉ yᵉ : type-action-Monoidᵉ Mᵉ Xᵉ} (fᵉ gᵉ : hom-orbit-action-Monoidᵉ xᵉ yᵉ) →
    is-propᵉ (htpy-hom-orbit-action-Monoidᵉ fᵉ gᵉ)
  is-prop-htpy-hom-orbit-action-Monoidᵉ fᵉ gᵉ =
    is-set-type-Monoidᵉ Mᵉ
      ( element-hom-orbit-action-Monoidᵉ fᵉ)
      ( element-hom-orbit-action-Monoidᵉ gᵉ)

  is-set-hom-orbit-action-Monoidᵉ :
    {xᵉ yᵉ : type-action-Monoidᵉ Mᵉ Xᵉ} →
    is-setᵉ (hom-orbit-action-Monoidᵉ xᵉ yᵉ)
  is-set-hom-orbit-action-Monoidᵉ {xᵉ} {yᵉ} fᵉ gᵉ =
    is-prop-equivᵉ
      ( extensionality-hom-orbit-action-Monoidᵉ fᵉ gᵉ)
      ( is-prop-htpy-hom-orbit-action-Monoidᵉ fᵉ gᵉ)

  hom-orbit-monoid-action-Setᵉ :
    (xᵉ yᵉ : type-action-Monoidᵉ Mᵉ Xᵉ) → Setᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (hom-orbit-monoid-action-Setᵉ xᵉ yᵉ) = hom-orbit-action-Monoidᵉ xᵉ yᵉ
  pr2ᵉ (hom-orbit-monoid-action-Setᵉ xᵉ yᵉ) = is-set-hom-orbit-action-Monoidᵉ

  id-hom-orbit-action-Monoidᵉ :
    (xᵉ : type-action-Monoidᵉ Mᵉ Xᵉ) → hom-orbit-action-Monoidᵉ xᵉ xᵉ
  pr1ᵉ (id-hom-orbit-action-Monoidᵉ xᵉ) = unit-Monoidᵉ Mᵉ
  pr2ᵉ (id-hom-orbit-action-Monoidᵉ xᵉ) = unit-law-mul-action-Monoidᵉ Mᵉ Xᵉ xᵉ

  comp-hom-orbit-action-Monoidᵉ :
    {xᵉ yᵉ zᵉ : type-action-Monoidᵉ Mᵉ Xᵉ} →
    hom-orbit-action-Monoidᵉ yᵉ zᵉ → hom-orbit-action-Monoidᵉ xᵉ yᵉ →
    hom-orbit-action-Monoidᵉ xᵉ zᵉ
  pr1ᵉ (comp-hom-orbit-action-Monoidᵉ gᵉ fᵉ) =
    mul-Monoidᵉ Mᵉ
      ( element-hom-orbit-action-Monoidᵉ gᵉ)
      ( element-hom-orbit-action-Monoidᵉ fᵉ)
  pr2ᵉ (comp-hom-orbit-action-Monoidᵉ {xᵉ} gᵉ fᵉ) =
    ( associative-mul-action-Monoidᵉ Mᵉ Xᵉ
      ( element-hom-orbit-action-Monoidᵉ gᵉ)
      ( element-hom-orbit-action-Monoidᵉ fᵉ)
      ( xᵉ)) ∙ᵉ
    ( ap-mul-action-Monoidᵉ Mᵉ Xᵉ (eq-hom-orbit-action-Monoidᵉ fᵉ)) ∙ᵉ
    ( eq-hom-orbit-action-Monoidᵉ gᵉ)

  associative-comp-hom-orbit-action-Monoidᵉ :
    {xᵉ yᵉ zᵉ wᵉ : type-action-Monoidᵉ Mᵉ Xᵉ} (hᵉ : hom-orbit-action-Monoidᵉ zᵉ wᵉ)
    (gᵉ : hom-orbit-action-Monoidᵉ yᵉ zᵉ) (fᵉ : hom-orbit-action-Monoidᵉ xᵉ yᵉ) →
    comp-hom-orbit-action-Monoidᵉ (comp-hom-orbit-action-Monoidᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-orbit-action-Monoidᵉ hᵉ (comp-hom-orbit-action-Monoidᵉ gᵉ fᵉ)
  associative-comp-hom-orbit-action-Monoidᵉ hᵉ gᵉ fᵉ =
    eq-htpy-hom-orbit-action-Monoidᵉ
      ( associative-mul-Monoidᵉ Mᵉ
        ( element-hom-orbit-action-Monoidᵉ hᵉ)
        ( element-hom-orbit-action-Monoidᵉ gᵉ)
        ( element-hom-orbit-action-Monoidᵉ fᵉ))

  left-unit-law-comp-hom-orbit-action-Monoidᵉ :
    {xᵉ yᵉ : type-action-Monoidᵉ Mᵉ Xᵉ} (fᵉ : hom-orbit-action-Monoidᵉ xᵉ yᵉ) →
    Idᵉ (comp-hom-orbit-action-Monoidᵉ (id-hom-orbit-action-Monoidᵉ yᵉ) fᵉ) fᵉ
  left-unit-law-comp-hom-orbit-action-Monoidᵉ fᵉ =
    eq-htpy-hom-orbit-action-Monoidᵉ
      ( left-unit-law-mul-Monoidᵉ Mᵉ (element-hom-orbit-action-Monoidᵉ fᵉ))

  right-unit-law-comp-hom-orbit-action-Monoidᵉ :
    {xᵉ yᵉ : type-action-Monoidᵉ Mᵉ Xᵉ} (fᵉ : hom-orbit-action-Monoidᵉ xᵉ yᵉ) →
    Idᵉ (comp-hom-orbit-action-Monoidᵉ fᵉ (id-hom-orbit-action-Monoidᵉ xᵉ)) fᵉ
  right-unit-law-comp-hom-orbit-action-Monoidᵉ fᵉ =
    eq-htpy-hom-orbit-action-Monoidᵉ
      ( right-unit-law-mul-Monoidᵉ Mᵉ (element-hom-orbit-action-Monoidᵉ fᵉ))

  orbit-monoid-action-Precategoryᵉ : Precategoryᵉ l2ᵉ (l1ᵉ ⊔ l2ᵉ)
  orbit-monoid-action-Precategoryᵉ =
    make-Precategoryᵉ
      ( type-action-Monoidᵉ Mᵉ Xᵉ)
      ( hom-orbit-monoid-action-Setᵉ)
      ( comp-hom-orbit-action-Monoidᵉ)
      ( id-hom-orbit-action-Monoidᵉ)
      ( associative-comp-hom-orbit-action-Monoidᵉ)
      ( left-unit-law-comp-hom-orbit-action-Monoidᵉ)
      ( right-unit-law-comp-hom-orbit-action-Monoidᵉ)
```