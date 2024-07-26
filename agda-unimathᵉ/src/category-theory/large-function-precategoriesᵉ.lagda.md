# Large function precategories

```agda
module category-theory.large-function-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.dependent-products-of-large-precategoriesᵉ
open import category-theory.isomorphisms-in-large-precategoriesᵉ
open import category-theory.large-precategoriesᵉ

open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ typeᵉ `I`ᵉ andᵉ aᵉ
[largeᵉ precategory](category-theory.large-precategories.mdᵉ) `C`,ᵉ theᵉ **largeᵉ
functionᵉ pre-category**ᵉ `Cᴵ`ᵉ consistsᵉ ofᵉ `I`-indexedᵉ familiesᵉ ofᵉ objectsᵉ ofᵉ `C`ᵉ
andᵉ `I`-indexedᵉ familiesᵉ ofᵉ morphismsᵉ betweenᵉ them.ᵉ

## Definition

### Large function precategories

```agda
module _
  {l1ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Iᵉ : UUᵉ l1ᵉ) (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  where

  Large-Function-Precategoryᵉ :
    Large-Precategoryᵉ (λ l2ᵉ → l1ᵉ ⊔ αᵉ l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ βᵉ l2ᵉ l3ᵉ)
  Large-Function-Precategoryᵉ =
    Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  obj-Large-Function-Precategoryᵉ : (l2ᵉ : Level) → UUᵉ (l1ᵉ ⊔ αᵉ l2ᵉ)
  obj-Large-Function-Precategoryᵉ =
    obj-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  hom-set-Large-Function-Precategoryᵉ :
    {l2ᵉ l3ᵉ : Level} →
    obj-Large-Function-Precategoryᵉ l2ᵉ → obj-Large-Function-Precategoryᵉ l3ᵉ →
    Setᵉ (l1ᵉ ⊔ βᵉ l2ᵉ l3ᵉ)
  hom-set-Large-Function-Precategoryᵉ =
    hom-set-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  hom-Large-Function-Precategoryᵉ :
    {l2ᵉ l3ᵉ : Level} →
    obj-Large-Function-Precategoryᵉ l2ᵉ → obj-Large-Function-Precategoryᵉ l3ᵉ →
    UUᵉ (l1ᵉ ⊔ βᵉ l2ᵉ l3ᵉ)
  hom-Large-Function-Precategoryᵉ =
    hom-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  comp-hom-Large-Function-Precategoryᵉ :
    {l2ᵉ l3ᵉ l4ᵉ : Level}
    {xᵉ : obj-Large-Function-Precategoryᵉ l2ᵉ}
    {yᵉ : obj-Large-Function-Precategoryᵉ l3ᵉ}
    {zᵉ : obj-Large-Function-Precategoryᵉ l4ᵉ} →
    hom-Large-Function-Precategoryᵉ yᵉ zᵉ →
    hom-Large-Function-Precategoryᵉ xᵉ yᵉ →
    hom-Large-Function-Precategoryᵉ xᵉ zᵉ
  comp-hom-Large-Function-Precategoryᵉ =
    comp-hom-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  associative-comp-hom-Large-Function-Precategoryᵉ :
    {l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
    {xᵉ : obj-Large-Function-Precategoryᵉ l2ᵉ}
    {yᵉ : obj-Large-Function-Precategoryᵉ l3ᵉ}
    {zᵉ : obj-Large-Function-Precategoryᵉ l4ᵉ}
    {wᵉ : obj-Large-Function-Precategoryᵉ l5ᵉ} →
    (hᵉ : hom-Large-Function-Precategoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Large-Function-Precategoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Large-Function-Precategoryᵉ xᵉ yᵉ) →
    comp-hom-Large-Function-Precategoryᵉ
      ( comp-hom-Large-Function-Precategoryᵉ hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-hom-Large-Function-Precategoryᵉ
      ( hᵉ)
      ( comp-hom-Large-Function-Precategoryᵉ gᵉ fᵉ)
  associative-comp-hom-Large-Function-Precategoryᵉ =
    associative-comp-hom-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  involutive-eq-associative-comp-hom-Large-Function-Precategoryᵉ :
    {l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
    {xᵉ : obj-Large-Function-Precategoryᵉ l2ᵉ}
    {yᵉ : obj-Large-Function-Precategoryᵉ l3ᵉ}
    {zᵉ : obj-Large-Function-Precategoryᵉ l4ᵉ}
    {wᵉ : obj-Large-Function-Precategoryᵉ l5ᵉ} →
    (hᵉ : hom-Large-Function-Precategoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Large-Function-Precategoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Large-Function-Precategoryᵉ xᵉ yᵉ) →
    comp-hom-Large-Function-Precategoryᵉ
      ( comp-hom-Large-Function-Precategoryᵉ hᵉ gᵉ)
      ( fᵉ) ＝ⁱᵉ
    comp-hom-Large-Function-Precategoryᵉ
      ( hᵉ)
      ( comp-hom-Large-Function-Precategoryᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Large-Function-Precategoryᵉ =
    involutive-eq-associative-comp-hom-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  id-hom-Large-Function-Precategoryᵉ :
    {l2ᵉ : Level} {xᵉ : obj-Large-Function-Precategoryᵉ l2ᵉ} →
    hom-Large-Function-Precategoryᵉ xᵉ xᵉ
  id-hom-Large-Function-Precategoryᵉ =
    id-hom-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  left-unit-law-comp-hom-Large-Function-Precategoryᵉ :
    {l2ᵉ l3ᵉ : Level}
    {xᵉ : obj-Large-Function-Precategoryᵉ l2ᵉ}
    {yᵉ : obj-Large-Function-Precategoryᵉ l3ᵉ}
    (fᵉ : hom-Large-Function-Precategoryᵉ xᵉ yᵉ) →
    comp-hom-Large-Function-Precategoryᵉ id-hom-Large-Function-Precategoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Large-Function-Precategoryᵉ =
    left-unit-law-comp-hom-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  right-unit-law-comp-hom-Large-Function-Precategoryᵉ :
    {l2ᵉ l3ᵉ : Level}
    {xᵉ : obj-Large-Function-Precategoryᵉ l2ᵉ}
    {yᵉ : obj-Large-Function-Precategoryᵉ l3ᵉ}
    (fᵉ : hom-Large-Function-Precategoryᵉ xᵉ yᵉ) →
    comp-hom-Large-Function-Precategoryᵉ fᵉ id-hom-Large-Function-Precategoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-hom-Large-Function-Precategoryᵉ =
    right-unit-law-comp-hom-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)
```

## Properties

### Isomorphisms in the dependent product precategory are fiberwise isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Iᵉ : UUᵉ l1ᵉ) (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  {xᵉ : obj-Large-Function-Precategoryᵉ Iᵉ Cᵉ l2ᵉ}
  {yᵉ : obj-Large-Function-Precategoryᵉ Iᵉ Cᵉ l3ᵉ}
  where

  is-fiberwise-iso-is-iso-Large-Function-Precategoryᵉ :
    (fᵉ : hom-Large-Function-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-iso-Large-Precategoryᵉ (Large-Function-Precategoryᵉ Iᵉ Cᵉ) fᵉ →
    (iᵉ : Iᵉ) → is-iso-Large-Precategoryᵉ Cᵉ (fᵉ iᵉ)
  is-fiberwise-iso-is-iso-Large-Function-Precategoryᵉ =
    is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  fiberwise-iso-iso-Large-Function-Precategoryᵉ :
    iso-Large-Precategoryᵉ (Large-Function-Precategoryᵉ Iᵉ Cᵉ) xᵉ yᵉ →
    (iᵉ : Iᵉ) → iso-Large-Precategoryᵉ Cᵉ (xᵉ iᵉ) (yᵉ iᵉ)
  fiberwise-iso-iso-Large-Function-Precategoryᵉ =
    fiberwise-iso-iso-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  is-iso-is-fiberwise-iso-Large-Function-Precategoryᵉ :
    (fᵉ : hom-Large-Function-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ((iᵉ : Iᵉ) → is-iso-Large-Precategoryᵉ Cᵉ (fᵉ iᵉ)) →
    is-iso-Large-Precategoryᵉ (Large-Function-Precategoryᵉ Iᵉ Cᵉ) fᵉ
  is-iso-is-fiberwise-iso-Large-Function-Precategoryᵉ =
    is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  iso-fiberwise-iso-Large-Function-Precategoryᵉ :
    ((iᵉ : Iᵉ) → iso-Large-Precategoryᵉ Cᵉ (xᵉ iᵉ) (yᵉ iᵉ)) →
    iso-Large-Precategoryᵉ (Large-Function-Precategoryᵉ Iᵉ Cᵉ) xᵉ yᵉ
  iso-fiberwise-iso-Large-Function-Precategoryᵉ =
    iso-fiberwise-iso-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  is-equiv-is-fiberwise-iso-is-iso-Large-Function-Precategoryᵉ :
    (fᵉ : hom-Large-Function-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-equivᵉ (is-fiberwise-iso-is-iso-Large-Function-Precategoryᵉ fᵉ)
  is-equiv-is-fiberwise-iso-is-iso-Large-Function-Precategoryᵉ =
    is-equiv-is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  equiv-is-fiberwise-iso-is-iso-Large-Function-Precategoryᵉ :
    (fᵉ : hom-Large-Function-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ( is-iso-Large-Precategoryᵉ (Large-Function-Precategoryᵉ Iᵉ Cᵉ) fᵉ) ≃ᵉ
    ( (iᵉ : Iᵉ) → is-iso-Large-Precategoryᵉ Cᵉ (fᵉ iᵉ))
  equiv-is-fiberwise-iso-is-iso-Large-Function-Precategoryᵉ =
    equiv-is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  is-equiv-is-iso-is-fiberwise-iso-Large-Function-Precategoryᵉ :
    (fᵉ : hom-Large-Function-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-equivᵉ (is-iso-is-fiberwise-iso-Large-Function-Precategoryᵉ fᵉ)
  is-equiv-is-iso-is-fiberwise-iso-Large-Function-Precategoryᵉ =
    is-equiv-is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  equiv-is-iso-is-fiberwise-iso-Large-Function-Precategoryᵉ :
    ( fᵉ : hom-Large-Function-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ( (iᵉ : Iᵉ) → is-iso-Large-Precategoryᵉ Cᵉ (fᵉ iᵉ)) ≃ᵉ
    ( is-iso-Large-Precategoryᵉ (Large-Function-Precategoryᵉ Iᵉ Cᵉ) fᵉ)
  equiv-is-iso-is-fiberwise-iso-Large-Function-Precategoryᵉ =
    equiv-is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  is-equiv-fiberwise-iso-iso-Large-Function-Precategoryᵉ :
    is-equivᵉ fiberwise-iso-iso-Large-Function-Precategoryᵉ
  is-equiv-fiberwise-iso-iso-Large-Function-Precategoryᵉ =
    is-equiv-fiberwise-iso-iso-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  equiv-fiberwise-iso-iso-Large-Function-Precategoryᵉ :
    ( iso-Large-Precategoryᵉ (Large-Function-Precategoryᵉ Iᵉ Cᵉ) xᵉ yᵉ) ≃ᵉ
    ( (iᵉ : Iᵉ) → iso-Large-Precategoryᵉ Cᵉ (xᵉ iᵉ) (yᵉ iᵉ))
  equiv-fiberwise-iso-iso-Large-Function-Precategoryᵉ =
    equiv-fiberwise-iso-iso-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  is-equiv-iso-fiberwise-iso-Large-Function-Precategoryᵉ :
    is-equivᵉ iso-fiberwise-iso-Large-Function-Precategoryᵉ
  is-equiv-iso-fiberwise-iso-Large-Function-Precategoryᵉ =
    is-equiv-iso-fiberwise-iso-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  equiv-iso-fiberwise-iso-Large-Function-Precategoryᵉ :
    ( (iᵉ : Iᵉ) → iso-Large-Precategoryᵉ Cᵉ (xᵉ iᵉ) (yᵉ iᵉ)) ≃ᵉ
    ( iso-Large-Precategoryᵉ (Large-Function-Precategoryᵉ Iᵉ Cᵉ) xᵉ yᵉ)
  equiv-iso-fiberwise-iso-Large-Function-Precategoryᵉ =
    equiv-iso-fiberwise-iso-Π-Large-Precategoryᵉ Iᵉ (λ _ → Cᵉ)
```