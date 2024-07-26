# Large function categories

```agda
module category-theory.large-function-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.dependent-products-of-large-categoriesᵉ
open import category-theory.isomorphisms-in-large-categoriesᵉ
open import category-theory.large-categoriesᵉ

open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ typeᵉ `I`ᵉ andᵉ aᵉ [largeᵉ category](category-theory.large-categories.mdᵉ)
`C`,ᵉ theᵉ {{#conceptᵉ "largeᵉ functionᵉ category"ᵉ Agda=Large-Function-Categoryᵉ}}
`Cᴵ`ᵉ consistsᵉ ofᵉ `I`-indexedᵉ familiesᵉ ofᵉ objectsᵉ ofᵉ `C`ᵉ andᵉ `I`-indexedᵉ familiesᵉ
ofᵉ morphismsᵉ betweenᵉ them.ᵉ

## Definition

### Large function categories

```agda
module _
  {l1ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Iᵉ : UUᵉ l1ᵉ) (Cᵉ : Large-Categoryᵉ αᵉ βᵉ)
  where

  Large-Function-Categoryᵉ :
    Large-Categoryᵉ (λ l2ᵉ → l1ᵉ ⊔ αᵉ l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ βᵉ l2ᵉ l3ᵉ)
  Large-Function-Categoryᵉ =
    Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  obj-Large-Function-Categoryᵉ : (l2ᵉ : Level) → UUᵉ (l1ᵉ ⊔ αᵉ l2ᵉ)
  obj-Large-Function-Categoryᵉ =
    obj-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  hom-set-Large-Function-Categoryᵉ :
    {l2ᵉ l3ᵉ : Level} →
    obj-Large-Function-Categoryᵉ l2ᵉ → obj-Large-Function-Categoryᵉ l3ᵉ →
    Setᵉ (l1ᵉ ⊔ βᵉ l2ᵉ l3ᵉ)
  hom-set-Large-Function-Categoryᵉ =
    hom-set-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  hom-Large-Function-Categoryᵉ :
    {l2ᵉ l3ᵉ : Level} →
    obj-Large-Function-Categoryᵉ l2ᵉ → obj-Large-Function-Categoryᵉ l3ᵉ →
    UUᵉ (l1ᵉ ⊔ βᵉ l2ᵉ l3ᵉ)
  hom-Large-Function-Categoryᵉ =
    hom-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  comp-hom-Large-Function-Categoryᵉ :
    {l2ᵉ l3ᵉ l4ᵉ : Level}
    {xᵉ : obj-Large-Function-Categoryᵉ l2ᵉ}
    {yᵉ : obj-Large-Function-Categoryᵉ l3ᵉ}
    {zᵉ : obj-Large-Function-Categoryᵉ l4ᵉ} →
    hom-Large-Function-Categoryᵉ yᵉ zᵉ →
    hom-Large-Function-Categoryᵉ xᵉ yᵉ →
    hom-Large-Function-Categoryᵉ xᵉ zᵉ
  comp-hom-Large-Function-Categoryᵉ =
    comp-hom-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  associative-comp-hom-Large-Function-Categoryᵉ :
    {l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
    {xᵉ : obj-Large-Function-Categoryᵉ l2ᵉ}
    {yᵉ : obj-Large-Function-Categoryᵉ l3ᵉ}
    {zᵉ : obj-Large-Function-Categoryᵉ l4ᵉ}
    {wᵉ : obj-Large-Function-Categoryᵉ l5ᵉ} →
    (hᵉ : hom-Large-Function-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Large-Function-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Large-Function-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Large-Function-Categoryᵉ (comp-hom-Large-Function-Categoryᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Large-Function-Categoryᵉ hᵉ (comp-hom-Large-Function-Categoryᵉ gᵉ fᵉ)
  associative-comp-hom-Large-Function-Categoryᵉ =
    associative-comp-hom-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  involutive-eq-associative-comp-hom-Large-Function-Categoryᵉ :
    {l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
    {xᵉ : obj-Large-Function-Categoryᵉ l2ᵉ}
    {yᵉ : obj-Large-Function-Categoryᵉ l3ᵉ}
    {zᵉ : obj-Large-Function-Categoryᵉ l4ᵉ}
    {wᵉ : obj-Large-Function-Categoryᵉ l5ᵉ} →
    (hᵉ : hom-Large-Function-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Large-Function-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Large-Function-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Large-Function-Categoryᵉ
      ( comp-hom-Large-Function-Categoryᵉ hᵉ gᵉ)
      ( fᵉ) ＝ⁱᵉ
    comp-hom-Large-Function-Categoryᵉ
      ( hᵉ)
      ( comp-hom-Large-Function-Categoryᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Large-Function-Categoryᵉ =
    involutive-eq-associative-comp-hom-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  id-hom-Large-Function-Categoryᵉ :
    {l2ᵉ : Level} {xᵉ : obj-Large-Function-Categoryᵉ l2ᵉ} →
    hom-Large-Function-Categoryᵉ xᵉ xᵉ
  id-hom-Large-Function-Categoryᵉ =
    id-hom-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  left-unit-law-comp-hom-Large-Function-Categoryᵉ :
    {l2ᵉ l3ᵉ : Level}
    {xᵉ : obj-Large-Function-Categoryᵉ l2ᵉ}
    {yᵉ : obj-Large-Function-Categoryᵉ l3ᵉ}
    (fᵉ : hom-Large-Function-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Large-Function-Categoryᵉ id-hom-Large-Function-Categoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Large-Function-Categoryᵉ =
    left-unit-law-comp-hom-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  right-unit-law-comp-hom-Large-Function-Categoryᵉ :
    {l2ᵉ l3ᵉ : Level}
    {xᵉ : obj-Large-Function-Categoryᵉ l2ᵉ}
    {yᵉ : obj-Large-Function-Categoryᵉ l3ᵉ}
    (fᵉ : hom-Large-Function-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Large-Function-Categoryᵉ fᵉ id-hom-Large-Function-Categoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-hom-Large-Function-Categoryᵉ =
    right-unit-law-comp-hom-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)
```

## Properties

### Isomorphisms in the dependent product category are fiberwise isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Iᵉ : UUᵉ l1ᵉ) (Cᵉ : Large-Categoryᵉ αᵉ βᵉ)
  {xᵉ : obj-Large-Function-Categoryᵉ Iᵉ Cᵉ l2ᵉ}
  {yᵉ : obj-Large-Function-Categoryᵉ Iᵉ Cᵉ l3ᵉ}
  where

  is-fiberwise-iso-is-iso-Large-Function-Categoryᵉ :
    (fᵉ : hom-Large-Function-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-iso-Large-Categoryᵉ (Large-Function-Categoryᵉ Iᵉ Cᵉ) fᵉ →
    (iᵉ : Iᵉ) → is-iso-Large-Categoryᵉ Cᵉ (fᵉ iᵉ)
  is-fiberwise-iso-is-iso-Large-Function-Categoryᵉ =
    is-fiberwise-iso-is-iso-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  fiberwise-iso-iso-Large-Function-Categoryᵉ :
    iso-Large-Categoryᵉ (Large-Function-Categoryᵉ Iᵉ Cᵉ) xᵉ yᵉ →
    (iᵉ : Iᵉ) → iso-Large-Categoryᵉ Cᵉ (xᵉ iᵉ) (yᵉ iᵉ)
  fiberwise-iso-iso-Large-Function-Categoryᵉ =
    fiberwise-iso-iso-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  is-iso-is-fiberwise-iso-Large-Function-Categoryᵉ :
    (fᵉ : hom-Large-Function-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ((iᵉ : Iᵉ) → is-iso-Large-Categoryᵉ Cᵉ (fᵉ iᵉ)) →
    is-iso-Large-Categoryᵉ (Large-Function-Categoryᵉ Iᵉ Cᵉ) fᵉ
  is-iso-is-fiberwise-iso-Large-Function-Categoryᵉ =
    is-iso-is-fiberwise-iso-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  iso-fiberwise-iso-Large-Function-Categoryᵉ :
    ((iᵉ : Iᵉ) → iso-Large-Categoryᵉ Cᵉ (xᵉ iᵉ) (yᵉ iᵉ)) →
    iso-Large-Categoryᵉ (Large-Function-Categoryᵉ Iᵉ Cᵉ) xᵉ yᵉ
  iso-fiberwise-iso-Large-Function-Categoryᵉ =
    iso-fiberwise-iso-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  is-equiv-is-fiberwise-iso-is-iso-Large-Function-Categoryᵉ :
    (fᵉ : hom-Large-Function-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-equivᵉ (is-fiberwise-iso-is-iso-Large-Function-Categoryᵉ fᵉ)
  is-equiv-is-fiberwise-iso-is-iso-Large-Function-Categoryᵉ =
    is-equiv-is-fiberwise-iso-is-iso-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  equiv-is-fiberwise-iso-is-iso-Large-Function-Categoryᵉ :
    (fᵉ : hom-Large-Function-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ( is-iso-Large-Categoryᵉ (Large-Function-Categoryᵉ Iᵉ Cᵉ) fᵉ) ≃ᵉ
    ( (iᵉ : Iᵉ) → is-iso-Large-Categoryᵉ Cᵉ (fᵉ iᵉ))
  equiv-is-fiberwise-iso-is-iso-Large-Function-Categoryᵉ =
    equiv-is-fiberwise-iso-is-iso-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  is-equiv-is-iso-is-fiberwise-iso-Large-Function-Categoryᵉ :
    (fᵉ : hom-Large-Function-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-equivᵉ (is-iso-is-fiberwise-iso-Large-Function-Categoryᵉ fᵉ)
  is-equiv-is-iso-is-fiberwise-iso-Large-Function-Categoryᵉ =
    is-equiv-is-iso-is-fiberwise-iso-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  equiv-is-iso-is-fiberwise-iso-Large-Function-Categoryᵉ :
    ( fᵉ : hom-Large-Function-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ( (iᵉ : Iᵉ) → is-iso-Large-Categoryᵉ Cᵉ (fᵉ iᵉ)) ≃ᵉ
    ( is-iso-Large-Categoryᵉ (Large-Function-Categoryᵉ Iᵉ Cᵉ) fᵉ)
  equiv-is-iso-is-fiberwise-iso-Large-Function-Categoryᵉ =
    equiv-is-iso-is-fiberwise-iso-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  is-equiv-fiberwise-iso-iso-Large-Function-Categoryᵉ :
    is-equivᵉ fiberwise-iso-iso-Large-Function-Categoryᵉ
  is-equiv-fiberwise-iso-iso-Large-Function-Categoryᵉ =
    is-equiv-fiberwise-iso-iso-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  equiv-fiberwise-iso-iso-Large-Function-Categoryᵉ :
    ( iso-Large-Categoryᵉ (Large-Function-Categoryᵉ Iᵉ Cᵉ) xᵉ yᵉ) ≃ᵉ
    ( (iᵉ : Iᵉ) → iso-Large-Categoryᵉ Cᵉ (xᵉ iᵉ) (yᵉ iᵉ))
  equiv-fiberwise-iso-iso-Large-Function-Categoryᵉ =
    equiv-fiberwise-iso-iso-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  is-equiv-iso-fiberwise-iso-Large-Function-Categoryᵉ :
    is-equivᵉ iso-fiberwise-iso-Large-Function-Categoryᵉ
  is-equiv-iso-fiberwise-iso-Large-Function-Categoryᵉ =
    is-equiv-iso-fiberwise-iso-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  equiv-iso-fiberwise-iso-Large-Function-Categoryᵉ :
    ( (iᵉ : Iᵉ) → iso-Large-Categoryᵉ Cᵉ (xᵉ iᵉ) (yᵉ iᵉ)) ≃ᵉ
    ( iso-Large-Categoryᵉ (Large-Function-Categoryᵉ Iᵉ Cᵉ) xᵉ yᵉ)
  equiv-iso-fiberwise-iso-Large-Function-Categoryᵉ =
    equiv-iso-fiberwise-iso-Π-Large-Categoryᵉ Iᵉ (λ _ → Cᵉ)
```