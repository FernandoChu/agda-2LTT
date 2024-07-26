# Large subprecategories

```agda
module category-theory.large-subprecategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **largeᵉ subprecategory**ᵉ ofᵉ aᵉ
[largeᵉ precategory](category-theory.large-precategories.mdᵉ) `C`ᵉ consistsᵉ ofᵉ aᵉ
familyᵉ ofᵉ subtypesᵉ `P₀`ᵉ

```text
  P₀ᵉ : (lᵉ : Level) → subtypeᵉ _ (objᵉ Cᵉ lᵉ)
```

ofᵉ theᵉ objectsᵉ ofᵉ `C`ᵉ indexedᵉ byᵉ universeᵉ levels,ᵉ andᵉ aᵉ familyᵉ ofᵉ subtypesᵉ `P₁`ᵉ

```text
  P₁ᵉ : {l1ᵉ l2ᵉ : Level} (Xᵉ : objᵉ Cᵉ l1ᵉ) (Yᵉ : objᵉ Cᵉ l2ᵉ) →
       P₀ᵉ Xᵉ → P₀ᵉ Yᵉ → subtypeᵉ _ (homᵉ Xᵉ Yᵉ)
```

ofᵉ theᵉ morphismsᵉ ofᵉ `C`,ᵉ suchᵉ thatᵉ `P₁`ᵉ containsᵉ allᵉ identityᵉ morphismsᵉ ofᵉ
objectsᵉ in `P₀`ᵉ andᵉ isᵉ closedᵉ underᵉ composition.ᵉ

## Definitions

### Large subprecategories

```agda
record
  Large-Subprecategoryᵉ
    {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
    (γᵉ : Level → Level) (δᵉ : Level → Level → Level)
    (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) : UUωᵉ
  where
  field
    subtype-obj-Large-Subprecategoryᵉ :
      (lᵉ : Level) → subtypeᵉ (γᵉ lᵉ) (obj-Large-Precategoryᵉ Cᵉ lᵉ)

  is-in-obj-Large-Subprecategoryᵉ :
    {lᵉ : Level} → obj-Large-Precategoryᵉ Cᵉ lᵉ → UUᵉ (γᵉ lᵉ)
  is-in-obj-Large-Subprecategoryᵉ {lᵉ} =
    is-in-subtypeᵉ (subtype-obj-Large-Subprecategoryᵉ lᵉ)

  obj-Large-Subprecategoryᵉ :
    (lᵉ : Level) → UUᵉ (αᵉ lᵉ ⊔ γᵉ lᵉ)
  obj-Large-Subprecategoryᵉ lᵉ = type-subtypeᵉ (subtype-obj-Large-Subprecategoryᵉ lᵉ)

  field
    subtype-hom-Large-Subprecategoryᵉ :
      {l1ᵉ l2ᵉ : Level}
      (Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ)
      (Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ) →
      is-in-obj-Large-Subprecategoryᵉ Xᵉ →
      is-in-obj-Large-Subprecategoryᵉ Yᵉ →
      subtypeᵉ (δᵉ l1ᵉ l2ᵉ) (hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)

  is-in-hom-is-in-obj-Large-Subprecategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
    {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
    (xᵉ : is-in-obj-Large-Subprecategoryᵉ Xᵉ)
    (yᵉ : is-in-obj-Large-Subprecategoryᵉ Yᵉ) →
    hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ → UUᵉ (δᵉ l1ᵉ l2ᵉ)
  is-in-hom-is-in-obj-Large-Subprecategoryᵉ {l1ᵉ} {l2ᵉ} {Xᵉ} {Yᵉ} xᵉ yᵉ =
    is-in-subtypeᵉ (subtype-hom-Large-Subprecategoryᵉ Xᵉ Yᵉ xᵉ yᵉ)

  field
    contains-id-Large-Subprecategoryᵉ :
      {lᵉ : Level} (Xᵉ : obj-Large-Precategoryᵉ Cᵉ lᵉ) →
      (Hᵉ : is-in-obj-Large-Subprecategoryᵉ Xᵉ) →
      is-in-hom-is-in-obj-Large-Subprecategoryᵉ Hᵉ Hᵉ (id-hom-Large-Precategoryᵉ Cᵉ)

    is-closed-under-composition-Large-Subprecategoryᵉ :
      {l1ᵉ l2ᵉ l3ᵉ : Level}
      (Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ)
      (Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ)
      (Zᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ)
      (gᵉ : hom-Large-Precategoryᵉ Cᵉ Yᵉ Zᵉ)
      (fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ) →
      (Kᵉ : is-in-obj-Large-Subprecategoryᵉ Xᵉ) →
      (Lᵉ : is-in-obj-Large-Subprecategoryᵉ Yᵉ) →
      (Mᵉ : is-in-obj-Large-Subprecategoryᵉ Zᵉ) →
      is-in-hom-is-in-obj-Large-Subprecategoryᵉ Lᵉ Mᵉ gᵉ →
      is-in-hom-is-in-obj-Large-Subprecategoryᵉ Kᵉ Lᵉ fᵉ →
      is-in-hom-is-in-obj-Large-Subprecategoryᵉ Kᵉ Mᵉ
        ( comp-hom-Large-Precategoryᵉ Cᵉ gᵉ fᵉ)

  hom-Large-Subprecategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Subprecategoryᵉ l1ᵉ)
    (Yᵉ : obj-Large-Subprecategoryᵉ l2ᵉ) → UUᵉ (βᵉ l1ᵉ l2ᵉ ⊔ δᵉ l1ᵉ l2ᵉ)
  hom-Large-Subprecategoryᵉ (Xᵉ ,ᵉ xᵉ) (Yᵉ ,ᵉ yᵉ) =
    type-subtypeᵉ (subtype-hom-Large-Subprecategoryᵉ Xᵉ Yᵉ xᵉ yᵉ)

  hom-set-Large-Subprecategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Subprecategoryᵉ l1ᵉ)
    (Yᵉ : obj-Large-Subprecategoryᵉ l2ᵉ) → Setᵉ (βᵉ l1ᵉ l2ᵉ ⊔ δᵉ l1ᵉ l2ᵉ)
  hom-set-Large-Subprecategoryᵉ (Xᵉ ,ᵉ xᵉ) (Yᵉ ,ᵉ yᵉ) =
    set-subsetᵉ
      ( hom-set-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
      ( subtype-hom-Large-Subprecategoryᵉ Xᵉ Yᵉ xᵉ yᵉ)

  is-set-hom-Large-Subprecategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Subprecategoryᵉ l1ᵉ)
    (Yᵉ : obj-Large-Subprecategoryᵉ l2ᵉ) → is-setᵉ (hom-Large-Subprecategoryᵉ Xᵉ Yᵉ)
  is-set-hom-Large-Subprecategoryᵉ Xᵉ Yᵉ =
    is-set-type-Setᵉ (hom-set-Large-Subprecategoryᵉ Xᵉ Yᵉ)

  id-hom-Large-Subprecategoryᵉ :
      {lᵉ : Level} (Xᵉ : obj-Large-Subprecategoryᵉ lᵉ) →
      hom-Large-Subprecategoryᵉ Xᵉ Xᵉ
  id-hom-Large-Subprecategoryᵉ (Xᵉ ,ᵉ xᵉ) =
    ( id-hom-Large-Precategoryᵉ Cᵉ ,ᵉ contains-id-Large-Subprecategoryᵉ Xᵉ xᵉ)

  comp-hom-Large-Subprecategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    (Xᵉ : obj-Large-Subprecategoryᵉ l1ᵉ)
    (Yᵉ : obj-Large-Subprecategoryᵉ l2ᵉ)
    (Zᵉ : obj-Large-Subprecategoryᵉ l3ᵉ) →
    hom-Large-Subprecategoryᵉ Yᵉ Zᵉ →
    hom-Large-Subprecategoryᵉ Xᵉ Yᵉ →
    hom-Large-Subprecategoryᵉ Xᵉ Zᵉ
  comp-hom-Large-Subprecategoryᵉ (Xᵉ ,ᵉ xᵉ) (Yᵉ ,ᵉ yᵉ) (Zᵉ ,ᵉ zᵉ) (Gᵉ ,ᵉ gᵉ) (Fᵉ ,ᵉ fᵉ) =
    ( comp-hom-Large-Precategoryᵉ Cᵉ Gᵉ Fᵉ ,ᵉ
      is-closed-under-composition-Large-Subprecategoryᵉ Xᵉ Yᵉ Zᵉ Gᵉ Fᵉ xᵉ yᵉ zᵉ gᵉ fᵉ)

  associative-comp-hom-Large-Subprecategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    (Xᵉ : obj-Large-Subprecategoryᵉ l1ᵉ)
    (Yᵉ : obj-Large-Subprecategoryᵉ l2ᵉ)
    (Zᵉ : obj-Large-Subprecategoryᵉ l3ᵉ)
    (Wᵉ : obj-Large-Subprecategoryᵉ l4ᵉ)
    (hᵉ : hom-Large-Subprecategoryᵉ Zᵉ Wᵉ)
    (gᵉ : hom-Large-Subprecategoryᵉ Yᵉ Zᵉ)
    (fᵉ : hom-Large-Subprecategoryᵉ Xᵉ Yᵉ) →
    comp-hom-Large-Subprecategoryᵉ Xᵉ Yᵉ Wᵉ
      ( comp-hom-Large-Subprecategoryᵉ Yᵉ Zᵉ Wᵉ hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-hom-Large-Subprecategoryᵉ Xᵉ Zᵉ Wᵉ
      ( hᵉ)
      ( comp-hom-Large-Subprecategoryᵉ Xᵉ Yᵉ Zᵉ gᵉ fᵉ)
  associative-comp-hom-Large-Subprecategoryᵉ
    ( Xᵉ ,ᵉ xᵉ) (Yᵉ ,ᵉ yᵉ) (Zᵉ ,ᵉ zᵉ) (Wᵉ ,ᵉ wᵉ) (Hᵉ ,ᵉ hᵉ) (Gᵉ ,ᵉ gᵉ) (Fᵉ ,ᵉ fᵉ) =
    eq-type-subtypeᵉ
      ( subtype-hom-Large-Subprecategoryᵉ Xᵉ Wᵉ xᵉ wᵉ)
      ( associative-comp-hom-Large-Precategoryᵉ Cᵉ Hᵉ Gᵉ Fᵉ)

  involutive-eq-associative-comp-hom-Large-Subprecategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    (Xᵉ : obj-Large-Subprecategoryᵉ l1ᵉ)
    (Yᵉ : obj-Large-Subprecategoryᵉ l2ᵉ)
    (Zᵉ : obj-Large-Subprecategoryᵉ l3ᵉ)
    (Wᵉ : obj-Large-Subprecategoryᵉ l4ᵉ)
    (hᵉ : hom-Large-Subprecategoryᵉ Zᵉ Wᵉ)
    (gᵉ : hom-Large-Subprecategoryᵉ Yᵉ Zᵉ)
    (fᵉ : hom-Large-Subprecategoryᵉ Xᵉ Yᵉ) →
    comp-hom-Large-Subprecategoryᵉ Xᵉ Yᵉ Wᵉ
      ( comp-hom-Large-Subprecategoryᵉ Yᵉ Zᵉ Wᵉ hᵉ gᵉ)
      ( fᵉ) ＝ⁱᵉ
    comp-hom-Large-Subprecategoryᵉ Xᵉ Zᵉ Wᵉ
      ( hᵉ)
      ( comp-hom-Large-Subprecategoryᵉ Xᵉ Yᵉ Zᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Large-Subprecategoryᵉ
    Xᵉ Yᵉ Zᵉ Wᵉ hᵉ gᵉ fᵉ =
    involutive-eq-eqᵉ (associative-comp-hom-Large-Subprecategoryᵉ Xᵉ Yᵉ Zᵉ Wᵉ hᵉ gᵉ fᵉ)

  left-unit-law-comp-hom-Large-Subprecategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Subprecategoryᵉ l1ᵉ)
    (Yᵉ : obj-Large-Subprecategoryᵉ l2ᵉ)
    (fᵉ : hom-Large-Subprecategoryᵉ Xᵉ Yᵉ) →
    comp-hom-Large-Subprecategoryᵉ Xᵉ Yᵉ Yᵉ (id-hom-Large-Subprecategoryᵉ Yᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Large-Subprecategoryᵉ (Xᵉ ,ᵉ xᵉ) (Yᵉ ,ᵉ yᵉ) (Fᵉ ,ᵉ fᵉ) =
    eq-type-subtypeᵉ
      ( subtype-hom-Large-Subprecategoryᵉ Xᵉ Yᵉ xᵉ yᵉ)
      ( left-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ Fᵉ)

  right-unit-law-comp-hom-Large-Subprecategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Subprecategoryᵉ l1ᵉ)
    (Yᵉ : obj-Large-Subprecategoryᵉ l2ᵉ)
    (fᵉ : hom-Large-Subprecategoryᵉ Xᵉ Yᵉ) →
    comp-hom-Large-Subprecategoryᵉ Xᵉ Xᵉ Yᵉ fᵉ (id-hom-Large-Subprecategoryᵉ Xᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-hom-Large-Subprecategoryᵉ (Xᵉ ,ᵉ xᵉ) (Yᵉ ,ᵉ yᵉ) (Fᵉ ,ᵉ fᵉ) =
    eq-type-subtypeᵉ
      ( subtype-hom-Large-Subprecategoryᵉ Xᵉ Yᵉ xᵉ yᵉ)
      ( right-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ Fᵉ)
```

### The underlying large precategory of a large subprecategory

```agda
  large-precategory-Large-Subprecategoryᵉ :
    Large-Precategoryᵉ (λ lᵉ → αᵉ lᵉ ⊔ γᵉ lᵉ) (λ l1ᵉ l2ᵉ → βᵉ l1ᵉ l2ᵉ ⊔ δᵉ l1ᵉ l2ᵉ)
  large-precategory-Large-Subprecategoryᵉ =
    λ where
      .obj-Large-Precategoryᵉ →
        obj-Large-Subprecategoryᵉ
      .hom-set-Large-Precategoryᵉ →
        hom-set-Large-Subprecategoryᵉ
      .comp-hom-Large-Precategoryᵉ {Xᵉ = Xᵉ} {Yᵉ} {Zᵉ} →
        comp-hom-Large-Subprecategoryᵉ Xᵉ Yᵉ Zᵉ
      .id-hom-Large-Precategoryᵉ {Xᵉ = Xᵉ} →
        id-hom-Large-Subprecategoryᵉ Xᵉ
      .involutive-eq-associative-comp-hom-Large-Precategoryᵉ
        {Xᵉ = Xᵉ} {Yᵉ} {Zᵉ} {Wᵉ} →
        involutive-eq-associative-comp-hom-Large-Subprecategoryᵉ Xᵉ Yᵉ Zᵉ Wᵉ
      .left-unit-law-comp-hom-Large-Precategoryᵉ {Xᵉ = Xᵉ} {Yᵉ} →
        left-unit-law-comp-hom-Large-Subprecategoryᵉ Xᵉ Yᵉ
      .right-unit-law-comp-hom-Large-Precategoryᵉ {Xᵉ = Xᵉ} {Yᵉ} →
        right-unit-law-comp-hom-Large-Subprecategoryᵉ Xᵉ Yᵉ

open Large-Subprecategoryᵉ public
```