# Large precategories

```agda
module category-theory.large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategoriesᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **largeᵉ precategory**ᵉ isᵉ aᵉ [precategory](category-theory.precategories.mdᵉ)
where weᵉ don'tᵉ fixᵉ aᵉ universeᵉ forᵉ theᵉ typeᵉ ofᵉ objectsᵉ orᵉ morphisms.ᵉ (Thisᵉ cannotᵉ
beᵉ doneᵉ with Σ-types,ᵉ weᵉ mustᵉ useᵉ aᵉ record type.ᵉ)

## Definition

### The large type of large precategories

```agda
record
  Large-Precategoryᵉ (αᵉ : Level → Level) (βᵉ : Level → Level → Level) : UUωᵉ where

  field
    obj-Large-Precategoryᵉ :
      (lᵉ : Level) → UUᵉ (αᵉ lᵉ)

    hom-set-Large-Precategoryᵉ :
      {l1ᵉ l2ᵉ : Level} →
      obj-Large-Precategoryᵉ l1ᵉ →
      obj-Large-Precategoryᵉ l2ᵉ →
      Setᵉ (βᵉ l1ᵉ l2ᵉ)

  hom-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level} →
    obj-Large-Precategoryᵉ l1ᵉ →
    obj-Large-Precategoryᵉ l2ᵉ →
    UUᵉ (βᵉ l1ᵉ l2ᵉ)
  hom-Large-Precategoryᵉ Xᵉ Yᵉ = type-Setᵉ (hom-set-Large-Precategoryᵉ Xᵉ Yᵉ)

  is-set-hom-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Precategoryᵉ l1ᵉ)
    (Yᵉ : obj-Large-Precategoryᵉ l2ᵉ) →
    is-setᵉ (hom-Large-Precategoryᵉ Xᵉ Yᵉ)
  is-set-hom-Large-Precategoryᵉ Xᵉ Yᵉ =
    is-set-type-Setᵉ (hom-set-Large-Precategoryᵉ Xᵉ Yᵉ)

  field
    comp-hom-Large-Precategoryᵉ :
      {l1ᵉ l2ᵉ l3ᵉ : Level}
      {Xᵉ : obj-Large-Precategoryᵉ l1ᵉ}
      {Yᵉ : obj-Large-Precategoryᵉ l2ᵉ}
      {Zᵉ : obj-Large-Precategoryᵉ l3ᵉ} →
      hom-Large-Precategoryᵉ Yᵉ Zᵉ →
      hom-Large-Precategoryᵉ Xᵉ Yᵉ →
      hom-Large-Precategoryᵉ Xᵉ Zᵉ

    id-hom-Large-Precategoryᵉ :
      {l1ᵉ : Level}
      {Xᵉ : obj-Large-Precategoryᵉ l1ᵉ} →
      hom-Large-Precategoryᵉ Xᵉ Xᵉ

    involutive-eq-associative-comp-hom-Large-Precategoryᵉ :
      {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
      {Xᵉ : obj-Large-Precategoryᵉ l1ᵉ}
      {Yᵉ : obj-Large-Precategoryᵉ l2ᵉ}
      {Zᵉ : obj-Large-Precategoryᵉ l3ᵉ}
      {Wᵉ : obj-Large-Precategoryᵉ l4ᵉ} →
      (hᵉ : hom-Large-Precategoryᵉ Zᵉ Wᵉ)
      (gᵉ : hom-Large-Precategoryᵉ Yᵉ Zᵉ)
      (fᵉ : hom-Large-Precategoryᵉ Xᵉ Yᵉ) →
      ( comp-hom-Large-Precategoryᵉ (comp-hom-Large-Precategoryᵉ hᵉ gᵉ) fᵉ) ＝ⁱᵉ
      ( comp-hom-Large-Precategoryᵉ hᵉ (comp-hom-Large-Precategoryᵉ gᵉ fᵉ))

    left-unit-law-comp-hom-Large-Precategoryᵉ :
      {l1ᵉ l2ᵉ : Level}
      {Xᵉ : obj-Large-Precategoryᵉ l1ᵉ}
      {Yᵉ : obj-Large-Precategoryᵉ l2ᵉ}
      (fᵉ : hom-Large-Precategoryᵉ Xᵉ Yᵉ) →
      ( comp-hom-Large-Precategoryᵉ id-hom-Large-Precategoryᵉ fᵉ) ＝ᵉ fᵉ

    right-unit-law-comp-hom-Large-Precategoryᵉ :
      {l1ᵉ l2ᵉ : Level}
      {Xᵉ : obj-Large-Precategoryᵉ l1ᵉ}
      {Yᵉ : obj-Large-Precategoryᵉ l2ᵉ}
      (fᵉ : hom-Large-Precategoryᵉ Xᵉ Yᵉ) →
      ( comp-hom-Large-Precategoryᵉ fᵉ id-hom-Large-Precategoryᵉ) ＝ᵉ fᵉ

  associative-comp-hom-Large-Precategoryᵉ :
      {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
      {Xᵉ : obj-Large-Precategoryᵉ l1ᵉ}
      {Yᵉ : obj-Large-Precategoryᵉ l2ᵉ}
      {Zᵉ : obj-Large-Precategoryᵉ l3ᵉ}
      {Wᵉ : obj-Large-Precategoryᵉ l4ᵉ} →
      (hᵉ : hom-Large-Precategoryᵉ Zᵉ Wᵉ)
      (gᵉ : hom-Large-Precategoryᵉ Yᵉ Zᵉ)
      (fᵉ : hom-Large-Precategoryᵉ Xᵉ Yᵉ) →
      ( comp-hom-Large-Precategoryᵉ (comp-hom-Large-Precategoryᵉ hᵉ gᵉ) fᵉ) ＝ᵉ
      ( comp-hom-Large-Precategoryᵉ hᵉ (comp-hom-Large-Precategoryᵉ gᵉ fᵉ))
  associative-comp-hom-Large-Precategoryᵉ hᵉ gᵉ fᵉ =
    eq-involutive-eqᵉ
      ( involutive-eq-associative-comp-hom-Large-Precategoryᵉ hᵉ gᵉ fᵉ)

open Large-Precategoryᵉ public

make-Large-Precategoryᵉ :
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  ( objᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ))
  ( hom-setᵉ : {l1ᵉ l2ᵉ : Level} → objᵉ l1ᵉ → objᵉ l2ᵉ → Setᵉ (βᵉ l1ᵉ l2ᵉ))
  ( _∘ᵉ_ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    {Xᵉ : objᵉ l1ᵉ} {Yᵉ : objᵉ l2ᵉ} {Zᵉ : objᵉ l3ᵉ} →
    type-Setᵉ (hom-setᵉ Yᵉ Zᵉ) → type-Setᵉ (hom-setᵉ Xᵉ Yᵉ) → type-Setᵉ (hom-setᵉ Xᵉ Zᵉ))
  ( idᵉ : {lᵉ : Level} {Xᵉ : objᵉ lᵉ} → type-Setᵉ (hom-setᵉ Xᵉ Xᵉ))
  ( assoc-comp-homᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Xᵉ : objᵉ l1ᵉ} {Yᵉ : objᵉ l2ᵉ} {Zᵉ : objᵉ l3ᵉ} {Wᵉ : objᵉ l4ᵉ}
    (hᵉ : type-Setᵉ (hom-setᵉ Zᵉ Wᵉ))
    (gᵉ : type-Setᵉ (hom-setᵉ Yᵉ Zᵉ))
    (fᵉ : type-Setᵉ (hom-setᵉ Xᵉ Yᵉ)) →
    ( (hᵉ ∘ᵉ gᵉ) ∘ᵉ fᵉ) ＝ᵉ ( hᵉ ∘ᵉ (gᵉ ∘ᵉ fᵉ)))
  ( left-unit-comp-homᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : objᵉ l1ᵉ} {Yᵉ : objᵉ l2ᵉ} (fᵉ : type-Setᵉ (hom-setᵉ Xᵉ Yᵉ)) →
    idᵉ ∘ᵉ fᵉ ＝ᵉ fᵉ)
  ( right-unit-comp-homᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : objᵉ l1ᵉ} {Yᵉ : objᵉ l2ᵉ} (fᵉ : type-Setᵉ (hom-setᵉ Xᵉ Yᵉ)) →
    fᵉ ∘ᵉ idᵉ ＝ᵉ fᵉ) →
  Large-Precategoryᵉ αᵉ βᵉ
make-Large-Precategoryᵉ
  objᵉ hom-setᵉ _∘ᵉ_ idᵉ assoc-comp-homᵉ left-unit-comp-homᵉ right-unit-comp-homᵉ =
  λ where
    .obj-Large-Precategoryᵉ → objᵉ
    .hom-set-Large-Precategoryᵉ → hom-setᵉ
    .comp-hom-Large-Precategoryᵉ → _∘ᵉ_
    .id-hom-Large-Precategoryᵉ → idᵉ
    .involutive-eq-associative-comp-hom-Large-Precategoryᵉ hᵉ gᵉ fᵉ →
      involutive-eq-eqᵉ (assoc-comp-homᵉ hᵉ gᵉ fᵉ)
    .left-unit-law-comp-hom-Large-Precategoryᵉ → left-unit-comp-homᵉ
    .right-unit-law-comp-hom-Large-Precategoryᵉ → right-unit-comp-homᵉ

{-# INLINE make-Large-Precategoryᵉ #-}
```

```agda
module _
  {αᵉ : Level → Level}
  {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  where

  ap-comp-hom-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
    {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
    {Zᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ}
    {gᵉ g'ᵉ : hom-Large-Precategoryᵉ Cᵉ Yᵉ Zᵉ} (pᵉ : gᵉ ＝ᵉ g'ᵉ)
    {fᵉ f'ᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ} (qᵉ : fᵉ ＝ᵉ f'ᵉ) →
    comp-hom-Large-Precategoryᵉ Cᵉ gᵉ fᵉ ＝ᵉ
    comp-hom-Large-Precategoryᵉ Cᵉ g'ᵉ f'ᵉ
  ap-comp-hom-Large-Precategoryᵉ = ap-binaryᵉ (comp-hom-Large-Precategoryᵉ Cᵉ)

  comp-hom-Large-Precategory'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
    {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
    {Zᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ} →
    hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ →
    hom-Large-Precategoryᵉ Cᵉ Yᵉ Zᵉ →
    hom-Large-Precategoryᵉ Cᵉ Xᵉ Zᵉ
  comp-hom-Large-Precategory'ᵉ fᵉ gᵉ = comp-hom-Large-Precategoryᵉ Cᵉ gᵉ fᵉ
```

### Precategories obtained from large precategories

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  where

  precategory-Large-Precategoryᵉ :
    (lᵉ : Level) → Precategoryᵉ (αᵉ lᵉ) (βᵉ lᵉ lᵉ)
  pr1ᵉ (precategory-Large-Precategoryᵉ lᵉ) =
    obj-Large-Precategoryᵉ Cᵉ lᵉ
  pr1ᵉ (pr2ᵉ (precategory-Large-Precategoryᵉ lᵉ)) =
    hom-set-Large-Precategoryᵉ Cᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (precategory-Large-Precategoryᵉ lᵉ)))) =
    comp-hom-Large-Precategoryᵉ Cᵉ
  pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (precategory-Large-Precategoryᵉ lᵉ)))) =
    involutive-eq-associative-comp-hom-Large-Precategoryᵉ Cᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (precategory-Large-Precategoryᵉ lᵉ)))) xᵉ =
    id-hom-Large-Precategoryᵉ Cᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (precategory-Large-Precategoryᵉ lᵉ))))) =
    left-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (precategory-Large-Precategoryᵉ lᵉ))))) =
    right-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ
```

### Equalities induce morphisms

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  {l1ᵉ : Level}
  where

  hom-eq-Large-Precategoryᵉ :
    (Xᵉ Yᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ) → Xᵉ ＝ᵉ Yᵉ → hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ
  hom-eq-Large-Precategoryᵉ Xᵉ .Xᵉ reflᵉ = id-hom-Large-Precategoryᵉ Cᵉ

  hom-inv-eq-Large-Precategoryᵉ :
    (Xᵉ Yᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ) → Xᵉ ＝ᵉ Yᵉ → hom-Large-Precategoryᵉ Cᵉ Yᵉ Xᵉ
  hom-inv-eq-Large-Precategoryᵉ Xᵉ Yᵉ = hom-eq-Large-Precategoryᵉ Yᵉ Xᵉ ∘ᵉ invᵉ

  compute-hom-eq-Large-Precategoryᵉ :
    (Xᵉ Yᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ) →
    hom-eq-Precategoryᵉ (precategory-Large-Precategoryᵉ Cᵉ l1ᵉ) Xᵉ Yᵉ ~ᵉ
    hom-eq-Large-Precategoryᵉ Xᵉ Yᵉ
  compute-hom-eq-Large-Precategoryᵉ Xᵉ .Xᵉ reflᵉ = reflᵉ
```

### Pre- and postcomposition by a morphism

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  where

  precomp-hom-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
    {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
    (fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ) →
    (Zᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ) →
    hom-Large-Precategoryᵉ Cᵉ Yᵉ Zᵉ → hom-Large-Precategoryᵉ Cᵉ Xᵉ Zᵉ
  precomp-hom-Large-Precategoryᵉ fᵉ Zᵉ gᵉ =
    comp-hom-Large-Precategoryᵉ Cᵉ gᵉ fᵉ

  postcomp-hom-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    (Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ)
    {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
    {Zᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ}
    (fᵉ : hom-Large-Precategoryᵉ Cᵉ Yᵉ Zᵉ) →
    hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ → hom-Large-Precategoryᵉ Cᵉ Xᵉ Zᵉ
  postcomp-hom-Large-Precategoryᵉ Xᵉ fᵉ gᵉ =
    comp-hom-Large-Precategoryᵉ Cᵉ fᵉ gᵉ
```