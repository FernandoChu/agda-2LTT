# Homotopies

```agda
module foundation-core.homotopiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.dependent-identificationsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Aᵉ **homotopy**ᵉ betweenᵉ dependentᵉ functionsᵉ `f`ᵉ andᵉ `g`ᵉ isᵉ aᵉ pointwiseᵉ equalityᵉ
betweenᵉ them.ᵉ

## Definitions

### The type family of identifications between values of two dependent functions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Pᵉ : Xᵉ → UUᵉ l2ᵉ} (fᵉ gᵉ : (xᵉ : Xᵉ) → Pᵉ xᵉ)
  where

  eq-valueᵉ : Xᵉ → UUᵉ l2ᵉ
  eq-valueᵉ xᵉ = (fᵉ xᵉ ＝ᵉ gᵉ xᵉ)

  {-# INLINE eq-valueᵉ #-}

  map-compute-dependent-identification-eq-valueᵉ :
    {xᵉ yᵉ : Xᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : eq-valueᵉ xᵉ) (rᵉ : eq-valueᵉ yᵉ) →
    apdᵉ fᵉ pᵉ ∙ᵉ rᵉ ＝ᵉ apᵉ (trᵉ Pᵉ pᵉ) qᵉ ∙ᵉ apdᵉ gᵉ pᵉ →
    dependent-identificationᵉ eq-valueᵉ pᵉ qᵉ rᵉ
  map-compute-dependent-identification-eq-valueᵉ reflᵉ qᵉ rᵉ =
    invᵉ ∘ᵉ (concat'ᵉ rᵉ (right-unitᵉ ∙ᵉ ap-idᵉ qᵉ))
```

### The type family of identifications between values of two ordinary functions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ gᵉ : Xᵉ → Yᵉ)
  where

  eq-value-functionᵉ : Xᵉ → UUᵉ l2ᵉ
  eq-value-functionᵉ = eq-valueᵉ fᵉ gᵉ

  {-# INLINE eq-value-functionᵉ #-}

  map-compute-dependent-identification-eq-value-functionᵉ :
    {xᵉ yᵉ : Xᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : eq-valueᵉ fᵉ gᵉ xᵉ) (rᵉ : eq-valueᵉ fᵉ gᵉ yᵉ) →
    apᵉ fᵉ pᵉ ∙ᵉ rᵉ ＝ᵉ qᵉ ∙ᵉ apᵉ gᵉ pᵉ →
    dependent-identificationᵉ eq-value-functionᵉ pᵉ qᵉ rᵉ
  map-compute-dependent-identification-eq-value-functionᵉ reflᵉ qᵉ rᵉ =
    invᵉ ∘ᵉ concat'ᵉ rᵉ right-unitᵉ

map-compute-dependent-identification-eq-value-id-idᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {aᵉ bᵉ : Aᵉ} (pᵉ : aᵉ ＝ᵉ bᵉ) (qᵉ : aᵉ ＝ᵉ aᵉ) (rᵉ : bᵉ ＝ᵉ bᵉ) →
  pᵉ ∙ᵉ rᵉ ＝ᵉ qᵉ ∙ᵉ pᵉ → dependent-identificationᵉ (eq-valueᵉ idᵉ idᵉ) pᵉ qᵉ rᵉ
map-compute-dependent-identification-eq-value-id-idᵉ reflᵉ qᵉ rᵉ sᵉ =
  invᵉ (sᵉ ∙ᵉ right-unitᵉ)

map-compute-dependent-identification-eq-value-comp-idᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (gᵉ : Bᵉ → Aᵉ) (fᵉ : Aᵉ → Bᵉ) {aᵉ bᵉ : Aᵉ}
  (pᵉ : aᵉ ＝ᵉ bᵉ) (qᵉ : eq-valueᵉ (gᵉ ∘ᵉ fᵉ) idᵉ aᵉ) (rᵉ : eq-valueᵉ (gᵉ ∘ᵉ fᵉ) idᵉ bᵉ) →
  apᵉ gᵉ (apᵉ fᵉ pᵉ) ∙ᵉ rᵉ ＝ᵉ qᵉ ∙ᵉ pᵉ →
  dependent-identificationᵉ (eq-valueᵉ (gᵉ ∘ᵉ fᵉ) idᵉ) pᵉ qᵉ rᵉ
map-compute-dependent-identification-eq-value-comp-idᵉ gᵉ fᵉ reflᵉ qᵉ rᵉ sᵉ =
  invᵉ (sᵉ ∙ᵉ right-unitᵉ)
```

### Homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  infix 6 _~ᵉ_
  _~ᵉ_ : (fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  fᵉ ~ᵉ gᵉ = (xᵉ : Aᵉ) → eq-valueᵉ fᵉ gᵉ xᵉ
```

## Properties

### Reflexivity

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  refl-htpyᵉ : {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} → fᵉ ~ᵉ fᵉ
  refl-htpyᵉ xᵉ = reflᵉ

  refl-htpy'ᵉ : (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → fᵉ ~ᵉ fᵉ
  refl-htpy'ᵉ fᵉ = refl-htpyᵉ
```

### Inverting homotopies

```agda
  inv-htpyᵉ : {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} → fᵉ ~ᵉ gᵉ → gᵉ ~ᵉ fᵉ
  inv-htpyᵉ Hᵉ xᵉ = invᵉ (Hᵉ xᵉ)
```

### Concatenating homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  infixl 15 _∙hᵉ_
  _∙hᵉ_ : {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} → fᵉ ~ᵉ gᵉ → gᵉ ~ᵉ hᵉ → fᵉ ~ᵉ hᵉ
  (Hᵉ ∙hᵉ Kᵉ) xᵉ = (Hᵉ xᵉ) ∙ᵉ (Kᵉ xᵉ)

  concat-htpyᵉ :
    {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} →
    fᵉ ~ᵉ gᵉ → (hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → gᵉ ~ᵉ hᵉ → fᵉ ~ᵉ hᵉ
  concat-htpyᵉ Hᵉ hᵉ Kᵉ xᵉ = concatᵉ (Hᵉ xᵉ) (hᵉ xᵉ) (Kᵉ xᵉ)

  concat-htpy'ᵉ :
    (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) {gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} →
    gᵉ ~ᵉ hᵉ → fᵉ ~ᵉ gᵉ → fᵉ ~ᵉ hᵉ
  concat-htpy'ᵉ fᵉ Kᵉ Hᵉ = Hᵉ ∙hᵉ Kᵉ

  concat-inv-htpyᵉ :
    {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} →
    fᵉ ~ᵉ gᵉ → (hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → fᵉ ~ᵉ hᵉ → gᵉ ~ᵉ hᵉ
  concat-inv-htpyᵉ = concat-htpyᵉ ∘ᵉ inv-htpyᵉ

  concat-inv-htpy'ᵉ :
    (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) {gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} →
    gᵉ ~ᵉ hᵉ → fᵉ ~ᵉ hᵉ → fᵉ ~ᵉ gᵉ
  concat-inv-htpy'ᵉ fᵉ Kᵉ = concat-htpy'ᵉ fᵉ (inv-htpyᵉ Kᵉ)
```

### Transposition of homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (Hᵉ : fᵉ ~ᵉ gᵉ) (Kᵉ : gᵉ ~ᵉ hᵉ) (Lᵉ : fᵉ ~ᵉ hᵉ) (Mᵉ : Hᵉ ∙hᵉ Kᵉ ~ᵉ Lᵉ)
  where

  left-transpose-htpy-concatᵉ : Kᵉ ~ᵉ inv-htpyᵉ Hᵉ ∙hᵉ Lᵉ
  left-transpose-htpy-concatᵉ xᵉ =
    left-transpose-eq-concatᵉ (Hᵉ xᵉ) (Kᵉ xᵉ) (Lᵉ xᵉ) (Mᵉ xᵉ)

  inv-htpy-left-transpose-htpy-concatᵉ : inv-htpyᵉ Hᵉ ∙hᵉ Lᵉ ~ᵉ Kᵉ
  inv-htpy-left-transpose-htpy-concatᵉ = inv-htpyᵉ left-transpose-htpy-concatᵉ

  right-transpose-htpy-concatᵉ : Hᵉ ~ᵉ Lᵉ ∙hᵉ inv-htpyᵉ Kᵉ
  right-transpose-htpy-concatᵉ xᵉ =
    right-transpose-eq-concatᵉ (Hᵉ xᵉ) (Kᵉ xᵉ) (Lᵉ xᵉ) (Mᵉ xᵉ)

  inv-htpy-right-transpose-htpy-concatᵉ : Lᵉ ∙hᵉ inv-htpyᵉ Kᵉ ~ᵉ Hᵉ
  inv-htpy-right-transpose-htpy-concatᵉ = inv-htpyᵉ right-transpose-htpy-concatᵉ
```

### Associativity of concatenation of homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ kᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (Hᵉ : fᵉ ~ᵉ gᵉ) (Kᵉ : gᵉ ~ᵉ hᵉ) (Lᵉ : hᵉ ~ᵉ kᵉ)
  where

  assoc-htpyᵉ : (Hᵉ ∙hᵉ Kᵉ) ∙hᵉ Lᵉ ~ᵉ Hᵉ ∙hᵉ (Kᵉ ∙hᵉ Lᵉ)
  assoc-htpyᵉ xᵉ = assocᵉ (Hᵉ xᵉ) (Kᵉ xᵉ) (Lᵉ xᵉ)

  inv-htpy-assoc-htpyᵉ : Hᵉ ∙hᵉ (Kᵉ ∙hᵉ Lᵉ) ~ᵉ (Hᵉ ∙hᵉ Kᵉ) ∙hᵉ Lᵉ
  inv-htpy-assoc-htpyᵉ = inv-htpyᵉ assoc-htpyᵉ
```

### Unit laws for homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} {Hᵉ : fᵉ ~ᵉ gᵉ}
  where

  left-unit-htpyᵉ : refl-htpyᵉ ∙hᵉ Hᵉ ~ᵉ Hᵉ
  left-unit-htpyᵉ xᵉ = left-unitᵉ

  inv-htpy-left-unit-htpyᵉ : Hᵉ ~ᵉ refl-htpyᵉ ∙hᵉ Hᵉ
  inv-htpy-left-unit-htpyᵉ = inv-htpyᵉ left-unit-htpyᵉ

  right-unit-htpyᵉ : Hᵉ ∙hᵉ refl-htpyᵉ ~ᵉ Hᵉ
  right-unit-htpyᵉ xᵉ = right-unitᵉ

  inv-htpy-right-unit-htpyᵉ : Hᵉ ~ᵉ Hᵉ ∙hᵉ refl-htpyᵉ
  inv-htpy-right-unit-htpyᵉ = inv-htpyᵉ right-unit-htpyᵉ
```

### Inverse laws for homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ)
  where

  left-inv-htpyᵉ : inv-htpyᵉ Hᵉ ∙hᵉ Hᵉ ~ᵉ refl-htpyᵉ
  left-inv-htpyᵉ = left-invᵉ ∘ᵉ Hᵉ

  inv-htpy-left-inv-htpyᵉ : refl-htpyᵉ ~ᵉ inv-htpyᵉ Hᵉ ∙hᵉ Hᵉ
  inv-htpy-left-inv-htpyᵉ = inv-htpyᵉ left-inv-htpyᵉ

  right-inv-htpyᵉ : Hᵉ ∙hᵉ inv-htpyᵉ Hᵉ ~ᵉ refl-htpyᵉ
  right-inv-htpyᵉ = right-invᵉ ∘ᵉ Hᵉ

  inv-htpy-right-inv-htpyᵉ : refl-htpyᵉ ~ᵉ Hᵉ ∙hᵉ inv-htpyᵉ Hᵉ
  inv-htpy-right-inv-htpyᵉ = inv-htpyᵉ right-inv-htpyᵉ
```

### Inverting homotopies is an involution

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ)
  where

  inv-inv-htpyᵉ : inv-htpyᵉ (inv-htpyᵉ Hᵉ) ~ᵉ Hᵉ
  inv-inv-htpyᵉ = inv-invᵉ ∘ᵉ Hᵉ
```

### Distributivity of `inv` over `concat` for homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (Hᵉ : fᵉ ~ᵉ gᵉ) (Kᵉ : gᵉ ~ᵉ hᵉ)
  where

  distributive-inv-concat-htpyᵉ :
    inv-htpyᵉ (Hᵉ ∙hᵉ Kᵉ) ~ᵉ inv-htpyᵉ Kᵉ ∙hᵉ inv-htpyᵉ Hᵉ
  distributive-inv-concat-htpyᵉ xᵉ = distributive-inv-concatᵉ (Hᵉ xᵉ) (Kᵉ xᵉ)

  inv-htpy-distributive-inv-concat-htpyᵉ :
    inv-htpyᵉ Kᵉ ∙hᵉ inv-htpyᵉ Hᵉ ~ᵉ inv-htpyᵉ (Hᵉ ∙hᵉ Kᵉ)
  inv-htpy-distributive-inv-concat-htpyᵉ =
    inv-htpyᵉ distributive-inv-concat-htpyᵉ
```

### Naturality of homotopies with respect to identifications

Givenᵉ twoᵉ mapsᵉ `fᵉ gᵉ : Aᵉ → B`ᵉ andᵉ aᵉ homotopyᵉ `Hᵉ : fᵉ ~ᵉ g`,ᵉ thenᵉ forᵉ everyᵉ
identificationᵉ `pᵉ : xᵉ ＝ᵉ y`ᵉ in `A`,ᵉ weᵉ haveᵉ aᵉ
[commutingᵉ squareᵉ ofᵉ identifications](foundation-core.commuting-squares-of-identifications.mdᵉ)

```text
          apᵉ fᵉ pᵉ
     fᵉ xᵉ ------->ᵉ fᵉ yᵉ
      |            |
  Hᵉ xᵉ |            | Hᵉ yᵉ
      ∨ᵉ            ∨ᵉ
     gᵉ xᵉ ------->ᵉ gᵉ y.ᵉ
          apᵉ gᵉ pᵉ
```

```agda
nat-htpyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ gᵉ : Aᵉ → Bᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ)
  {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
  Hᵉ xᵉ ∙ᵉ apᵉ gᵉ pᵉ ＝ᵉ apᵉ fᵉ pᵉ ∙ᵉ Hᵉ yᵉ
nat-htpyᵉ Hᵉ reflᵉ = right-unitᵉ

inv-nat-htpyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ gᵉ : Aᵉ → Bᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ)
  {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
  apᵉ fᵉ pᵉ ∙ᵉ Hᵉ yᵉ ＝ᵉ Hᵉ xᵉ ∙ᵉ apᵉ gᵉ pᵉ
inv-nat-htpyᵉ Hᵉ pᵉ = invᵉ (nat-htpyᵉ Hᵉ pᵉ)

nat-refl-htpyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
  nat-htpyᵉ (refl-htpy'ᵉ fᵉ) pᵉ ＝ᵉ invᵉ right-unitᵉ
nat-refl-htpyᵉ fᵉ reflᵉ = reflᵉ

inv-nat-refl-htpyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
  inv-nat-htpyᵉ (refl-htpy'ᵉ fᵉ) pᵉ ＝ᵉ right-unitᵉ
inv-nat-refl-htpyᵉ fᵉ reflᵉ = reflᵉ

nat-htpy-idᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {fᵉ : Aᵉ → Aᵉ} (Hᵉ : fᵉ ~ᵉ idᵉ)
  {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → Hᵉ xᵉ ∙ᵉ pᵉ ＝ᵉ apᵉ fᵉ pᵉ ∙ᵉ Hᵉ yᵉ
nat-htpy-idᵉ Hᵉ reflᵉ = right-unitᵉ

inv-nat-htpy-idᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {fᵉ : Aᵉ → Aᵉ} (Hᵉ : fᵉ ~ᵉ idᵉ)
  {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → apᵉ fᵉ pᵉ ∙ᵉ Hᵉ yᵉ ＝ᵉ Hᵉ xᵉ ∙ᵉ pᵉ
inv-nat-htpy-idᵉ Hᵉ pᵉ = invᵉ (nat-htpy-idᵉ Hᵉ pᵉ)
```

### Homotopies preserve the laws of the action on identity types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  ap-concat-htpyᵉ :
    (Hᵉ : fᵉ ~ᵉ gᵉ) {Kᵉ K'ᵉ : gᵉ ~ᵉ hᵉ} → Kᵉ ~ᵉ K'ᵉ → Hᵉ ∙hᵉ Kᵉ ~ᵉ Hᵉ ∙hᵉ K'ᵉ
  ap-concat-htpyᵉ Hᵉ Lᵉ xᵉ = apᵉ (concatᵉ (Hᵉ xᵉ) (hᵉ xᵉ)) (Lᵉ xᵉ)

  ap-concat-htpy'ᵉ :
    {Hᵉ H'ᵉ : fᵉ ~ᵉ gᵉ} (Kᵉ : gᵉ ~ᵉ hᵉ) → Hᵉ ~ᵉ H'ᵉ → Hᵉ ∙hᵉ Kᵉ ~ᵉ H'ᵉ ∙hᵉ Kᵉ
  ap-concat-htpy'ᵉ Kᵉ Lᵉ xᵉ =
    apᵉ (concat'ᵉ (fᵉ xᵉ) (Kᵉ xᵉ)) (Lᵉ xᵉ)

  ap-binary-concat-htpyᵉ :
    {Hᵉ H'ᵉ : fᵉ ~ᵉ gᵉ} {Kᵉ K'ᵉ : gᵉ ~ᵉ hᵉ} → Hᵉ ~ᵉ H'ᵉ → Kᵉ ~ᵉ K'ᵉ → Hᵉ ∙hᵉ Kᵉ ~ᵉ H'ᵉ ∙hᵉ K'ᵉ
  ap-binary-concat-htpyᵉ {Hᵉ} {H'ᵉ} {Kᵉ} {K'ᵉ} HHᵉ KKᵉ =
    ap-concat-htpyᵉ Hᵉ KKᵉ ∙hᵉ ap-concat-htpy'ᵉ K'ᵉ HHᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  {Hᵉ H'ᵉ : fᵉ ~ᵉ gᵉ}
  where

  ap-inv-htpyᵉ :
    Hᵉ ~ᵉ H'ᵉ → inv-htpyᵉ Hᵉ ~ᵉ inv-htpyᵉ H'ᵉ
  ap-inv-htpyᵉ Kᵉ xᵉ = apᵉ invᵉ (Kᵉ xᵉ)
```

### Concatenating with an inverse homotopy is inverse to concatenating

Weᵉ showᵉ thatᵉ theᵉ operationᵉ `Kᵉ ↦ᵉ inv-htpyᵉ Hᵉ ∙hᵉ K`ᵉ isᵉ inverseᵉ to theᵉ operationᵉ
`Kᵉ ↦ᵉ Hᵉ ∙hᵉ K`ᵉ byᵉ constructingᵉ homotopiesᵉ

```text
  inv-htpyᵉ Hᵉ ∙hᵉ (Hᵉ ∙hᵉ Kᵉ) ~ᵉ Kᵉ
  Hᵉ ∙hᵉ (invᵉ Hᵉ ∙hᵉ Kᵉ) ~ᵉ K.ᵉ
```

Similarly,ᵉ weᵉ showᵉ thatᵉ theᵉ operationᵉ `Hᵉ ↦ᵉ Hᵉ ∙hᵉ inv-htpyᵉ K`ᵉ isᵉ inverseᵉ to theᵉ
operationᵉ `Hᵉ ↦ᵉ Hᵉ ∙hᵉ K`ᵉ byᵉ constructingᵉ homotopiesᵉ

```text
  (Hᵉ ∙hᵉ Kᵉ) ∙hᵉ inv-htpyᵉ Kᵉ ~ᵉ Hᵉ
  (Hᵉ ∙hᵉ inv-htpyᵉ Kᵉ) ∙hᵉ Kᵉ ~ᵉ H.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  is-retraction-inv-concat-htpyᵉ :
    (Hᵉ : fᵉ ~ᵉ gᵉ) (Kᵉ : gᵉ ~ᵉ hᵉ) → inv-htpyᵉ Hᵉ ∙hᵉ (Hᵉ ∙hᵉ Kᵉ) ~ᵉ Kᵉ
  is-retraction-inv-concat-htpyᵉ Hᵉ Kᵉ xᵉ = is-retraction-inv-concatᵉ (Hᵉ xᵉ) (Kᵉ xᵉ)

  is-section-inv-concat-htpyᵉ :
    (Hᵉ : fᵉ ~ᵉ gᵉ) (Lᵉ : fᵉ ~ᵉ hᵉ) → Hᵉ ∙hᵉ (inv-htpyᵉ Hᵉ ∙hᵉ Lᵉ) ~ᵉ Lᵉ
  is-section-inv-concat-htpyᵉ Hᵉ Lᵉ xᵉ = is-section-inv-concatᵉ (Hᵉ xᵉ) (Lᵉ xᵉ)

  is-retraction-inv-concat-htpy'ᵉ :
    (Kᵉ : gᵉ ~ᵉ hᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ) → (Hᵉ ∙hᵉ Kᵉ) ∙hᵉ inv-htpyᵉ Kᵉ ~ᵉ Hᵉ
  is-retraction-inv-concat-htpy'ᵉ Kᵉ Hᵉ xᵉ = is-retraction-inv-concat'ᵉ (Kᵉ xᵉ) (Hᵉ xᵉ)

  is-section-inv-concat-htpy'ᵉ :
    (Kᵉ : gᵉ ~ᵉ hᵉ) (Lᵉ : fᵉ ~ᵉ hᵉ) → (Lᵉ ∙hᵉ inv-htpyᵉ Kᵉ) ∙hᵉ Kᵉ ~ᵉ Lᵉ
  is-section-inv-concat-htpy'ᵉ Kᵉ Lᵉ xᵉ = is-section-inv-concat'ᵉ (Kᵉ xᵉ) (Lᵉ xᵉ)
```

## Reasoning with homotopies

Homotopiesᵉ canᵉ beᵉ constructedᵉ byᵉ equationalᵉ reasoningᵉ in theᵉ followingᵉ wayᵉ:

```text
homotopy-reasoningᵉ
  fᵉ ~ᵉ gᵉ byᵉ htpy-1ᵉ
    ~ᵉ hᵉ byᵉ htpy-2ᵉ
    ~ᵉ iᵉ byᵉ htpy-3ᵉ
```

Theᵉ homotopyᵉ obtainedᵉ in thisᵉ wayᵉ isᵉ `htpy-1ᵉ ∙hᵉ (htpy-2ᵉ ∙hᵉ htpy-3)`,ᵉ i.e.,ᵉ itᵉ isᵉ
associatedᵉ fullyᵉ to theᵉ right.ᵉ

```agda
infixl 1 homotopy-reasoningᵉ_
infixl 0 step-homotopy-reasoningᵉ

homotopy-reasoningᵉ_ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : Xᵉ → UUᵉ l2ᵉ}
  (fᵉ : (xᵉ : Xᵉ) → Yᵉ xᵉ) → fᵉ ~ᵉ fᵉ
homotopy-reasoningᵉ fᵉ = refl-htpyᵉ

step-homotopy-reasoningᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : Xᵉ → UUᵉ l2ᵉ}
  {fᵉ gᵉ : (xᵉ : Xᵉ) → Yᵉ xᵉ} → fᵉ ~ᵉ gᵉ →
  (hᵉ : (xᵉ : Xᵉ) → Yᵉ xᵉ) → gᵉ ~ᵉ hᵉ → fᵉ ~ᵉ hᵉ
step-homotopy-reasoningᵉ pᵉ hᵉ qᵉ = pᵉ ∙hᵉ qᵉ

syntax step-homotopy-reasoningᵉ pᵉ hᵉ qᵉ = pᵉ ~ᵉ hᵉ byᵉ qᵉ
```

## See also

-ᵉ Weᵉ postulate thatᵉ homotopiesᵉ characterizeᵉ identificationsᵉ ofᵉ (dependentᵉ)
  functionsᵉ in theᵉ fileᵉ
  [`foundation.function-extensionality`](foundation.function-extensionality.md).ᵉ
-ᵉ [Multivariableᵉ homotopies](foundation.multivariable-homotopies.md).ᵉ
-ᵉ Theᵉ [whiskeringᵉ operations](foundation.whiskering-homotopies-composition.mdᵉ)
  onᵉ homotopies.ᵉ