# The action on identifications of functions

```agda
module foundation.action-on-identifications-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import foundation-core.constant-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Anyᵉ functionᵉ `fᵉ : Aᵉ → B`ᵉ preservesᵉ
[identifications](foundation-core.identity-types.md),ᵉ in theᵉ senseᵉ thatᵉ itᵉ mapsᵉ
identificationsᵉ `pᵉ : xᵉ ＝ᵉ y`ᵉ in `A`ᵉ to anᵉ identificationᵉ `apᵉ fᵉ pᵉ : fᵉ xᵉ ＝ᵉ fᵉ y`ᵉ
in `B`.ᵉ Thisᵉ actionᵉ onᵉ identificationsᵉ canᵉ beᵉ thoughtᵉ ofᵉ asᵉ theᵉ functorialityᵉ ofᵉ
identityᵉ types.ᵉ

## Definition

### The functorial action of functions on identity types

```agda
apᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) {xᵉ yᵉ : Aᵉ} →
  xᵉ ＝ᵉ yᵉ → (fᵉ xᵉ) ＝ᵉ (fᵉ yᵉ)
apᵉ fᵉ reflᵉ = reflᵉ
```

## Properties

### The identity function acts trivially on identifications

```agda
ap-idᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → (apᵉ idᵉ pᵉ) ＝ᵉ pᵉ
ap-idᵉ reflᵉ = reflᵉ
```

### The action on identifications of a composite function is the composite of the actions

```agda
ap-compᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (gᵉ : Bᵉ → Cᵉ)
  (fᵉ : Aᵉ → Bᵉ) {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → (apᵉ (gᵉ ∘ᵉ fᵉ) pᵉ) ＝ᵉ ((apᵉ gᵉ ∘ᵉ apᵉ fᵉ) pᵉ)
ap-compᵉ gᵉ fᵉ reflᵉ = reflᵉ

ap-comp-assocᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (hᵉ : Cᵉ → Dᵉ) (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ) {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
  apᵉ (hᵉ ∘ᵉ gᵉ) (apᵉ fᵉ pᵉ) ＝ᵉ apᵉ hᵉ (apᵉ (gᵉ ∘ᵉ fᵉ) pᵉ)
ap-comp-assocᵉ hᵉ gᵉ fᵉ reflᵉ = reflᵉ
```

### The action on identifications of any map preserves `refl`

```agda
ap-reflᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (xᵉ : Aᵉ) →
  (apᵉ fᵉ (reflᵉ {xᵉ = xᵉ})) ＝ᵉ reflᵉ
ap-reflᵉ fᵉ xᵉ = reflᵉ
```

### The action on identifications of any map preserves concatenation of identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  ap-concatᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) → apᵉ fᵉ (pᵉ ∙ᵉ qᵉ) ＝ᵉ apᵉ fᵉ pᵉ ∙ᵉ apᵉ fᵉ qᵉ
  ap-concatᵉ reflᵉ qᵉ = reflᵉ

  compute-right-refl-ap-concatᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
    ap-concatᵉ pᵉ reflᵉ ＝ᵉ apᵉ (apᵉ fᵉ) right-unitᵉ ∙ᵉ invᵉ right-unitᵉ
  compute-right-refl-ap-concatᵉ reflᵉ = reflᵉ
```

### The action on identifications of any map preserves inverses

```agda
ap-invᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) {xᵉ yᵉ : Aᵉ}
  (pᵉ : xᵉ ＝ᵉ yᵉ) → apᵉ fᵉ (invᵉ pᵉ) ＝ᵉ invᵉ (apᵉ fᵉ pᵉ)
ap-invᵉ fᵉ reflᵉ = reflᵉ
```

### The action on identifications of a constant map is constant

```agda
ap-constᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (bᵉ : Bᵉ) {xᵉ yᵉ : Aᵉ}
  (pᵉ : xᵉ ＝ᵉ yᵉ) → (apᵉ (constᵉ Aᵉ bᵉ) pᵉ) ＝ᵉ reflᵉ
ap-constᵉ bᵉ reflᵉ = reflᵉ
```

## See also

-ᵉ [Actionᵉ ofᵉ functionsᵉ onᵉ higherᵉ identifications](foundation.action-on-higher-identifications-functions.md).ᵉ
-ᵉ [Actionᵉ ofᵉ binaryᵉ functionsᵉ onᵉ identifications](foundation.action-on-identifications-binary-functions.md).ᵉ
-ᵉ [Actionᵉ ofᵉ dependentᵉ functionsᵉ onᵉ identifications](foundation.action-on-identifications-dependent-functions.md).ᵉ