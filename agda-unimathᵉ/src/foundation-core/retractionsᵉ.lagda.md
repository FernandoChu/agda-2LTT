# Retractions

```agda
module foundation-core.retractionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Aᵉ **retraction**ᵉ ofᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ consistsᵉ ofᵉ aᵉ mapᵉ `rᵉ : Bᵉ → A`ᵉ equippedᵉ
with aᵉ [homotopy](foundation-core.homotopies.mdᵉ) `rᵉ ∘ᵉ fᵉ ~ᵉ id`.ᵉ Inᵉ otherᵉ words,ᵉ aᵉ
retractionᵉ ofᵉ aᵉ mapᵉ `f`ᵉ isᵉ aᵉ leftᵉ inverseᵉ ofᵉ `f`.ᵉ

## Definitions

### The type of retractions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-retractionᵉ : (fᵉ : Aᵉ → Bᵉ) (gᵉ : Bᵉ → Aᵉ) → UUᵉ l1ᵉ
  is-retractionᵉ fᵉ gᵉ = gᵉ ∘ᵉ fᵉ ~ᵉ idᵉ

  retractionᵉ : (fᵉ : Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  retractionᵉ fᵉ = Σᵉ (Bᵉ → Aᵉ) (is-retractionᵉ fᵉ)

  map-retractionᵉ : (fᵉ : Aᵉ → Bᵉ) → retractionᵉ fᵉ → Bᵉ → Aᵉ
  map-retractionᵉ fᵉ = pr1ᵉ

  is-retraction-map-retractionᵉ :
    (fᵉ : Aᵉ → Bᵉ) (rᵉ : retractionᵉ fᵉ) → map-retractionᵉ fᵉ rᵉ ∘ᵉ fᵉ ~ᵉ idᵉ
  is-retraction-map-retractionᵉ fᵉ = pr2ᵉ
```

## Properties

### For any map `i : A → B`, a retraction of `i` induces a retraction of the action on identifications of `i`

**Proof:**ᵉ Supposeᵉ thatᵉ `Hᵉ : rᵉ ∘ᵉ iᵉ ~ᵉ id`ᵉ andᵉ `pᵉ : iᵉ xᵉ ＝ᵉ iᵉ y`ᵉ isᵉ anᵉ
identificationᵉ in `B`.ᵉ Thenᵉ weᵉ getᵉ theᵉ identificationᵉ

```text
     (Hᵉ x)⁻¹ᵉ           apᵉ rᵉ pᵉ           Hᵉ yᵉ
  xᵉ =========ᵉ rᵉ (iᵉ xᵉ) ========ᵉ rᵉ (iᵉ yᵉ) =====ᵉ yᵉ
```

Thisᵉ definesᵉ aᵉ mapᵉ `sᵉ : (iᵉ xᵉ ＝ᵉ iᵉ yᵉ) → xᵉ ＝ᵉ y`.ᵉ Toᵉ seeᵉ thatᵉ `sᵉ ∘ᵉ apᵉ iᵉ ~ᵉ id`,ᵉ
i.e.,ᵉ thatᵉ theᵉ concatenationᵉ

```text
     (Hᵉ x)⁻¹ᵉ           apᵉ rᵉ (apᵉ iᵉ pᵉ)           Hᵉ yᵉ
  xᵉ =========ᵉ rᵉ (iᵉ xᵉ) ===============ᵉ rᵉ (iᵉ yᵉ) =====ᵉ yᵉ
```

isᵉ identicalᵉ to `pᵉ : xᵉ ＝ᵉ y`ᵉ forᵉ allᵉ `pᵉ : xᵉ ＝ᵉ y`,ᵉ weᵉ proceedᵉ byᵉ identificationᵉ
elimination.ᵉ Thenᵉ itᵉ sufficesᵉ to showᵉ thatᵉ `(Hᵉ x)⁻¹ᵉ ∙ᵉ (Hᵉ x)`ᵉ isᵉ identicalᵉ to
`refl`,ᵉ whichᵉ isᵉ indeedᵉ theᵉ caseᵉ byᵉ theᵉ leftᵉ inverseᵉ lawᵉ ofᵉ concatenationᵉ ofᵉ
identifications.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (iᵉ : Aᵉ → Bᵉ)
  (rᵉ : Bᵉ → Aᵉ) (Hᵉ : rᵉ ∘ᵉ iᵉ ~ᵉ idᵉ)
  where

  is-injective-has-retractionᵉ :
    {xᵉ yᵉ : Aᵉ} → iᵉ xᵉ ＝ᵉ iᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  is-injective-has-retractionᵉ {xᵉ} {yᵉ} pᵉ = invᵉ (Hᵉ xᵉ) ∙ᵉ (apᵉ rᵉ pᵉ ∙ᵉ Hᵉ yᵉ)

  is-retraction-is-injective-has-retractionᵉ :
    {xᵉ yᵉ : Aᵉ} → is-injective-has-retractionᵉ ∘ᵉ apᵉ iᵉ {xᵉ} {yᵉ} ~ᵉ idᵉ
  is-retraction-is-injective-has-retractionᵉ {xᵉ} reflᵉ = left-invᵉ (Hᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (iᵉ : Aᵉ → Bᵉ) (Rᵉ : retractionᵉ iᵉ)
  where

  is-injective-retractionᵉ :
    {xᵉ yᵉ : Aᵉ} → iᵉ xᵉ ＝ᵉ iᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  is-injective-retractionᵉ =
    is-injective-has-retractionᵉ iᵉ
      ( map-retractionᵉ iᵉ Rᵉ)
      ( is-retraction-map-retractionᵉ iᵉ Rᵉ)

  is-retraction-is-injective-retractionᵉ :
    {xᵉ yᵉ : Aᵉ} → is-injective-retractionᵉ ∘ᵉ apᵉ iᵉ {xᵉ} {yᵉ} ~ᵉ idᵉ
  is-retraction-is-injective-retractionᵉ =
    is-retraction-is-injective-has-retractionᵉ iᵉ
      ( map-retractionᵉ iᵉ Rᵉ)
      ( is-retraction-map-retractionᵉ iᵉ Rᵉ)

  retraction-apᵉ : {xᵉ yᵉ : Aᵉ} → retractionᵉ (apᵉ iᵉ {xᵉ} {yᵉ})
  pr1ᵉ retraction-apᵉ = is-injective-retractionᵉ
  pr2ᵉ retraction-apᵉ = is-retraction-is-injective-retractionᵉ
```

### Composites of retractions are retractions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (rᵉ : retractionᵉ gᵉ) (sᵉ : retractionᵉ hᵉ)
  where

  map-retraction-compᵉ : Xᵉ → Aᵉ
  map-retraction-compᵉ = map-retractionᵉ hᵉ sᵉ ∘ᵉ map-retractionᵉ gᵉ rᵉ

  is-retraction-map-retraction-compᵉ : is-retractionᵉ (gᵉ ∘ᵉ hᵉ) map-retraction-compᵉ
  is-retraction-map-retraction-compᵉ =
    ( map-retractionᵉ hᵉ sᵉ ·lᵉ (is-retraction-map-retractionᵉ gᵉ rᵉ ·rᵉ hᵉ)) ∙hᵉ
    ( is-retraction-map-retractionᵉ hᵉ sᵉ)

  retraction-compᵉ : retractionᵉ (gᵉ ∘ᵉ hᵉ)
  pr1ᵉ retraction-compᵉ = map-retraction-compᵉ
  pr2ᵉ retraction-compᵉ = is-retraction-map-retraction-compᵉ
```

### If `g ∘ f` has a retraction then `f` has a retraction

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (rᵉ : retractionᵉ (gᵉ ∘ᵉ hᵉ))
  where

  map-retraction-right-factorᵉ : Bᵉ → Aᵉ
  map-retraction-right-factorᵉ = map-retractionᵉ (gᵉ ∘ᵉ hᵉ) rᵉ ∘ᵉ gᵉ

  is-retraction-map-retraction-right-factorᵉ :
    is-retractionᵉ hᵉ map-retraction-right-factorᵉ
  is-retraction-map-retraction-right-factorᵉ =
    is-retraction-map-retractionᵉ (gᵉ ∘ᵉ hᵉ) rᵉ

  retraction-right-factorᵉ : retractionᵉ hᵉ
  pr1ᵉ retraction-right-factorᵉ = map-retraction-right-factorᵉ
  pr2ᵉ retraction-right-factorᵉ = is-retraction-map-retraction-right-factorᵉ
```

### In a commuting triangle `f ~ g ∘ h`, any retraction of the left map `f` induces a retraction of the top map `h`

Inᵉ aᵉ commutingᵉ triangleᵉ ofᵉ theᵉ formᵉ

```text
       hᵉ
  Aᵉ ------>ᵉ Bᵉ
   \ᵉ       /ᵉ
   f\ᵉ     /gᵉ
     \ᵉ   /ᵉ
      ∨ᵉ ∨ᵉ
       X,ᵉ
```

ifᵉ `rᵉ : Xᵉ → A`ᵉ isᵉ aᵉ retractionᵉ ofᵉ theᵉ mapᵉ `f`ᵉ onᵉ theᵉ left,ᵉ thenᵉ `rᵉ ∘ᵉ g`ᵉ isᵉ aᵉ
retractionᵉ ofᵉ theᵉ topᵉ mapᵉ `h`.ᵉ

Noteᵉ: Inᵉ thisᵉ fileᵉ weᵉ areᵉ unableᵉ to useᵉ theᵉ definitionᵉ ofᵉ
[commutingᵉ triangles](foundation-core.commuting-triangles-of-maps.md),ᵉ becauseᵉ
thatᵉ wouldᵉ resultᵉ in aᵉ cyclicᵉ module dependency.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ ∘ᵉ hᵉ)
  (rᵉ : retractionᵉ fᵉ)
  where

  map-retraction-top-map-triangleᵉ : Bᵉ → Aᵉ
  map-retraction-top-map-triangleᵉ = map-retractionᵉ fᵉ rᵉ ∘ᵉ gᵉ

  is-retraction-map-retraction-top-map-triangleᵉ :
    is-retractionᵉ hᵉ map-retraction-top-map-triangleᵉ
  is-retraction-map-retraction-top-map-triangleᵉ =
    ( inv-htpyᵉ (map-retractionᵉ fᵉ rᵉ ·lᵉ Hᵉ)) ∙hᵉ
    ( is-retraction-map-retractionᵉ fᵉ rᵉ)

  retraction-top-map-triangleᵉ : retractionᵉ hᵉ
  pr1ᵉ retraction-top-map-triangleᵉ =
    map-retraction-top-map-triangleᵉ
  pr2ᵉ retraction-top-map-triangleᵉ =
    is-retraction-map-retraction-top-map-triangleᵉ
```

### In a commuting triangle `f ~ g ∘ h`, retractions of `g` and `h` compose to a retraction of `f`

Inᵉ aᵉ commutingᵉ triangleᵉ ofᵉ theᵉ formᵉ

```text
       hᵉ
  Aᵉ ------>ᵉ Bᵉ
   \ᵉ       /ᵉ
   f\ᵉ     /gᵉ
     \ᵉ   /ᵉ
      ∨ᵉ ∨ᵉ
       X,ᵉ
```

ifᵉ `rᵉ : Xᵉ → A`ᵉ isᵉ aᵉ retractionᵉ ofᵉ theᵉ mapᵉ `g`ᵉ onᵉ theᵉ rightᵉ andᵉ `sᵉ : Bᵉ → A`ᵉ isᵉ aᵉ
retractionᵉ ofᵉ theᵉ mapᵉ `h`ᵉ onᵉ top,ᵉ thenᵉ `sᵉ ∘ᵉ r`ᵉ isᵉ aᵉ retractionᵉ ofᵉ theᵉ mapᵉ `f`ᵉ onᵉ
theᵉ left.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ ∘ᵉ hᵉ)
  (rᵉ : retractionᵉ gᵉ) (sᵉ : retractionᵉ hᵉ)
  where

  map-retraction-left-map-triangleᵉ : Xᵉ → Aᵉ
  map-retraction-left-map-triangleᵉ = map-retraction-compᵉ gᵉ hᵉ rᵉ sᵉ

  is-retraction-map-retraction-left-map-triangleᵉ :
    is-retractionᵉ fᵉ map-retraction-left-map-triangleᵉ
  is-retraction-map-retraction-left-map-triangleᵉ =
    ( map-retraction-compᵉ gᵉ hᵉ rᵉ sᵉ ·lᵉ Hᵉ) ∙hᵉ
    ( is-retraction-map-retraction-compᵉ gᵉ hᵉ rᵉ sᵉ)

  retraction-left-map-triangleᵉ : retractionᵉ fᵉ
  pr1ᵉ retraction-left-map-triangleᵉ =
    map-retraction-left-map-triangleᵉ
  pr2ᵉ retraction-left-map-triangleᵉ =
    is-retraction-map-retraction-left-map-triangleᵉ
```

## See also

-ᵉ Retractsᵉ ofᵉ typesᵉ areᵉ definedᵉ in
  [`foundation-core.retracts-of-types`](foundation-core.retracts-of-types.md).ᵉ
-ᵉ Retractsᵉ ofᵉ mapsᵉ areᵉ definedᵉ in
  [`foundation.retracts-of-maps`](foundation.retracts-of-maps.md).ᵉ