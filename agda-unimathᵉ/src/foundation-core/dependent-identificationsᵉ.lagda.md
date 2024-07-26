# Dependent identifications

```agda
module foundation-core.dependent-identificationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Considerᵉ aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`,ᵉ anᵉ
[identification](foundation-core.identity-types.mdᵉ) `pᵉ : xᵉ ＝ᵉ y`ᵉ in `A`,ᵉ andᵉ twoᵉ
elementsᵉ `uᵉ : Bᵉ x`ᵉ andᵉ `vᵉ : Bᵉ y`.ᵉ Aᵉ **pathᵉ over**ᵉ `p`ᵉ fromᵉ `u`ᵉ to `v`ᵉ isᵉ anᵉ
identificationᵉ

```text
  trᵉ Bᵉ pᵉ uᵉ ＝ᵉ v,ᵉ
```

where `tr`ᵉ isᵉ theᵉ
[transport](foundation-core.transport-along-identifications.mdᵉ) function.ᵉ
Dependentᵉ identificationsᵉ alsoᵉ satisfyᵉ groupoidᵉ laws,ᵉ whichᵉ areᵉ formulatedᵉ
appropriatelyᵉ asᵉ dependentᵉ identifications.ᵉ Theᵉ groupoidᵉ lawsᵉ forᵉ dependentᵉ
identificationsᵉ areᵉ provenᵉ in
[`foundation.dependent-identifications`](foundation.dependent-identifications.md).ᵉ

## Definition

### Dependent identifications

```agda
dependent-identificationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) {xᵉ x'ᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ x'ᵉ) →
  Bᵉ xᵉ → Bᵉ x'ᵉ → UUᵉ l2ᵉ
dependent-identificationᵉ Bᵉ pᵉ uᵉ vᵉ = (trᵉ Bᵉ pᵉ uᵉ ＝ᵉ vᵉ)

refl-dependent-identificationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) {xᵉ : Aᵉ} {yᵉ : Bᵉ xᵉ} →
  dependent-identificationᵉ Bᵉ reflᵉ yᵉ yᵉ
refl-dependent-identificationᵉ Bᵉ = reflᵉ
```

### Iterated dependent identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  dependent-identification²ᵉ :
    {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ qᵉ)
    {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ}
    (p'ᵉ : dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ)
    (q'ᵉ : dependent-identificationᵉ Bᵉ qᵉ x'ᵉ y'ᵉ) →
    UUᵉ l2ᵉ
  dependent-identification²ᵉ αᵉ {x'ᵉ} {y'ᵉ} p'ᵉ q'ᵉ =
    dependent-identificationᵉ (λ tᵉ → dependent-identificationᵉ Bᵉ tᵉ x'ᵉ y'ᵉ) αᵉ p'ᵉ q'ᵉ
```