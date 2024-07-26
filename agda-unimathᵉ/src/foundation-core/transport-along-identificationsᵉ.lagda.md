# Transport along identifications

```agda
module foundation-core.transport-along-identificationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`,ᵉ anᵉ
[identification](foundation-core.identity-types.mdᵉ) `pᵉ : xᵉ ＝ᵉ y`ᵉ in `A`ᵉ andᵉ anᵉ
elementᵉ `bᵉ : Bᵉ x`,ᵉ weᵉ canᵉ **transport**ᵉ theᵉ elementᵉ `b`ᵉ alongᵉ theᵉ identificationᵉ
`p`ᵉ to obtainᵉ anᵉ elementᵉ `trᵉ Bᵉ pᵉ bᵉ : Bᵉ y`.ᵉ

Theᵉ factᵉ thatᵉ `trᵉ Bᵉ p`ᵉ isᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) isᵉ
recordedᵉ in
[`foundation.transport-along-identifications`](foundation.transport-along-identifications.md).ᵉ

## Definitions

### Transport

```agda
trᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → Bᵉ xᵉ → Bᵉ yᵉ
trᵉ Bᵉ reflᵉ bᵉ = bᵉ
```

## Properties

### Transport preserves concatenation of identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  tr-concatᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) (bᵉ : Bᵉ xᵉ) →
    trᵉ Bᵉ (pᵉ ∙ᵉ qᵉ) bᵉ ＝ᵉ trᵉ Bᵉ qᵉ (trᵉ Bᵉ pᵉ bᵉ)
  tr-concatᵉ reflᵉ qᵉ bᵉ = reflᵉ
```

### Transposing transport along the inverse of an identification

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  eq-transpose-trᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {uᵉ : Bᵉ xᵉ} {vᵉ : Bᵉ yᵉ} →
    vᵉ ＝ᵉ trᵉ Bᵉ pᵉ uᵉ → trᵉ Bᵉ (invᵉ pᵉ) vᵉ ＝ᵉ uᵉ
  eq-transpose-trᵉ reflᵉ qᵉ = qᵉ

  eq-transpose-tr'ᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {uᵉ : Bᵉ xᵉ} {vᵉ : Bᵉ yᵉ} →
    trᵉ Bᵉ pᵉ uᵉ ＝ᵉ vᵉ → uᵉ ＝ᵉ trᵉ Bᵉ (invᵉ pᵉ) vᵉ
  eq-transpose-tr'ᵉ reflᵉ qᵉ = qᵉ
```

### Every family of maps preserves transport

```agda
preserves-trᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
  (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ)
  {iᵉ jᵉ : Iᵉ} (pᵉ : iᵉ ＝ᵉ jᵉ) (xᵉ : Aᵉ iᵉ) →
  fᵉ jᵉ (trᵉ Aᵉ pᵉ xᵉ) ＝ᵉ trᵉ Bᵉ pᵉ (fᵉ iᵉ xᵉ)
preserves-trᵉ fᵉ reflᵉ xᵉ = reflᵉ
```

### Transporting along the action on identifications of a function

```agda
tr-apᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : Cᵉ → UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Cᵉ) (gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Dᵉ (fᵉ xᵉ))
  {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (zᵉ : Bᵉ xᵉ) →
  trᵉ Dᵉ (apᵉ fᵉ pᵉ) (gᵉ xᵉ zᵉ) ＝ᵉ gᵉ yᵉ (trᵉ Bᵉ pᵉ zᵉ)
tr-apᵉ fᵉ gᵉ reflᵉ zᵉ = reflᵉ
```

### Computing maps out of identity types as transports

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {aᵉ : Aᵉ}
  (fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) → Bᵉ xᵉ)
  where

  compute-map-out-of-identity-typeᵉ :
    (xᵉ : Aᵉ) (pᵉ : aᵉ ＝ᵉ xᵉ) → fᵉ xᵉ pᵉ ＝ᵉ trᵉ Bᵉ pᵉ (fᵉ aᵉ reflᵉ)
  compute-map-out-of-identity-typeᵉ xᵉ reflᵉ = reflᵉ
```

### Computing transport in the type family of identifications with a fixed target

```agda
tr-Id-leftᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ cᵉ : Aᵉ} (qᵉ : bᵉ ＝ᵉ cᵉ) (pᵉ : bᵉ ＝ᵉ aᵉ) →
  trᵉ (_＝ᵉ aᵉ) qᵉ pᵉ ＝ᵉ (invᵉ qᵉ ∙ᵉ pᵉ)
tr-Id-leftᵉ reflᵉ pᵉ = reflᵉ
```

### Computing transport in the type family of identifications with a fixed source

```agda
tr-Id-rightᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ cᵉ : Aᵉ} (qᵉ : bᵉ ＝ᵉ cᵉ) (pᵉ : aᵉ ＝ᵉ bᵉ) →
  trᵉ (aᵉ ＝ᵉ_) qᵉ pᵉ ＝ᵉ (pᵉ ∙ᵉ qᵉ)
tr-Id-rightᵉ reflᵉ pᵉ = invᵉ right-unitᵉ
```

### Substitution law for transport

```agda
substitution-law-trᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (Bᵉ : Aᵉ → UUᵉ l3ᵉ) (fᵉ : Xᵉ → Aᵉ)
  {xᵉ yᵉ : Xᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {x'ᵉ : Bᵉ (fᵉ xᵉ)} →
  trᵉ Bᵉ (apᵉ fᵉ pᵉ) x'ᵉ ＝ᵉ trᵉ (Bᵉ ∘ᵉ fᵉ) pᵉ x'ᵉ
substitution-law-trᵉ Bᵉ fᵉ reflᵉ = reflᵉ
```