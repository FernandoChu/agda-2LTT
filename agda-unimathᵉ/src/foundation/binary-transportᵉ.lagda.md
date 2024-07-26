# Binary transport

```agda
module foundation.binary-transportᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Givenᵉ aᵉ binaryᵉ relationᵉ `Bᵉ : Aᵉ → Aᵉ → UU`ᵉ andᵉ identificationsᵉ `pᵉ : xᵉ ＝ᵉ x'`ᵉ andᵉ
`qᵉ : yᵉ ＝ᵉ y'`ᵉ in `A`,ᵉ theᵉ binaryᵉ transportᵉ ofᵉ `B`ᵉ isᵉ anᵉ operationᵉ

```text
  binary-trᵉ Bᵉ pᵉ qᵉ : Bᵉ xᵉ yᵉ → Bᵉ x'ᵉ y'ᵉ
```

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (Cᵉ : Aᵉ → Bᵉ → UUᵉ l3ᵉ)
  {xᵉ x'ᵉ : Aᵉ} {yᵉ y'ᵉ : Bᵉ}
  where

  binary-trᵉ : (pᵉ : xᵉ ＝ᵉ x'ᵉ) (qᵉ : yᵉ ＝ᵉ y'ᵉ) → Cᵉ xᵉ yᵉ → Cᵉ x'ᵉ y'ᵉ
  binary-trᵉ reflᵉ reflᵉ = idᵉ

  is-equiv-binary-trᵉ : (pᵉ : xᵉ ＝ᵉ x'ᵉ) (qᵉ : yᵉ ＝ᵉ y'ᵉ) → is-equivᵉ (binary-trᵉ pᵉ qᵉ)
  is-equiv-binary-trᵉ reflᵉ reflᵉ = is-equiv-idᵉ

  equiv-binary-trᵉ : (pᵉ : xᵉ ＝ᵉ x'ᵉ) (qᵉ : yᵉ ＝ᵉ y'ᵉ) → Cᵉ xᵉ yᵉ ≃ᵉ Cᵉ x'ᵉ y'ᵉ
  pr1ᵉ (equiv-binary-trᵉ pᵉ qᵉ) = binary-trᵉ pᵉ qᵉ
  pr2ᵉ (equiv-binary-trᵉ pᵉ qᵉ) = is-equiv-binary-trᵉ pᵉ qᵉ

  compute-binary-trᵉ :
    (pᵉ : xᵉ ＝ᵉ x'ᵉ) (qᵉ : yᵉ ＝ᵉ y'ᵉ) (uᵉ : Cᵉ xᵉ yᵉ) →
    trᵉ (λ aᵉ → Cᵉ aᵉ y'ᵉ) pᵉ (trᵉ (Cᵉ xᵉ) qᵉ uᵉ) ＝ᵉ binary-trᵉ pᵉ qᵉ uᵉ
  compute-binary-trᵉ reflᵉ reflᵉ uᵉ = reflᵉ

  compute-binary-tr'ᵉ :
    (pᵉ : xᵉ ＝ᵉ x'ᵉ) (qᵉ : yᵉ ＝ᵉ y'ᵉ) (uᵉ : Cᵉ xᵉ yᵉ) →
    trᵉ (Cᵉ x'ᵉ) qᵉ (trᵉ (λ aᵉ → Cᵉ aᵉ yᵉ) pᵉ uᵉ) ＝ᵉ binary-trᵉ pᵉ qᵉ uᵉ
  compute-binary-tr'ᵉ reflᵉ reflᵉ uᵉ = reflᵉ
```

## Properties

### Transposing binary path-overs

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (Cᵉ : Aᵉ → Bᵉ → UUᵉ l3ᵉ)
  where

  transpose-binary-path-overᵉ :
    {x1ᵉ x2ᵉ : Aᵉ} (pᵉ : x1ᵉ ＝ᵉ x2ᵉ) {y1ᵉ y2ᵉ : Bᵉ} (qᵉ : y1ᵉ ＝ᵉ y2ᵉ)
    {c1ᵉ : Cᵉ x1ᵉ y1ᵉ} {c2ᵉ : Cᵉ x2ᵉ y2ᵉ} →
    c2ᵉ ＝ᵉ binary-trᵉ Cᵉ pᵉ qᵉ c1ᵉ → binary-trᵉ Cᵉ (invᵉ pᵉ) (invᵉ qᵉ) c2ᵉ ＝ᵉ c1ᵉ
  transpose-binary-path-overᵉ reflᵉ reflᵉ = idᵉ

  transpose-binary-path-over'ᵉ :
    {x1ᵉ x2ᵉ : Aᵉ} (pᵉ : x1ᵉ ＝ᵉ x2ᵉ) {y1ᵉ y2ᵉ : Bᵉ} (qᵉ : y1ᵉ ＝ᵉ y2ᵉ)
    {c1ᵉ : Cᵉ x1ᵉ y1ᵉ} {c2ᵉ : Cᵉ x2ᵉ y2ᵉ} →
    c1ᵉ ＝ᵉ binary-trᵉ Cᵉ (invᵉ pᵉ) (invᵉ qᵉ) c2ᵉ → binary-trᵉ Cᵉ pᵉ qᵉ c1ᵉ ＝ᵉ c2ᵉ
  transpose-binary-path-over'ᵉ reflᵉ reflᵉ = idᵉ
```

### Binary transport along concatenated paths

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (Cᵉ : Aᵉ → Bᵉ → UUᵉ l3ᵉ)
  where

  binary-tr-concatᵉ :
    {x1ᵉ x2ᵉ x3ᵉ : Aᵉ} (pᵉ : x1ᵉ ＝ᵉ x2ᵉ) (p'ᵉ : x2ᵉ ＝ᵉ x3ᵉ)
    {y1ᵉ y2ᵉ y3ᵉ : Bᵉ} (qᵉ : y1ᵉ ＝ᵉ y2ᵉ) (q'ᵉ : y2ᵉ ＝ᵉ y3ᵉ) →
    (cᵉ : Cᵉ x1ᵉ y1ᵉ) →
    binary-trᵉ Cᵉ (pᵉ ∙ᵉ p'ᵉ) (qᵉ ∙ᵉ q'ᵉ) cᵉ ＝ᵉ
    binary-trᵉ Cᵉ p'ᵉ q'ᵉ (binary-trᵉ Cᵉ pᵉ qᵉ cᵉ)
  binary-tr-concatᵉ reflᵉ reflᵉ reflᵉ reflᵉ cᵉ = reflᵉ
```

### Binary transport along paths of the form `ap f p` and `ap g q`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  {Eᵉ : Aᵉ → Cᵉ → UUᵉ l5ᵉ} (Fᵉ : Bᵉ → Dᵉ → UUᵉ l6ᵉ)
  {fᵉ : Aᵉ → Bᵉ} {gᵉ : Cᵉ → Dᵉ} (hᵉ : (aᵉ : Aᵉ) (cᵉ : Cᵉ) → Eᵉ aᵉ cᵉ → Fᵉ (fᵉ aᵉ) (gᵉ cᵉ))
  where

  binary-tr-apᵉ :
    {xᵉ x'ᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ x'ᵉ) {yᵉ y'ᵉ : Cᵉ} (qᵉ : yᵉ ＝ᵉ y'ᵉ) →
    {uᵉ : Eᵉ xᵉ yᵉ} {vᵉ : Eᵉ x'ᵉ y'ᵉ} (rᵉ : binary-trᵉ Eᵉ pᵉ qᵉ uᵉ ＝ᵉ vᵉ) →
    binary-trᵉ Fᵉ (apᵉ fᵉ pᵉ) (apᵉ gᵉ qᵉ) (hᵉ xᵉ yᵉ uᵉ) ＝ᵉ hᵉ x'ᵉ y'ᵉ vᵉ
  binary-tr-apᵉ reflᵉ reflᵉ reflᵉ = reflᵉ
```