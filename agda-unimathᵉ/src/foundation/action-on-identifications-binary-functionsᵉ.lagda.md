# The binary action on identifications of binary functions

```agda
module foundation.action-on-identifications-binary-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ binaryᵉ operationᵉ `fᵉ : Aᵉ → Bᵉ → C`ᵉ andᵉ
[identifications](foundation-core.identity-types.mdᵉ) `pᵉ : xᵉ ＝ᵉ x'`ᵉ in `A`ᵉ andᵉ
`qᵉ : yᵉ ＝ᵉ y'`ᵉ in `B`,ᵉ weᵉ obtainᵉ anᵉ identificationᵉ

```text
  ap-binaryᵉ fᵉ pᵉ qᵉ : fᵉ xᵉ yᵉ ＝ᵉ fᵉ x'ᵉ y'ᵉ
```

weᵉ callᵉ thisᵉ theᵉ
{{#conceptᵉ "binaryᵉ actionᵉ onᵉ identificationsᵉ ofᵉ binaryᵉ functions"ᵉ Agda=ap-binary}}.ᵉ

Thereᵉ areᵉ aᵉ fewᵉ differentᵉ waysᵉ weᵉ canᵉ defineᵉ `ap-binary`.ᵉ Weᵉ couldᵉ defineᵉ itᵉ byᵉ
pattern matchingᵉ onᵉ bothᵉ `p`ᵉ andᵉ `q`,ᵉ butᵉ thisᵉ leadsᵉ to restrictedᵉ computationalᵉ
behaviour.ᵉ Instead,ᵉ weᵉ defineᵉ itᵉ asᵉ theᵉ upperᵉ concatenationᵉ in theᵉ Grayᵉ
interchangerᵉ diagramᵉ

```text
                      apᵉ (rᵉ ↦ᵉ fᵉ xᵉ rᵉ) qᵉ
                 fᵉ xᵉ yᵉ ------------->ᵉ fᵉ xᵉ y'ᵉ
                   |                    |
                   |                    |
  apᵉ (rᵉ ↦ᵉ fᵉ rᵉ yᵉ) pᵉ |                    | apᵉ (rᵉ ↦ᵉ fᵉ rᵉ y'ᵉ) pᵉ
                   |                    |
                   ∨ᵉ                    ∨ᵉ
                 fᵉ x'ᵉ yᵉ ------------>ᵉ fᵉ x'ᵉ y'.ᵉ
                      apᵉ (rᵉ ↦ᵉ fᵉ x'ᵉ rᵉ) qᵉ
```

## Definition

### The binary action on identifications of binary functions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ → Cᵉ)
  where

  ap-binaryᵉ :
    {xᵉ x'ᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ x'ᵉ) {yᵉ y'ᵉ : Bᵉ} (qᵉ : yᵉ ＝ᵉ y'ᵉ) → fᵉ xᵉ yᵉ ＝ᵉ fᵉ x'ᵉ y'ᵉ
  ap-binaryᵉ {xᵉ} {x'ᵉ} pᵉ {yᵉ} {y'ᵉ} qᵉ = apᵉ (λ rᵉ → fᵉ rᵉ yᵉ) pᵉ ∙ᵉ apᵉ (fᵉ x'ᵉ) qᵉ
```

## Properties

### The binary action on identifications in terms of the unary action on identifications

Theᵉ binaryᵉ actionᵉ onᵉ identificationsᵉ computesᵉ asᵉ aᵉ concatenationᵉ ofᵉ applicationsᵉ
ofᵉ theᵉ
[unaryᵉ actionᵉ onᵉ identificationsᵉ ofᵉ functions](foundation.action-on-identifications-functions.mdᵉ):

```text
  ap-binaryᵉ fᵉ pᵉ qᵉ ＝ᵉ apᵉ (rᵉ ↦ᵉ fᵉ rᵉ yᵉ) pᵉ ∙ᵉ apᵉ (rᵉ ↦ᵉ fᵉ x'ᵉ rᵉ) qᵉ
```

andᵉ

```text
  ap-binaryᵉ fᵉ pᵉ qᵉ ＝ᵉ apᵉ (rᵉ ↦ᵉ fᵉ xᵉ rᵉ) qᵉ ∙ᵉ apᵉ (rᵉ ↦ᵉ fᵉ rᵉ y'ᵉ) p.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ → Cᵉ)
  where

  triangle-ap-binaryᵉ :
    {xᵉ x'ᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ x'ᵉ) {yᵉ y'ᵉ : Bᵉ} (qᵉ : yᵉ ＝ᵉ y'ᵉ) →
    ap-binaryᵉ fᵉ pᵉ qᵉ ＝ᵉ apᵉ (λ rᵉ → fᵉ rᵉ yᵉ) pᵉ ∙ᵉ apᵉ (fᵉ x'ᵉ) qᵉ
  triangle-ap-binaryᵉ _ _ = reflᵉ

  triangle-ap-binary'ᵉ :
    {xᵉ x'ᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ x'ᵉ) {yᵉ y'ᵉ : Bᵉ} (qᵉ : yᵉ ＝ᵉ y'ᵉ) →
    ap-binaryᵉ fᵉ pᵉ qᵉ ＝ᵉ apᵉ (fᵉ xᵉ) qᵉ ∙ᵉ apᵉ (λ rᵉ → fᵉ rᵉ y'ᵉ) pᵉ
  triangle-ap-binary'ᵉ reflᵉ reflᵉ = reflᵉ
```

### The unit laws for the binary action on identifications of binary functions

Theᵉ binaryᵉ actionᵉ onᵉ identificationsᵉ ofᵉ binaryᵉ functionsᵉ evaluatedᵉ atᵉ aᵉ
reflexivityᵉ computesᵉ asᵉ anᵉ instance ofᵉ unaryᵉ actionᵉ onᵉ identificationsᵉ ofᵉ
(unaryᵉ) functions.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ → Cᵉ)
  where

  left-unit-ap-binaryᵉ :
    {xᵉ : Aᵉ} {yᵉ y'ᵉ : Bᵉ} (qᵉ : yᵉ ＝ᵉ y'ᵉ) → ap-binaryᵉ fᵉ reflᵉ qᵉ ＝ᵉ apᵉ (fᵉ xᵉ) qᵉ
  left-unit-ap-binaryᵉ _ = reflᵉ

  right-unit-ap-binaryᵉ :
    {xᵉ x'ᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ x'ᵉ) {yᵉ : Bᵉ} → ap-binaryᵉ fᵉ pᵉ reflᵉ ＝ᵉ apᵉ (λ rᵉ → fᵉ rᵉ yᵉ) pᵉ
  right-unit-ap-binaryᵉ reflᵉ = reflᵉ
```

### The binary action on identifications evaluated on the diagonal

Theᵉ binaryᵉ actionᵉ onᵉ identificationsᵉ evaluatedᵉ onᵉ theᵉ diagonalᵉ computesᵉ asᵉ anᵉ
instance ofᵉ unaryᵉ actionᵉ onᵉ identifications.ᵉ Specifically,ᵉ weᵉ haveᵉ theᵉ followingᵉ
uncurriedᵉ [commutingᵉ square](foundation-core.commuting-squares-of-maps.mdᵉ)

```text
                           (-ᵉ ∘ᵉ Δᵉ) ×ᵉ 1
       (Aᵉ ×ᵉ Aᵉ → Bᵉ) ×ᵉ Pathᵉ Aᵉ -------->ᵉ (Aᵉ → Bᵉ) ×ᵉ Pathᵉ Aᵉ
                |                             |
                |                             |
          1 ×ᵉ Δᵉ |                             | apᵉ
                |                             |
                ∨ᵉ                             ∨ᵉ
  (Aᵉ ×ᵉ Aᵉ → Bᵉ) ×ᵉ Pathᵉ Aᵉ ×ᵉ Pathᵉ Aᵉ ---------->ᵉ Pathᵉ B.ᵉ
                                 ap-binaryᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Aᵉ → Bᵉ)
  where

  ap-binary-diagonalᵉ :
    {xᵉ x'ᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ x'ᵉ) → ap-binaryᵉ fᵉ pᵉ pᵉ ＝ᵉ apᵉ (λ rᵉ → fᵉ rᵉ rᵉ) pᵉ
  ap-binary-diagonalᵉ reflᵉ = reflᵉ
```

### The binary action on identifications distributes over identification concatenation

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ → Cᵉ)
  where

  ap-binary-concatᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (p'ᵉ : yᵉ ＝ᵉ zᵉ)
    {x'ᵉ y'ᵉ z'ᵉ : Bᵉ} (qᵉ : x'ᵉ ＝ᵉ y'ᵉ) (q'ᵉ : y'ᵉ ＝ᵉ z'ᵉ) →
    ap-binaryᵉ fᵉ (pᵉ ∙ᵉ p'ᵉ) (qᵉ ∙ᵉ q'ᵉ) ＝ᵉ ap-binaryᵉ fᵉ pᵉ qᵉ ∙ᵉ ap-binaryᵉ fᵉ p'ᵉ q'ᵉ
  ap-binary-concatᵉ reflᵉ _ reflᵉ _ = reflᵉ
```

### The binary action on identifications distributes over function composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (Hᵉ : Aᵉ → Bᵉ → Cᵉ)
  where

  ap-binary-compᵉ :
    {l4ᵉ l5ᵉ : Level} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} (fᵉ : Xᵉ → Aᵉ) (gᵉ : Yᵉ → Bᵉ)
    {xᵉ x'ᵉ : Xᵉ} (pᵉ : xᵉ ＝ᵉ x'ᵉ) {yᵉ y'ᵉ : Yᵉ} (qᵉ : yᵉ ＝ᵉ y'ᵉ) →
    ap-binaryᵉ (λ xᵉ yᵉ → Hᵉ (fᵉ xᵉ) (gᵉ yᵉ)) pᵉ qᵉ ＝ᵉ ap-binaryᵉ Hᵉ (apᵉ fᵉ pᵉ) (apᵉ gᵉ qᵉ)
  ap-binary-compᵉ fᵉ gᵉ reflᵉ reflᵉ = reflᵉ

  ap-binary-comp-diagonalᵉ :
    {l4ᵉ : Level} {A'ᵉ : UUᵉ l4ᵉ} (fᵉ : A'ᵉ → Aᵉ) (gᵉ : A'ᵉ → Bᵉ)
    {xᵉ yᵉ : A'ᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
    apᵉ (λ zᵉ → Hᵉ (fᵉ zᵉ) (gᵉ zᵉ)) pᵉ ＝ᵉ ap-binaryᵉ Hᵉ (apᵉ fᵉ pᵉ) (apᵉ gᵉ pᵉ)
  ap-binary-comp-diagonalᵉ fᵉ gᵉ pᵉ =
    ( invᵉ (ap-binary-diagonalᵉ (λ xᵉ yᵉ → Hᵉ (fᵉ xᵉ) (gᵉ yᵉ)) pᵉ)) ∙ᵉ
    ( ap-binary-compᵉ fᵉ gᵉ pᵉ pᵉ)

  ap-binary-comp'ᵉ :
    {l4ᵉ : Level} {Dᵉ : UUᵉ l4ᵉ} (fᵉ : Cᵉ → Dᵉ)
    {xᵉ x'ᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ x'ᵉ) {yᵉ y'ᵉ : Bᵉ} (qᵉ : yᵉ ＝ᵉ y'ᵉ) →
    ap-binaryᵉ (λ aᵉ bᵉ → fᵉ (Hᵉ aᵉ bᵉ)) pᵉ qᵉ ＝ᵉ apᵉ fᵉ (ap-binaryᵉ Hᵉ pᵉ qᵉ)
  ap-binary-comp'ᵉ fᵉ reflᵉ reflᵉ = reflᵉ
```

### Computing the binary action on identifications when swapping argument order

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ → Cᵉ)
  where

  ap-binary-permuteᵉ :
    {xᵉ x'ᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ x'ᵉ) {yᵉ y'ᵉ : Bᵉ} (qᵉ : yᵉ ＝ᵉ y'ᵉ) →
    ap-binaryᵉ (λ yᵉ xᵉ → fᵉ xᵉ yᵉ) qᵉ pᵉ ＝ᵉ ap-binaryᵉ fᵉ pᵉ qᵉ
  ap-binary-permuteᵉ reflᵉ reflᵉ = reflᵉ
```

## See also

-ᵉ [Actionᵉ ofᵉ functionsᵉ onᵉ identifications](foundation.action-on-identifications-functions.mdᵉ)
-ᵉ [Actionᵉ ofᵉ functionsᵉ onᵉ higherᵉ identifications](foundation.action-on-higher-identifications-functions.md).ᵉ
-ᵉ [Actionᵉ ofᵉ dependentᵉ functionsᵉ onᵉ identifications](foundation.action-on-identifications-dependent-functions.md).ᵉ