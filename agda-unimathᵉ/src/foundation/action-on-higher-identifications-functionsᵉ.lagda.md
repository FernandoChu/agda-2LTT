# The action of functions on higher identifications

```agda
module foundation.action-on-higher-identifications-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.path-algebraᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-squares-of-identificationsᵉ
open import foundation-core.constant-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Anyᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ hasᵉ anᵉ
{{#conceptᵉ "actionᵉ onᵉ higherᵉ identifications"ᵉ Disambiguation="functions"ᵉ Agda=ap²}},ᵉ
whichᵉ isᵉ aᵉ mapᵉ

```text
  ap²ᵉ fᵉ : (pᵉ ＝ᵉ qᵉ) → (apᵉ fᵉ pᵉ ＝ᵉ apᵉ fᵉ qᵉ)
```

Hereᵉ `pᵉ qᵉ : xᵉ ＝ᵉ y`ᵉ areᵉ [identifications](foundation-core.identity-types.mdᵉ) in
theᵉ typeᵉ `A`.ᵉ Theᵉ actionᵉ ofᵉ `f`ᵉ onᵉ higherᵉ identificationsᵉ isᵉ definedᵉ byᵉ

```text
  ap²ᵉ fᵉ :=ᵉ apᵉ (apᵉ f).ᵉ
```

## Definitions

### The action of functions on higher identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {xᵉ yᵉ : Aᵉ}
  {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (fᵉ : Aᵉ → Bᵉ) (αᵉ : pᵉ ＝ᵉ qᵉ)
  where

  ap²ᵉ : apᵉ fᵉ pᵉ ＝ᵉ apᵉ fᵉ qᵉ
  ap²ᵉ = apᵉ (apᵉ fᵉ) αᵉ
```

## Properties

### The inverse law of the action of functions on higher identifications

Considerᵉ anᵉ identificationᵉ `αᵉ : pᵉ ＝ᵉ q`ᵉ betweenᵉ twoᵉ identificationsᵉ
`pᵉ qᵉ : xᵉ ＝ᵉ y`ᵉ in aᵉ typeᵉ `A`,ᵉ andᵉ considerᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`.ᵉ Thenᵉ theᵉ squareᵉ ofᵉ
identificationsᵉ

```text
                      ap²ᵉ fᵉ (horizontal-inv-Id²ᵉ αᵉ)
        apᵉ fᵉ (invᵉ pᵉ) ------------------------------>ᵉ apᵉ fᵉ (invᵉ qᵉ)
             |                                            |
  ap-invᵉ fᵉ pᵉ |                                            | ap-invᵉ fᵉ qᵉ
             ∨ᵉ                                            ∨ᵉ
        invᵉ (apᵉ fᵉ pᵉ) ------------------------------>ᵉ invᵉ (apᵉ fᵉ qᵉ)
                      horizontal-inv-Id²ᵉ (ap²ᵉ fᵉ αᵉ)
```

[commutes](foundation.commuting-squares-of-identifications.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {xᵉ yᵉ : Aᵉ}
  {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (fᵉ : Aᵉ → Bᵉ) (αᵉ : pᵉ ＝ᵉ qᵉ)
  where

  compute-inv-ap²ᵉ :
    coherence-square-identificationsᵉ
      ( ap²ᵉ fᵉ (horizontal-inv-Id²ᵉ αᵉ))
      ( ap-invᵉ fᵉ pᵉ)
      ( ap-invᵉ fᵉ qᵉ)
      ( horizontal-inv-Id²ᵉ (ap²ᵉ fᵉ αᵉ))
  compute-inv-ap²ᵉ =
    ( ( invᵉ (horizontal-concat-Id²ᵉ reflᵉ (ap-compᵉ invᵉ (apᵉ fᵉ) αᵉ))) ∙ᵉ
      ( nat-htpyᵉ (ap-invᵉ fᵉ) αᵉ)) ∙ᵉ
    ( horizontal-concat-Id²ᵉ (ap-compᵉ (apᵉ fᵉ) invᵉ αᵉ) reflᵉ)
```

### The action of the identity function on higher identifications is trivial

Considerᵉ anᵉ identificationᵉ `αᵉ : pᵉ ＝ᵉ q`ᵉ betweenᵉ twoᵉ identificationsᵉ
`pᵉ qᵉ : xᵉ ＝ᵉ y`ᵉ in aᵉ typeᵉ `A`.ᵉ Thenᵉ theᵉ squareᵉ ofᵉ identificationsᵉ

```text
                ap²ᵉ idᵉ αᵉ
       apᵉ idᵉ pᵉ ---------->ᵉ apᵉ idᵉ qᵉ
          |                    |
  ap-idᵉ pᵉ |                    | ap-idᵉ qᵉ
          ∨ᵉ                    ∨ᵉ
          pᵉ ----------------->ᵉ qᵉ
                     αᵉ
```

commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {xᵉ yᵉ : Aᵉ}
  {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ qᵉ)
  where

  compute-id-ap²ᵉ :
    coherence-square-identificationsᵉ (ap²ᵉ idᵉ αᵉ) (ap-idᵉ pᵉ) (ap-idᵉ qᵉ) αᵉ
  compute-id-ap²ᵉ =
    horizontal-concat-Id²ᵉ reflᵉ (invᵉ (ap-idᵉ αᵉ)) ∙ᵉ nat-htpyᵉ ap-idᵉ αᵉ
```

### The action of a composite function on higher identifications

Considerᵉ anᵉ identificationᵉ `αᵉ : pᵉ ＝ᵉ q`ᵉ betweenᵉ twoᵉ identificationsᵉ
`pᵉ qᵉ : xᵉ ＝ᵉ y`ᵉ in aᵉ typeᵉ `A`ᵉ andᵉ considerᵉ twoᵉ functionsᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ
`gᵉ : Bᵉ → C`.ᵉ Thenᵉ theᵉ squareᵉ ofᵉ identificationsᵉ

```text
                         ap²ᵉ (gᵉ ∘ᵉ fᵉ) αᵉ
          apᵉ (gᵉ ∘ᵉ fᵉ) pᵉ ----------------->ᵉ apᵉ (gᵉ ∘ᵉ fᵉ) qᵉ
                |                               |
  ap-compᵉ gᵉ fᵉ pᵉ |                               | ap-compᵉ gᵉ fᵉ qᵉ
                ∨ᵉ                               ∨ᵉ
          apᵉ gᵉ (apᵉ fᵉ pᵉ) ---------------->ᵉ apᵉ gᵉ (apᵉ fᵉ qᵉ)
                         ap²ᵉ gᵉ (ap²ᵉ fᵉ αᵉ)
```

commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ) (αᵉ : pᵉ ＝ᵉ qᵉ)
  where

  compute-comp-ap²ᵉ :
    coherence-square-identificationsᵉ
      ( ap²ᵉ (gᵉ ∘ᵉ fᵉ) αᵉ)
      ( ap-compᵉ gᵉ fᵉ pᵉ)
      ( ap-compᵉ gᵉ fᵉ qᵉ)
      ( (ap²ᵉ gᵉ ∘ᵉ ap²ᵉ fᵉ) αᵉ)
  compute-comp-ap²ᵉ =
    (horizontal-concat-Id²ᵉ reflᵉ (invᵉ (ap-compᵉ (apᵉ gᵉ) (apᵉ fᵉ) αᵉ)) ∙ᵉ
      (nat-htpyᵉ (ap-compᵉ gᵉ fᵉ) αᵉ))
```

### The action of a constant function on higher identifications is constant

Considerᵉ anᵉ identificationᵉ `αᵉ : pᵉ ＝ᵉ q`ᵉ betweenᵉ twoᵉ identificationsᵉ
`pᵉ qᵉ : xᵉ ＝ᵉ y`ᵉ in aᵉ typeᵉ `A`ᵉ andᵉ considerᵉ anᵉ elementᵉ `bᵉ : B`.ᵉ Thenᵉ theᵉ triangleᵉ
ofᵉ identificationsᵉ

```text
                 ap²ᵉ (constᵉ bᵉ) αᵉ
  apᵉ (constᵉ bᵉ) pᵉ --------------->ᵉ apᵉ (constᵉ bᵉ) qᵉ
                 \ᵉ              /ᵉ
      ap-constᵉ bᵉ pᵉ \ᵉ          /ᵉ ap-constᵉ bᵉ qᵉ
                     ∨ᵉ      ∨ᵉ
                       reflᵉ
```

[commutes](foundation.commuting-triangles-of-identifications.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {xᵉ yᵉ : Aᵉ}
  {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ qᵉ)
  where

  compute-const-ap²ᵉ :
    (bᵉ : Bᵉ) →
    coherence-square-identificationsᵉ
      ( ap²ᵉ (constᵉ Aᵉ bᵉ) αᵉ)
      ( ap-constᵉ bᵉ pᵉ)
      ( ap-constᵉ bᵉ qᵉ)
      ( reflᵉ)
  compute-const-ap²ᵉ bᵉ =
    ( invᵉ (horizontal-concat-Id²ᵉ reflᵉ (ap-constᵉ reflᵉ αᵉ))) ∙ᵉ
    ( nat-htpyᵉ (ap-constᵉ bᵉ) αᵉ)
```

## See also

-ᵉ [Actionᵉ ofᵉ functionsᵉ onᵉ identifications](foundation.action-on-identifications-functions.mdᵉ)
-ᵉ [Actionᵉ ofᵉ binaryᵉ functionsᵉ onᵉ identifications](foundation.action-on-identifications-binary-functions.md).ᵉ
-ᵉ [Actionᵉ ofᵉ dependentᵉ functionsᵉ onᵉ identifications](foundation.action-on-identifications-dependent-functions.md).ᵉ