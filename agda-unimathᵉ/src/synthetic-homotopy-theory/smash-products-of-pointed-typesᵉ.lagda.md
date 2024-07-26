# Smash products of pointed types

```agda
module synthetic-homotopy-theory.smash-products-of-pointed-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functionsᵉ
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import structured-types.constant-pointed-mapsᵉ
open import structured-types.pointed-cartesian-product-typesᵉ
open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.pointed-unit-typeᵉ

open import synthetic-homotopy-theory.cocones-under-pointed-span-diagramsᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
open import synthetic-homotopy-theory.pushouts-of-pointed-typesᵉ
open import synthetic-homotopy-theory.wedges-of-pointed-typesᵉ
```

</details>

## Idea

Givenᵉ twoᵉ [pointedᵉ types](structured-types.pointed-types.mdᵉ) `aᵉ : A`ᵉ andᵉ `bᵉ : B`ᵉ
weᵉ mayᵉ formᵉ theirᵉ **smashᵉ product**ᵉ asᵉ theᵉ followingᵉ
[pushout](synthetic-homotopy-theory.pushouts.mdᵉ)

```text
 Aᵉ ∨∗ᵉ Bᵉ ---->ᵉ Aᵉ ×∗ᵉ Bᵉ
    |           |
    |           |
    ∨ᵉ         ⌜ᵉ ∨ᵉ
  unitᵉ ----->ᵉ Aᵉ ∧∗ᵉ Bᵉ
```

where theᵉ mapᵉ `Aᵉ ∨∗ᵉ Bᵉ → Aᵉ ×∗ᵉ B`ᵉ isᵉ theᵉ canonicalᵉ inclusionᵉ
`map-wedge-product-Pointed-Type`ᵉ fromᵉ theᵉ
[wedge](synthetic-homotopy-theory.wedges-of-pointed-types.mdᵉ) intoᵉ theᵉ
[pointedᵉ cartesianᵉ product](structured-types.pointed-cartesian-product-types.md).ᵉ

## Definition

```agda
smash-product-Pointed-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ) →
  Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
smash-product-Pointed-Typeᵉ Aᵉ Bᵉ =
  pushout-Pointed-Typeᵉ
    ( pointed-map-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ)
    ( terminal-pointed-mapᵉ (Aᵉ ∨∗ᵉ Bᵉ))

infixr 15 _∧∗ᵉ_
_∧∗ᵉ_ = smash-product-Pointed-Typeᵉ
```

**Note**ᵉ: Theᵉ symbolsᵉ usedᵉ forᵉ theᵉ smashᵉ productᵉ `_∧∗_`ᵉ areᵉ theᵉ
[logicalᵉ and](https://codepoints.net/U+2227ᵉ) `∧`ᵉ (agda-inputᵉ: `\wedge`ᵉ `\and`),ᵉ
andᵉ theᵉ [asteriskᵉ operator](https://codepoints.net/U+2217ᵉ) `∗`ᵉ (agda-inputᵉ:
`\ast`),ᵉ notᵉ theᵉ [asterisk](https://codepoints.net/U+002Aᵉ) `*`.ᵉ

```agda
cogap-smash-product-Pointed-Typeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} {Xᵉ : Pointed-Typeᵉ l3ᵉ} →
  cocone-Pointed-Typeᵉ
    ( pointed-map-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ)
    ( terminal-pointed-mapᵉ (Aᵉ ∨∗ᵉ Bᵉ)) Xᵉ →
  (Aᵉ ∧∗ᵉ Bᵉ) →∗ᵉ Xᵉ
cogap-smash-product-Pointed-Typeᵉ {Aᵉ = Aᵉ} {Bᵉ} =
  cogap-Pointed-Typeᵉ
    ( pointed-map-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ)
    ( terminal-pointed-mapᵉ (Aᵉ ∨∗ᵉ Bᵉ))

map-cogap-smash-product-Pointed-Typeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} {Xᵉ : Pointed-Typeᵉ l3ᵉ} →
  cocone-Pointed-Typeᵉ
    ( pointed-map-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ)
    ( terminal-pointed-mapᵉ (Aᵉ ∨∗ᵉ Bᵉ))
    ( Xᵉ) →
  type-Pointed-Typeᵉ (Aᵉ ∧∗ᵉ Bᵉ) → type-Pointed-Typeᵉ Xᵉ
map-cogap-smash-product-Pointed-Typeᵉ cᵉ =
  pr1ᵉ (cogap-smash-product-Pointed-Typeᵉ cᵉ)
```

## Properties

### The canonical pointed map from the cartesian product to the smash product

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ)
  where

  pointed-map-smash-product-product-Pointed-Typeᵉ : (Aᵉ ×∗ᵉ Bᵉ) →∗ᵉ (Aᵉ ∧∗ᵉ Bᵉ)
  pointed-map-smash-product-product-Pointed-Typeᵉ =
    inl-pushout-Pointed-Typeᵉ
      ( pointed-map-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ)
      ( terminal-pointed-mapᵉ (Aᵉ ∨∗ᵉ Bᵉ))

  map-smash-product-product-Pointed-Typeᵉ :
    type-Pointed-Typeᵉ (Aᵉ ×∗ᵉ Bᵉ) → type-Pointed-Typeᵉ (Aᵉ ∧∗ᵉ Bᵉ)
  map-smash-product-product-Pointed-Typeᵉ =
    map-pointed-mapᵉ pointed-map-smash-product-product-Pointed-Typeᵉ
```

### Pointed maps into pointed types `A` and `B` induce a pointed map into `A ∧∗ B`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} {Sᵉ : Pointed-Typeᵉ l3ᵉ}
  where

  gap-smash-product-Pointed-Typeᵉ :
    (fᵉ : Sᵉ →∗ᵉ Aᵉ) (gᵉ : Sᵉ →∗ᵉ Bᵉ) → Sᵉ →∗ᵉ (Aᵉ ∧∗ᵉ Bᵉ)
  gap-smash-product-Pointed-Typeᵉ fᵉ gᵉ =
    pointed-map-smash-product-product-Pointed-Typeᵉ Aᵉ Bᵉ ∘∗ᵉ
    gap-product-Pointed-Typeᵉ fᵉ gᵉ

  map-gap-smash-product-Pointed-Typeᵉ :
    (fᵉ : Sᵉ →∗ᵉ Aᵉ) (gᵉ : Sᵉ →∗ᵉ Bᵉ) → type-Pointed-Typeᵉ Sᵉ → type-Pointed-Typeᵉ (Aᵉ ∧∗ᵉ Bᵉ)
  map-gap-smash-product-Pointed-Typeᵉ fᵉ gᵉ =
    pr1ᵉ (gap-smash-product-Pointed-Typeᵉ fᵉ gᵉ)
```

### The canonical map from the wedge sum to the smash product identifies all points

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ)
  where

  pointed-map-smash-product-wedge-Pointed-Typeᵉ : (Aᵉ ∨∗ᵉ Bᵉ) →∗ᵉ (Aᵉ ∧∗ᵉ Bᵉ)
  pointed-map-smash-product-wedge-Pointed-Typeᵉ =
    pointed-map-smash-product-product-Pointed-Typeᵉ Aᵉ Bᵉ ∘∗ᵉ
    pointed-map-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ

  map-smash-product-wedge-Pointed-Typeᵉ :
    type-Pointed-Typeᵉ (Aᵉ ∨∗ᵉ Bᵉ) → type-Pointed-Typeᵉ (Aᵉ ∧∗ᵉ Bᵉ)
  map-smash-product-wedge-Pointed-Typeᵉ =
    map-pointed-mapᵉ pointed-map-smash-product-wedge-Pointed-Typeᵉ

  contraction-map-smash-product-wedge-Pointed-Typeᵉ :
    ( xᵉ : type-Pointed-Typeᵉ (Aᵉ ∨∗ᵉ Bᵉ)) →
    map-smash-product-wedge-Pointed-Typeᵉ xᵉ ＝ᵉ
    point-Pointed-Typeᵉ (Aᵉ ∧∗ᵉ Bᵉ)
  contraction-map-smash-product-wedge-Pointed-Typeᵉ xᵉ =
    ( glue-pushoutᵉ
      ( map-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ)
      ( map-pointed-mapᵉ {Aᵉ = Aᵉ ∨∗ᵉ Bᵉ} {Bᵉ = unit-Pointed-Typeᵉ}
        ( terminal-pointed-mapᵉ (Aᵉ ∨∗ᵉ Bᵉ)))
      ( xᵉ)) ∙ᵉ
    ( right-whisker-compᵉ
      ( htpy-pointed-htpyᵉ
        ( is-initial-unit-Pointed-Typeᵉ
          ( Aᵉ ∧∗ᵉ Bᵉ)
          ( inr-pushout-Pointed-Typeᵉ
            ( pointed-map-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ)
            ( terminal-pointed-mapᵉ (Aᵉ ∨∗ᵉ Bᵉ)))))
      ( map-terminal-pointed-mapᵉ (Aᵉ ∨∗ᵉ Bᵉ))
      ( xᵉ)) ∙ᵉ
    ( preserves-point-pointed-mapᵉ
      ( inclusion-point-Pointed-Typeᵉ (Aᵉ ∧∗ᵉ Bᵉ)))

  coh-contraction-map-smash-product-wedge-Pointed-Typeᵉ :
    ( apᵉ
      ( map-smash-product-wedge-Pointed-Typeᵉ)
      ( glue-wedge-Pointed-Typeᵉ Aᵉ Bᵉ)) ∙ᵉ
    ( contraction-map-smash-product-wedge-Pointed-Typeᵉ
        ( map-inr-wedge-Pointed-Typeᵉ Aᵉ Bᵉ (point-Pointed-Typeᵉ Bᵉ))) ＝ᵉ
    ( contraction-map-smash-product-wedge-Pointed-Typeᵉ
      ( map-inl-wedge-Pointed-Typeᵉ Aᵉ Bᵉ (point-Pointed-Typeᵉ Aᵉ)))
  coh-contraction-map-smash-product-wedge-Pointed-Typeᵉ =
    ( map-inv-compute-dependent-identification-eq-value-functionᵉ
      ( map-smash-product-wedge-Pointed-Typeᵉ)
      ( map-constant-pointed-mapᵉ (Aᵉ ∨∗ᵉ Bᵉ) (Aᵉ ∧∗ᵉ Bᵉ))
      ( glue-wedge-Pointed-Typeᵉ Aᵉ Bᵉ)
      ( contraction-map-smash-product-wedge-Pointed-Typeᵉ
        ( map-inl-wedge-Pointed-Typeᵉ Aᵉ Bᵉ (point-Pointed-Typeᵉ Aᵉ)))
      ( contraction-map-smash-product-wedge-Pointed-Typeᵉ
        ( map-inr-wedge-Pointed-Typeᵉ Aᵉ Bᵉ (point-Pointed-Typeᵉ Bᵉ)))
      ( apdᵉ
        ( contraction-map-smash-product-wedge-Pointed-Typeᵉ)
        ( glue-wedge-Pointed-Typeᵉ Aᵉ Bᵉ))) ∙ᵉ
    ( left-whisker-concatᵉ
      ( contraction-map-smash-product-wedge-Pointed-Typeᵉ
        ( map-inl-wedge-Pointed-Typeᵉ Aᵉ Bᵉ (point-Pointed-Typeᵉ Aᵉ)))
      ( ap-constᵉ
        ( point-Pointed-Typeᵉ (Aᵉ ∧∗ᵉ Bᵉ))
        ( glue-wedge-Pointed-Typeᵉ Aᵉ Bᵉ))) ∙ᵉ
    ( right-unitᵉ)
```

### The map from the pointed product to the smash product identifies elements

ofᵉ theᵉ formᵉ `(x,ᵉ b)`ᵉ andᵉ `(a,ᵉ y)`,ᵉ where `b`ᵉ andᵉ `a`ᵉ areᵉ theᵉ baseᵉ pointsᵉ ofᵉ `B`ᵉ
andᵉ `A`ᵉ respectively.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ)
  where

  inl-glue-smash-product-Pointed-Typeᵉ :
    ( xᵉ : type-Pointed-Typeᵉ Aᵉ) →
    map-smash-product-product-Pointed-Typeᵉ Aᵉ Bᵉ
      ( xᵉ ,ᵉ point-Pointed-Typeᵉ Bᵉ) ＝ᵉ
    map-smash-product-product-Pointed-Typeᵉ Aᵉ Bᵉ
      ( point-Pointed-Typeᵉ Aᵉ ,ᵉ point-Pointed-Typeᵉ Bᵉ)
  inl-glue-smash-product-Pointed-Typeᵉ xᵉ =
    ( apᵉ
      ( map-smash-product-product-Pointed-Typeᵉ Aᵉ Bᵉ)
      ( invᵉ (compute-inl-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ xᵉ))) ∙ᵉ
    ( contraction-map-smash-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ
      ( map-inl-wedge-Pointed-Typeᵉ Aᵉ Bᵉ xᵉ))

  inr-glue-smash-product-Pointed-Typeᵉ :
    ( yᵉ : type-Pointed-Typeᵉ Bᵉ) →
    map-smash-product-product-Pointed-Typeᵉ Aᵉ Bᵉ
      ( point-Pointed-Typeᵉ Aᵉ ,ᵉ yᵉ) ＝ᵉ
    map-smash-product-product-Pointed-Typeᵉ Aᵉ Bᵉ
      ( point-Pointed-Typeᵉ Aᵉ ,ᵉ point-Pointed-Typeᵉ Bᵉ)
  inr-glue-smash-product-Pointed-Typeᵉ yᵉ =
    ( apᵉ
      ( map-smash-product-product-Pointed-Typeᵉ Aᵉ Bᵉ)
      ( invᵉ (compute-inr-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ yᵉ))) ∙ᵉ
    ( contraction-map-smash-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ
      ( map-inr-wedge-Pointed-Typeᵉ Aᵉ Bᵉ yᵉ))

  coh-glue-smash-product-Pointed-Typeᵉ :
    inl-glue-smash-product-Pointed-Typeᵉ (point-Pointed-Typeᵉ Aᵉ) ＝ᵉ
    inr-glue-smash-product-Pointed-Typeᵉ (point-Pointed-Typeᵉ Bᵉ)
  coh-glue-smash-product-Pointed-Typeᵉ =
    ( left-whisker-concatᵉ
      ( apᵉ
        ( map-smash-product-product-Pointed-Typeᵉ Aᵉ Bᵉ)
        ( invᵉ
          ( compute-inl-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ (point-Pointed-Typeᵉ Aᵉ))))
      ( invᵉ (coh-contraction-map-smash-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ))) ∙ᵉ
    ( invᵉ
      ( assocᵉ
        ( apᵉ (map-smash-product-product-Pointed-Typeᵉ Aᵉ Bᵉ)
          ( invᵉ
            ( compute-inl-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ
              ( point-Pointed-Typeᵉ Aᵉ))))
        ( apᵉ (map-smash-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ)
          ( glue-wedge-Pointed-Typeᵉ Aᵉ Bᵉ))
        ( contraction-map-smash-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ
          ( map-inr-wedge-Pointed-Typeᵉ Aᵉ Bᵉ (point-Pointed-Typeᵉ Bᵉ))))) ∙ᵉ
    ( right-whisker-concatᵉ
      ( ( left-whisker-concatᵉ
          ( apᵉ (map-smash-product-product-Pointed-Typeᵉ Aᵉ Bᵉ)
            ( invᵉ
              ( compute-inl-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ
                ( point-Pointed-Typeᵉ Aᵉ))))
          ( ap-compᵉ
            ( map-smash-product-product-Pointed-Typeᵉ Aᵉ Bᵉ)
            ( map-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ)
            ( glue-wedge-Pointed-Typeᵉ Aᵉ Bᵉ))) ∙ᵉ
        ( invᵉ
          ( ap-concatᵉ
            ( map-smash-product-product-Pointed-Typeᵉ Aᵉ Bᵉ)
            ( invᵉ
              ( compute-inl-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ
                ( point-Pointed-Typeᵉ Aᵉ)))
            ( apᵉ
              ( map-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ)
              ( glue-wedge-Pointed-Typeᵉ Aᵉ Bᵉ)))) ∙ᵉ
        ( ap²ᵉ
          ( map-smash-product-product-Pointed-Typeᵉ Aᵉ Bᵉ)
          ( invᵉ
            ( left-transpose-eq-concatᵉ
              ( compute-inl-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ
                ( point-Pointed-Typeᵉ Aᵉ))
              ( invᵉ
                ( compute-inr-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ
                  ( point-Pointed-Typeᵉ Bᵉ)))
              ( apᵉ
                ( map-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ)
                ( glue-wedge-Pointed-Typeᵉ Aᵉ Bᵉ))
              ( invᵉ
                ( right-transpose-eq-concatᵉ
                  ( apᵉ
                    ( map-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ)
                    ( glue-wedge-Pointed-Typeᵉ Aᵉ Bᵉ))
                  ( compute-inr-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ
                    ( point-Pointed-Typeᵉ Bᵉ))
                  ( compute-inl-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ
                    ( point-Pointed-Typeᵉ Aᵉ))
                  ( ( compute-glue-cogapᵉ
                      ( map-pointed-mapᵉ
                        ( inclusion-point-Pointed-Typeᵉ Aᵉ))
                      ( map-pointed-mapᵉ
                        ( inclusion-point-Pointed-Typeᵉ Bᵉ))
                      ( cocone-cocone-Pointed-Typeᵉ
                        ( inclusion-point-Pointed-Typeᵉ Aᵉ)
                        ( inclusion-point-Pointed-Typeᵉ Bᵉ)
                        ( cocone-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ))
                      ( point-Pointed-Typeᵉ unit-Pointed-Typeᵉ)) ∙ᵉ
                    ( right-unitᵉ))))))))
      ( contraction-map-smash-product-wedge-Pointed-Typeᵉ Aᵉ Bᵉ
        ( map-inr-wedge-Pointed-Typeᵉ Aᵉ Bᵉ (point-Pointed-Typeᵉ Bᵉ))))
```

### The universal property of the smash product

Fixingᵉ aᵉ pointedᵉ typeᵉ `B`,ᵉ theᵉ _universalᵉ propertyᵉ ofᵉ theᵉ smashᵉ productᵉ_ statesᵉ
thatᵉ theᵉ functorᵉ `-ᵉ ∧∗ᵉ B`ᵉ formsᵉ theᵉ left-adjointᵉ to theᵉ functorᵉ `Bᵉ →∗ᵉ -`ᵉ ofᵉ
[pointedᵉ maps](structured-types.pointed-maps.mdᵉ) with sourceᵉ `B`.ᵉ Inᵉ theᵉ
languageᵉ ofᵉ typeᵉ theory,ᵉ thisᵉ meansᵉ thatᵉ weᵉ haveᵉ aᵉ pointedᵉ equivalenceᵉ:

```text
  ((Aᵉ ∧∗ᵉ Bᵉ) →∗ᵉ Cᵉ) ≃∗ᵉ (Aᵉ →∗ᵉ Bᵉ →∗ᵉ C).ᵉ
```

**Note:**ᵉ Theᵉ categoricalᵉ productᵉ in theᵉ categoryᵉ ofᵉ pointedᵉ typesᵉ isᵉ theᵉ
[pointedᵉ cartesianᵉ product](structured-types.pointed-cartesian-product-types.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ) (Cᵉ : Pointed-Typeᵉ l3ᵉ)
  (fᵉ : (Aᵉ ∧∗ᵉ Bᵉ) →∗ᵉ Cᵉ)
  where

  map-map-universal-property-smash-product-Pointed-Typeᵉ :
    type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ Cᵉ
  map-map-universal-property-smash-product-Pointed-Typeᵉ xᵉ yᵉ =
    map-pointed-mapᵉ fᵉ (map-smash-product-product-Pointed-Typeᵉ Aᵉ Bᵉ (xᵉ ,ᵉ yᵉ))

  preserves-point-map-map-universal-property-smash-product-Pointed-Typeᵉ :
    (xᵉ : type-Pointed-Typeᵉ Aᵉ) →
    map-map-universal-property-smash-product-Pointed-Typeᵉ xᵉ
      ( point-Pointed-Typeᵉ Bᵉ) ＝ᵉ
    point-Pointed-Typeᵉ Cᵉ
  preserves-point-map-map-universal-property-smash-product-Pointed-Typeᵉ xᵉ =
    ( apᵉ
      ( map-pointed-mapᵉ fᵉ)
      ( inl-glue-smash-product-Pointed-Typeᵉ Aᵉ Bᵉ xᵉ)) ∙ᵉ
    ( preserves-point-pointed-mapᵉ fᵉ)

  map-universal-property-smash-product-Pointed-Typeᵉ :
    type-Pointed-Typeᵉ Aᵉ → (Bᵉ →∗ᵉ Cᵉ)
  pr1ᵉ (map-universal-property-smash-product-Pointed-Typeᵉ xᵉ) =
    map-map-universal-property-smash-product-Pointed-Typeᵉ xᵉ
  pr2ᵉ (map-universal-property-smash-product-Pointed-Typeᵉ xᵉ) =
    preserves-point-map-map-universal-property-smash-product-Pointed-Typeᵉ xᵉ

  htpy-preserves-point-map-universal-property-smash-product-Pointed-Typeᵉ :
    map-map-universal-property-smash-product-Pointed-Typeᵉ
      ( point-Pointed-Typeᵉ Aᵉ) ~ᵉ
    map-constant-pointed-mapᵉ Bᵉ Cᵉ
  htpy-preserves-point-map-universal-property-smash-product-Pointed-Typeᵉ yᵉ =
    ( apᵉ (map-pointed-mapᵉ fᵉ) (inr-glue-smash-product-Pointed-Typeᵉ Aᵉ Bᵉ yᵉ)) ∙ᵉ
    ( preserves-point-pointed-mapᵉ fᵉ)

  coherence-point-preserves-point-map-universal-property-smash-product-Pointed-Typeᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ
      ( map-universal-property-smash-product-Pointed-Typeᵉ
        ( point-Pointed-Typeᵉ Aᵉ))
      ( constant-pointed-mapᵉ Bᵉ Cᵉ)
      ( htpy-preserves-point-map-universal-property-smash-product-Pointed-Typeᵉ)
  coherence-point-preserves-point-map-universal-property-smash-product-Pointed-Typeᵉ =
    ( right-whisker-concatᵉ
      ( ap²ᵉ
        ( map-pointed-mapᵉ fᵉ)
        ( coh-glue-smash-product-Pointed-Typeᵉ Aᵉ Bᵉ))
      ( preserves-point-pointed-mapᵉ fᵉ)) ∙ᵉ
    ( invᵉ right-unitᵉ)

  pointed-htpy-preserves-point-map-universal-property-smash-product-Pointed-Typeᵉ :
    map-universal-property-smash-product-Pointed-Typeᵉ (point-Pointed-Typeᵉ Aᵉ) ~∗ᵉ
    constant-pointed-mapᵉ Bᵉ Cᵉ
  pr1ᵉ
    pointed-htpy-preserves-point-map-universal-property-smash-product-Pointed-Typeᵉ =
    htpy-preserves-point-map-universal-property-smash-product-Pointed-Typeᵉ
  pr2ᵉ
    pointed-htpy-preserves-point-map-universal-property-smash-product-Pointed-Typeᵉ =
    coherence-point-preserves-point-map-universal-property-smash-product-Pointed-Typeᵉ

  preserves-point-map-universal-property-smash-product-Pointed-Typeᵉ :
    map-universal-property-smash-product-Pointed-Typeᵉ (point-Pointed-Typeᵉ Aᵉ) ＝ᵉ
    constant-pointed-mapᵉ Bᵉ Cᵉ
  preserves-point-map-universal-property-smash-product-Pointed-Typeᵉ =
    eq-pointed-htpyᵉ
      ( map-universal-property-smash-product-Pointed-Typeᵉ
        ( point-Pointed-Typeᵉ Aᵉ))
      ( constant-pointed-mapᵉ Bᵉ Cᵉ)
      ( pointed-htpy-preserves-point-map-universal-property-smash-product-Pointed-Typeᵉ)

  pointed-map-universal-property-smash-product-Pointed-Typeᵉ :
    Aᵉ →∗ᵉ (pointed-map-Pointed-Typeᵉ Bᵉ Cᵉ)
  pr1ᵉ pointed-map-universal-property-smash-product-Pointed-Typeᵉ =
    map-universal-property-smash-product-Pointed-Typeᵉ
  pr2ᵉ pointed-map-universal-property-smash-product-Pointed-Typeᵉ =
    preserves-point-map-universal-property-smash-product-Pointed-Typeᵉ
```

## See also

-ᵉ [Wedgesᵉ ofᵉ pointedᵉ types](synthetic-homotopy-theory.wedges-of-pointed-types.mdᵉ)