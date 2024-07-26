# Morphisms of H-spaces

```agda
module structured-types.morphisms-h-spacesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functionsᵉ
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.commuting-triangles-of-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.path-algebraᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import group-theory.homomorphisms-semigroupsᵉ

open import structured-types.h-spacesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Considerᵉ twoᵉ [H-spaces](structured-types.h-spaces.mdᵉ) `X`ᵉ andᵉ `Y`.ᵉ Aᵉ
{{#conceptᵉ "morphismᵉ ofᵉ H-spaces"ᵉ Agda=hom-H-Spaceᵉ}} fromᵉ `X`ᵉ to `Y`ᵉ consistsᵉ ofᵉ
aᵉ [pointedᵉ map](structured-types.pointed-maps.mdᵉ) `fᵉ : Xᵉ →∗ᵉ Y`ᵉ thatᵉ preservesᵉ
theᵉ unitalᵉ binaryᵉ operationᵉ

```text
  αᵉ : (xᵉ x'ᵉ : Xᵉ) → fᵉ (μᵉ xᵉ x'ᵉ) ＝ᵉ μᵉ (fᵉ xᵉ) (fᵉ x'ᵉ)
```

andᵉ whichᵉ furthermoreᵉ comesᵉ equippedᵉ with theᵉ followingᵉ structure,ᵉ witnessingᵉ
thatᵉ theᵉ unitᵉ lawsᵉ areᵉ preservedᵉ:

-ᵉ Forᵉ eachᵉ `x'ᵉ : X`ᵉ anᵉ identificationᵉ `α₁ᵉ x'`ᵉ witnessingᵉ thatᵉ theᵉ triangleᵉ

  ```text
                              αᵉ *ᵉ x'ᵉ
                  fᵉ (μᵉ *ᵉ x'ᵉ) ------->ᵉ μᵉ (fᵉ *ᵉ) (fᵉ x'ᵉ)
                        \ᵉ                 /ᵉ
                         \ᵉ               /ᵉ apᵉ (μᵉ -ᵉ (fᵉ x'ᵉ)) f₁ᵉ
                          \ᵉ             /ᵉ
                           \ᵉ           ∨ᵉ
    apᵉ fᵉ (left-unit-lawᵉ x'ᵉ) \ᵉ       μᵉ *ᵉ (fᵉ x'ᵉ)
                             \ᵉ       /ᵉ
                              \ᵉ     /ᵉ left-unit-lawᵉ (fᵉ x'ᵉ)
                               \ᵉ   /ᵉ
                                ∨ᵉ ∨ᵉ
                                fᵉ x'ᵉ
  ```

  commutes.ᵉ

-ᵉ Forᵉ eachᵉ `xᵉ : X`ᵉ anᵉ identificationᵉ `α₂ᵉ x`ᵉ witnessingᵉ thatᵉ theᵉ triangleᵉ

  ```text
                              αᵉ xᵉ *ᵉ
                  fᵉ (μᵉ xᵉ *ᵉ) -------->ᵉ μᵉ (fᵉ xᵉ) (fᵉ *ᵉ)
                        \ᵉ                 /ᵉ
                         \ᵉ               /ᵉ apᵉ (μᵉ (fᵉ xᵉ) -ᵉ) f₁ᵉ
                          \ᵉ             /ᵉ
                           \ᵉ           ∨ᵉ
    apᵉ fᵉ (right-unit-lawᵉ xᵉ) \ᵉ       μᵉ (fᵉ xᵉ) *ᵉ
                             \ᵉ       /ᵉ
                              \ᵉ     /ᵉ right-unit-lawᵉ (fᵉ xᵉ)
                               \ᵉ   /ᵉ
                                ∨ᵉ ∨ᵉ
                                fᵉ xᵉ
  ```

  commutes.ᵉ

-ᵉ Anᵉ identificationᵉ `α₃`ᵉ witnessingᵉ thatᵉ theᵉ squareᵉ

  ```text
                                                     α₁ᵉ
     α₀ᵉ *ᵉ *ᵉ ∙ᵉ (apᵉ (μᵉ -ᵉ (fᵉ *ᵉ)) f₁ᵉ ∙ᵉ left-unit-lawᵉ *ᵉ) --->ᵉ apᵉ fᵉ (left-unit-lawᵉ *ᵉ)
                       |                                         |
         (α₀ᵉ *ᵉ *ᵉ) ·lᵉ βᵉ |                                         |
                       ∨ᵉ                                         ∨ᵉ
    α₀ᵉ *ᵉ *ᵉ ∙ᵉ (apᵉ (μᵉ (fᵉ *ᵉ) -ᵉ) f₁ᵉ ∙ᵉ right-unit-lawᵉ *ᵉ) --->ᵉ apᵉ fᵉ (right-unit-lawᵉ *ᵉ)
                                                     α₂ᵉ
  ```

  Here,ᵉ theᵉ identificationᵉ onᵉ theᵉ leftᵉ isᵉ obtainedᵉ byᵉ leftᵉ whiskeringᵉ theᵉ
  identificationᵉ witnessingᵉ thatᵉ theᵉ squareᵉ

  ```text
                               apᵉ (μᵉ (fᵉ *ᵉ)) f₁ᵉ
                μᵉ (fᵉ *ᵉ) (fᵉ *ᵉ) ----------------->ᵉ μᵉ (fᵉ *ᵉ) *ᵉ
                      |                               |
    apᵉ (μᵉ -ᵉ (fᵉ *ᵉ)) f₁ᵉ |                 βᵉ             | right-unit-lawᵉ (fᵉ *ᵉ)
                      ∨ᵉ                               ∨ᵉ
                   μᵉ *ᵉ (fᵉ *ᵉ) ---------------------->ᵉ fᵉ *ᵉ
                               left-unit-lawᵉ (fᵉ *ᵉ)
  ```

  commutes,ᵉ with theᵉ identificationᵉ `αᵉ *ᵉ *ᵉ : fᵉ (μᵉ *ᵉ *ᵉ) ＝ᵉ μᵉ (fᵉ *ᵉ) (fᵉ *)`.ᵉ Theᵉ
  quickestᵉ wayᵉ to seeᵉ thatᵉ thisᵉ squareᵉ commutesᵉ isᵉ byᵉ identificationᵉ eliminationᵉ
  onᵉ theᵉ identificationᵉ `f₁ᵉ : fᵉ *ᵉ ＝ᵉ *`,ᵉ using theᵉ coherenceᵉ
  `left-unit-lawᵉ *ᵉ ＝ᵉ right-unit-lawᵉ *`.ᵉ Alternatively,ᵉ noteᵉ thatᵉ allᵉ theᵉ
  squaresᵉ in theᵉ diagramᵉ

  ```text
                               apᵉ (μᵉ (fᵉ *ᵉ)) f₁ᵉ
                μᵉ (fᵉ *ᵉ) (fᵉ *ᵉ) ----------------->ᵉ μᵉ (fᵉ *ᵉ) *ᵉ -------->ᵉ fᵉ *ᵉ
                      |                               |               |
    apᵉ (μᵉ -ᵉ (fᵉ *ᵉ)) f₁ᵉ |                 apᵉ (μᵉ -ᵉ *ᵉ) f₁ᵉ |               |
                      ∨ᵉ                               ∨ᵉ               ∨ᵉ
                   μᵉ *ᵉ (fᵉ *ᵉ) --------------------->ᵉ μᵉ *ᵉ *ᵉ ---------->ᵉ *ᵉ
                      |            apᵉ (μᵉ *ᵉ) f₁ᵉ        |               |
                      |                               |  cohᵉ ·rᵉ reflᵉ  | reflᵉ
                      ∨ᵉ                               ∨ᵉ               ∨ᵉ
                     fᵉ *ᵉ --------------------------->ᵉ *ᵉ ------------>ᵉ *ᵉ
                                       f₁ᵉ                  reflᵉ
  ```

  commute.ᵉ Thereforeᵉ weᵉ obtainᵉ anᵉ identificationᵉ

  ```text
    apᵉ (μᵉ -ᵉ (fᵉ *ᵉ)) f₁ᵉ ∙ᵉ (left-unit-lawᵉ (fᵉ *ᵉ) ∙ᵉ f₁ᵉ) ＝ᵉ
    apᵉ (μᵉ (fᵉ *ᵉ) -ᵉ) f₁ᵉ ∙ᵉ (right-unit-lawᵉ (fᵉ *ᵉ) ∙ᵉ f₁).ᵉ
  ```

  Byᵉ unwhiskeringᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ identifications,ᵉ i.e.,ᵉ byᵉ cancellingᵉ
  outᵉ `f₁`ᵉ onᵉ bothᵉ sides,ᵉ itᵉ followsᵉ thatᵉ theᵉ assertedᵉ squareᵉ commutes.ᵉ

## Definition

### The predicate of preserving left and right unit laws

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  (μᵉ : (xᵉ yᵉ : type-Pointed-Typeᵉ Aᵉ) → type-Pointed-Typeᵉ Aᵉ)
  (νᵉ : (xᵉ yᵉ : type-Pointed-Typeᵉ Bᵉ) → type-Pointed-Typeᵉ Bᵉ)
  (μfᵉ : preserves-mulᵉ μᵉ νᵉ (map-pointed-mapᵉ fᵉ))
  where

  preserves-left-unit-law-mulᵉ :
    ((xᵉ : type-Pointed-Typeᵉ Aᵉ) → μᵉ (point-Pointed-Typeᵉ Aᵉ) xᵉ ＝ᵉ xᵉ) →
    ((yᵉ : type-Pointed-Typeᵉ Bᵉ) → Idᵉ (νᵉ (point-Pointed-Typeᵉ Bᵉ) yᵉ) yᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-left-unit-law-mulᵉ lAᵉ lBᵉ =
    (xᵉ : type-Pointed-Typeᵉ Aᵉ) →
    coherence-triangle-identificationsᵉ
      ( apᵉ (map-pointed-mapᵉ fᵉ) (lAᵉ xᵉ))
      ( ( apᵉ
          ( λ tᵉ → νᵉ tᵉ (map-pointed-mapᵉ fᵉ xᵉ))
          ( preserves-point-pointed-mapᵉ fᵉ)) ∙ᵉ
        ( lBᵉ (map-pointed-mapᵉ fᵉ xᵉ)))
      ( μfᵉ)

  preserves-right-unit-law-mulᵉ :
    ((xᵉ : type-Pointed-Typeᵉ Aᵉ) → μᵉ xᵉ (point-Pointed-Typeᵉ Aᵉ) ＝ᵉ xᵉ) →
    ((yᵉ : type-Pointed-Typeᵉ Bᵉ) → νᵉ yᵉ (point-Pointed-Typeᵉ Bᵉ) ＝ᵉ yᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-right-unit-law-mulᵉ rAᵉ rBᵉ =
    (xᵉ : type-Pointed-Typeᵉ Aᵉ) →
    coherence-triangle-identificationsᵉ
      ( apᵉ (map-pointed-mapᵉ fᵉ) (rAᵉ xᵉ))
      ( ( apᵉ (νᵉ (map-pointed-mapᵉ fᵉ xᵉ)) (preserves-point-pointed-mapᵉ fᵉ)) ∙ᵉ
        ( rBᵉ (map-pointed-mapᵉ fᵉ xᵉ)))
      ( μfᵉ)
```

### The predicate of preserving H-space structure on a pointed type

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : H-Spaceᵉ l1ᵉ) (Nᵉ : H-Spaceᵉ l2ᵉ)
  where

  preserves-mul-pointed-map-H-Spaceᵉ :
    (pointed-type-H-Spaceᵉ Mᵉ →∗ᵉ pointed-type-H-Spaceᵉ Nᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-mul-pointed-map-H-Spaceᵉ fᵉ =
    preserves-mulᵉ (mul-H-Spaceᵉ Mᵉ) (mul-H-Spaceᵉ Nᵉ) (map-pointed-mapᵉ fᵉ)

  preserves-left-unit-law-mul-pointed-map-H-Spaceᵉ :
    (fᵉ : pointed-type-H-Spaceᵉ Mᵉ →∗ᵉ pointed-type-H-Spaceᵉ Nᵉ) →
    preserves-mul-pointed-map-H-Spaceᵉ fᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-left-unit-law-mul-pointed-map-H-Spaceᵉ fᵉ μfᵉ =
    preserves-left-unit-law-mulᵉ fᵉ
      ( mul-H-Spaceᵉ Mᵉ)
      ( mul-H-Spaceᵉ Nᵉ)
      ( μfᵉ)
      ( left-unit-law-mul-H-Spaceᵉ Mᵉ)
      ( left-unit-law-mul-H-Spaceᵉ Nᵉ)

  preserves-right-unit-law-mul-pointed-map-H-Spaceᵉ :
    (fᵉ : pointed-type-H-Spaceᵉ Mᵉ →∗ᵉ pointed-type-H-Spaceᵉ Nᵉ) →
    preserves-mul-pointed-map-H-Spaceᵉ fᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-right-unit-law-mul-pointed-map-H-Spaceᵉ fᵉ μfᵉ =
    preserves-right-unit-law-mulᵉ fᵉ
      ( mul-H-Spaceᵉ Mᵉ)
      ( mul-H-Spaceᵉ Nᵉ)
      ( μfᵉ)
      ( right-unit-law-mul-H-Spaceᵉ Mᵉ)
      ( right-unit-law-mul-H-Spaceᵉ Nᵉ)

  coherence-square-unit-laws-preserves-point-pointed-map-H-Spaceᵉ :
    (fᵉ : pointed-type-H-Spaceᵉ Mᵉ →∗ᵉ pointed-type-H-Spaceᵉ Nᵉ) →
    coherence-square-identificationsᵉ
      ( apᵉ
        ( mul-H-Spaceᵉ Nᵉ (map-pointed-mapᵉ fᵉ (unit-H-Spaceᵉ Mᵉ)))
        ( preserves-point-pointed-mapᵉ fᵉ))
      ( apᵉ
        ( mul-H-Space'ᵉ Nᵉ (map-pointed-mapᵉ fᵉ (unit-H-Spaceᵉ Mᵉ)))
        ( preserves-point-pointed-mapᵉ fᵉ))
      ( right-unit-law-mul-H-Spaceᵉ Nᵉ (map-pointed-mapᵉ fᵉ (unit-H-Spaceᵉ Mᵉ)))
      ( left-unit-law-mul-H-Spaceᵉ Nᵉ (map-pointed-mapᵉ fᵉ (unit-H-Spaceᵉ Mᵉ)))
  coherence-square-unit-laws-preserves-point-pointed-map-H-Spaceᵉ (fᵉ ,ᵉ reflᵉ) =
    coh-unit-laws-mul-H-Spaceᵉ Nᵉ

  preserves-coherence-unit-laws-mul-pointed-map-H-Spaceᵉ :
    (fᵉ : pointed-type-H-Spaceᵉ Mᵉ →∗ᵉ pointed-type-H-Spaceᵉ Nᵉ) →
    (μᵉ : preserves-mul-pointed-map-H-Spaceᵉ fᵉ) →
    (νᵉ : preserves-left-unit-law-mul-pointed-map-H-Spaceᵉ fᵉ μᵉ) →
    (ρᵉ : preserves-right-unit-law-mul-pointed-map-H-Spaceᵉ fᵉ μᵉ) → UUᵉ l2ᵉ
  preserves-coherence-unit-laws-mul-pointed-map-H-Spaceᵉ fᵉ μᵉ νᵉ ρᵉ =
    coherence-square-identificationsᵉ
      ( νᵉ (unit-H-Spaceᵉ Mᵉ))
      ( ap²ᵉ (map-pointed-mapᵉ fᵉ) (coh-unit-laws-mul-H-Spaceᵉ Mᵉ))
      ( left-whisker-concatᵉ
        ( μᵉ)
        ( coherence-square-unit-laws-preserves-point-pointed-map-H-Spaceᵉ fᵉ))
      ( ρᵉ (unit-H-Spaceᵉ Mᵉ))

  preserves-unital-mul-pointed-map-H-Spaceᵉ :
    (fᵉ : pointed-type-H-Spaceᵉ Mᵉ →∗ᵉ pointed-type-H-Spaceᵉ Nᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-unital-mul-pointed-map-H-Spaceᵉ fᵉ =
    Σᵉ ( preserves-mul-pointed-map-H-Spaceᵉ fᵉ)
      ( λ μᵉ →
        Σᵉ ( preserves-left-unit-law-mul-pointed-map-H-Spaceᵉ fᵉ μᵉ)
          ( λ νᵉ →
            Σᵉ ( preserves-right-unit-law-mul-pointed-map-H-Spaceᵉ fᵉ μᵉ)
              ( preserves-coherence-unit-laws-mul-pointed-map-H-Spaceᵉ fᵉ μᵉ νᵉ)))
```

### Morphisms of H-spaces

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : H-Spaceᵉ l1ᵉ) (Nᵉ : H-Spaceᵉ l2ᵉ)
  where

  hom-H-Spaceᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-H-Spaceᵉ =
    Σᵉ ( pointed-type-H-Spaceᵉ Mᵉ →∗ᵉ pointed-type-H-Spaceᵉ Nᵉ)
      ( preserves-unital-mul-pointed-map-H-Spaceᵉ Mᵉ Nᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Mᵉ : H-Spaceᵉ l1ᵉ} {Nᵉ : H-Spaceᵉ l2ᵉ} (fᵉ : hom-H-Spaceᵉ Mᵉ Nᵉ)
  where

  pointed-map-hom-H-Spaceᵉ : pointed-type-H-Spaceᵉ Mᵉ →∗ᵉ pointed-type-H-Spaceᵉ Nᵉ
  pointed-map-hom-H-Spaceᵉ = pr1ᵉ fᵉ

  map-hom-H-Spaceᵉ : type-H-Spaceᵉ Mᵉ → type-H-Spaceᵉ Nᵉ
  map-hom-H-Spaceᵉ = map-pointed-mapᵉ pointed-map-hom-H-Spaceᵉ

  preserves-unit-hom-H-Spaceᵉ :
    map-hom-H-Spaceᵉ (unit-H-Spaceᵉ Mᵉ) ＝ᵉ unit-H-Spaceᵉ Nᵉ
  preserves-unit-hom-H-Spaceᵉ =
    preserves-point-pointed-mapᵉ pointed-map-hom-H-Spaceᵉ

  preserves-unital-mul-hom-H-Spaceᵉ :
    preserves-unital-mul-pointed-map-H-Spaceᵉ Mᵉ Nᵉ pointed-map-hom-H-Spaceᵉ
  preserves-unital-mul-hom-H-Spaceᵉ = pr2ᵉ fᵉ

  preserves-mul-hom-H-Spaceᵉ :
    preserves-mul-pointed-map-H-Spaceᵉ Mᵉ Nᵉ pointed-map-hom-H-Spaceᵉ
  preserves-mul-hom-H-Spaceᵉ =
    pr1ᵉ preserves-unital-mul-hom-H-Spaceᵉ

  preserves-left-unit-law-mul-hom-H-Spaceᵉ :
    preserves-left-unit-law-mul-pointed-map-H-Spaceᵉ Mᵉ Nᵉ
      ( pointed-map-hom-H-Spaceᵉ)
      ( preserves-mul-hom-H-Spaceᵉ)
  preserves-left-unit-law-mul-hom-H-Spaceᵉ =
    pr1ᵉ (pr2ᵉ preserves-unital-mul-hom-H-Spaceᵉ)

  preserves-right-unit-law-mul-hom-H-Spaceᵉ :
    preserves-right-unit-law-mul-pointed-map-H-Spaceᵉ Mᵉ Nᵉ
      ( pointed-map-hom-H-Spaceᵉ)
      ( preserves-mul-hom-H-Spaceᵉ)
  preserves-right-unit-law-mul-hom-H-Spaceᵉ =
    pr1ᵉ (pr2ᵉ (pr2ᵉ preserves-unital-mul-hom-H-Spaceᵉ))

  preserves-coherence-unit-laws-mul-hom-H-Spaceᵉ :
    preserves-coherence-unit-laws-mul-pointed-map-H-Spaceᵉ Mᵉ Nᵉ
      ( pointed-map-hom-H-Spaceᵉ)
      ( preserves-mul-hom-H-Spaceᵉ)
      ( preserves-left-unit-law-mul-hom-H-Spaceᵉ)
      ( preserves-right-unit-law-mul-hom-H-Spaceᵉ)
  preserves-coherence-unit-laws-mul-hom-H-Spaceᵉ =
    pr2ᵉ (pr2ᵉ (pr2ᵉ preserves-unital-mul-hom-H-Spaceᵉ))
```

### Homotopies of morphisms of H-spaces

```agda
preserves-mul-htpyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (μAᵉ : Aᵉ → Aᵉ → Aᵉ) (μBᵉ : Bᵉ → Bᵉ → Bᵉ) →
  {fᵉ gᵉ : Aᵉ → Bᵉ} (μfᵉ : preserves-mulᵉ μAᵉ μBᵉ fᵉ) (μgᵉ : preserves-mulᵉ μAᵉ μBᵉ gᵉ) →
  (fᵉ ~ᵉ gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
preserves-mul-htpyᵉ {Aᵉ = Aᵉ} μAᵉ μBᵉ μfᵉ μgᵉ Hᵉ =
  (aᵉ bᵉ : Aᵉ) → Idᵉ (μfᵉ ∙ᵉ ap-binaryᵉ μBᵉ (Hᵉ aᵉ) (Hᵉ bᵉ)) (Hᵉ (μAᵉ aᵉ bᵉ) ∙ᵉ μgᵉ)
```