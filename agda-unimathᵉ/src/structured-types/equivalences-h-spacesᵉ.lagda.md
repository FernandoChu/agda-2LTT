# Equivalences of H-spaces

```agda
module structured-types.equivalences-h-spacesᵉ where
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
open import structured-types.morphisms-h-spacesᵉ
open import structured-types.pointed-equivalencesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Considerᵉ twoᵉ [H-spaces](structured-types.h-spaces.mdᵉ) `X`ᵉ andᵉ `Y`.ᵉ Anᵉ
{{#conceptᵉ "equivalenceᵉ ofᵉ H-spaces"ᵉ Agda=equiv-H-Spaceᵉ}} fromᵉ `X`ᵉ to `Y`ᵉ
consistsᵉ ofᵉ aᵉ [pointedᵉ equivalence](structured-types.pointed-equivalences.mdᵉ)
`eᵉ : Xᵉ ≃∗ᵉ Y`ᵉ thatᵉ preservesᵉ theᵉ unitalᵉ binaryᵉ operationᵉ

```text
  αᵉ : (xᵉ x'ᵉ : Xᵉ) → eᵉ (μᵉ xᵉ x'ᵉ) ＝ᵉ μᵉ (eᵉ xᵉ) (eᵉ x'ᵉ)
```

andᵉ whichᵉ furthermoreᵉ comesᵉ equippedᵉ with theᵉ followingᵉ structure,ᵉ witnessingᵉ
thatᵉ theᵉ unitᵉ lawsᵉ areᵉ preservedᵉ:

-ᵉ Forᵉ eachᵉ `x'ᵉ : X`ᵉ anᵉ identificationᵉ `α₁ᵉ x'`ᵉ witnessingᵉ thatᵉ theᵉ triangleᵉ

  ```text
                              αᵉ *ᵉ x'ᵉ
                  eᵉ (μᵉ *ᵉ x'ᵉ) ------->ᵉ μᵉ (eᵉ *ᵉ) (eᵉ x'ᵉ)
                        \ᵉ                 /ᵉ
                         \ᵉ               /ᵉ apᵉ (μᵉ -ᵉ (eᵉ x'ᵉ)) e₁ᵉ
                          \ᵉ             /ᵉ
                           \ᵉ           ∨ᵉ
    apᵉ eᵉ (left-unit-lawᵉ x'ᵉ) \ᵉ       μᵉ *ᵉ (eᵉ x'ᵉ)
                             \ᵉ       /ᵉ
                              \ᵉ     /ᵉ left-unit-lawᵉ (eᵉ x'ᵉ)
                               \ᵉ   /ᵉ
                                ∨ᵉ ∨ᵉ
                                eᵉ x'ᵉ
  ```

  commutes.ᵉ

-ᵉ Forᵉ eachᵉ `xᵉ : X`ᵉ anᵉ identificationᵉ `α₂ᵉ x`ᵉ witnessingᵉ thatᵉ theᵉ triangleᵉ

  ```text
                              αᵉ xᵉ *ᵉ
                  eᵉ (μᵉ xᵉ *ᵉ) -------->ᵉ μᵉ (eᵉ xᵉ) (eᵉ *ᵉ)
                        \ᵉ                 /ᵉ
                         \ᵉ               /ᵉ apᵉ (μᵉ (eᵉ xᵉ) -ᵉ) e₁ᵉ
                          \ᵉ             /ᵉ
                           \ᵉ           ∨ᵉ
    apᵉ eᵉ (right-unit-lawᵉ xᵉ) \ᵉ       μᵉ (eᵉ xᵉ) *ᵉ
                             \ᵉ       /ᵉ
                              \ᵉ     /ᵉ right-unit-lawᵉ (eᵉ xᵉ)
                               \ᵉ   /ᵉ
                                ∨ᵉ ∨ᵉ
                                eᵉ xᵉ
  ```

  commutes.ᵉ

-ᵉ Anᵉ identificationᵉ `α₃`ᵉ witnessingᵉ thatᵉ theᵉ squareᵉ

  ```text
                                                     α₁ᵉ
     α₀ᵉ *ᵉ *ᵉ ∙ᵉ (apᵉ (μᵉ -ᵉ (eᵉ *ᵉ)) e₁ᵉ ∙ᵉ left-unit-lawᵉ *ᵉ) --->ᵉ apᵉ eᵉ (left-unit-lawᵉ *ᵉ)
                       |                                         |
         (α₀ᵉ *ᵉ *ᵉ) ·lᵉ βᵉ |                                         |
                       ∨ᵉ                                         ∨ᵉ
    α₀ᵉ *ᵉ *ᵉ ∙ᵉ (apᵉ (μᵉ (eᵉ *ᵉ) -ᵉ) e₁ᵉ ∙ᵉ right-unit-lawᵉ *ᵉ) --->ᵉ apᵉ eᵉ (right-unit-lawᵉ *ᵉ)
                                                     α₂ᵉ
  ```

  Here,ᵉ theᵉ identificationᵉ onᵉ theᵉ leftᵉ isᵉ obtainedᵉ byᵉ leftᵉ whiskeringᵉ theᵉ
  identificationᵉ witnessingᵉ thatᵉ theᵉ squareᵉ

  ```text
                               apᵉ (μᵉ (eᵉ *ᵉ)) e₁ᵉ
                μᵉ (eᵉ *ᵉ) (eᵉ *ᵉ) ----------------->ᵉ μᵉ (eᵉ *ᵉ) *ᵉ
                      |                               |
    apᵉ (μᵉ -ᵉ (eᵉ *ᵉ)) e₁ᵉ |                 βᵉ             | right-unit-lawᵉ (eᵉ *ᵉ)
                      ∨ᵉ                               ∨ᵉ
                   μᵉ *ᵉ (eᵉ *ᵉ) ---------------------->ᵉ eᵉ *ᵉ
                               left-unit-lawᵉ (eᵉ *ᵉ)
  ```

  commutes,ᵉ with theᵉ identificationᵉ `αᵉ *ᵉ *ᵉ : eᵉ (μᵉ *ᵉ *ᵉ) ＝ᵉ μᵉ (eᵉ *ᵉ) (eᵉ *)`.ᵉ Theᵉ
  quickestᵉ wayᵉ to seeᵉ thatᵉ thisᵉ squareᵉ commutesᵉ isᵉ byᵉ identificationᵉ eliminationᵉ
  onᵉ theᵉ identificationᵉ `e₁ᵉ : eᵉ *ᵉ ＝ᵉ *`,ᵉ using theᵉ coherenceᵉ
  `left-unit-lawᵉ *ᵉ ＝ᵉ right-unit-lawᵉ *`.ᵉ Alternatively,ᵉ noteᵉ thatᵉ allᵉ theᵉ
  squaresᵉ in theᵉ diagramᵉ

  ```text
                               apᵉ (μᵉ (eᵉ *ᵉ)) e₁ᵉ
                μᵉ (eᵉ *ᵉ) (eᵉ *ᵉ) ----------------->ᵉ μᵉ (eᵉ *ᵉ) *ᵉ -------->ᵉ eᵉ *ᵉ
                      |                               |               |
    apᵉ (μᵉ -ᵉ (eᵉ *ᵉ)) e₁ᵉ |                 apᵉ (μᵉ -ᵉ *ᵉ) e₁ᵉ |               |
                      ∨ᵉ                               ∨ᵉ               ∨ᵉ
                   μᵉ *ᵉ (eᵉ *ᵉ) --------------------->ᵉ μᵉ *ᵉ *ᵉ ---------->ᵉ *ᵉ
                      |            apᵉ (μᵉ *ᵉ) e₁ᵉ        |               |
                      |                               |  cohᵉ ·rᵉ reflᵉ  | reflᵉ
                      ∨ᵉ                               ∨ᵉ               ∨ᵉ
                     eᵉ *ᵉ --------------------------->ᵉ *ᵉ ------------>ᵉ *ᵉ
                                       e₁ᵉ                  reflᵉ
  ```

  commute.ᵉ Thereforeᵉ weᵉ obtainᵉ anᵉ identificationᵉ

  ```text
    apᵉ (μᵉ -ᵉ (eᵉ *ᵉ)) e₁ᵉ ∙ᵉ (left-unit-lawᵉ (eᵉ *ᵉ) ∙ᵉ e₁ᵉ) ＝ᵉ
    apᵉ (μᵉ (eᵉ *ᵉ) -ᵉ) e₁ᵉ ∙ᵉ (right-unit-lawᵉ (eᵉ *ᵉ) ∙ᵉ e₁).ᵉ
  ```

  Byᵉ unwhiskeringᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ identifications,ᵉ i.e.,ᵉ byᵉ cancellingᵉ
  outᵉ `e₁`ᵉ onᵉ bothᵉ sides,ᵉ itᵉ followsᵉ thatᵉ theᵉ assertedᵉ squareᵉ commutes.ᵉ

## Definition

### The predicate of preserving H-space structure on a pointed type

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : H-Spaceᵉ l1ᵉ) (Nᵉ : H-Spaceᵉ l2ᵉ)
  where

  preserves-mul-pointed-equiv-H-Spaceᵉ :
    (pointed-type-H-Spaceᵉ Mᵉ ≃∗ᵉ pointed-type-H-Spaceᵉ Nᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-mul-pointed-equiv-H-Spaceᵉ eᵉ =
    preserves-mul-pointed-map-H-Spaceᵉ Mᵉ Nᵉ (pointed-map-pointed-equivᵉ eᵉ)

  preserves-left-unit-law-mul-pointed-equiv-H-Spaceᵉ :
    (eᵉ : pointed-type-H-Spaceᵉ Mᵉ ≃∗ᵉ pointed-type-H-Spaceᵉ Nᵉ) →
    preserves-mul-pointed-equiv-H-Spaceᵉ eᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-left-unit-law-mul-pointed-equiv-H-Spaceᵉ eᵉ =
    preserves-left-unit-law-mul-pointed-map-H-Spaceᵉ Mᵉ Nᵉ
      ( pointed-map-pointed-equivᵉ eᵉ)

  preserves-right-unit-law-mul-pointed-equiv-H-Spaceᵉ :
    (eᵉ : pointed-type-H-Spaceᵉ Mᵉ ≃∗ᵉ pointed-type-H-Spaceᵉ Nᵉ) →
    preserves-mul-pointed-equiv-H-Spaceᵉ eᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-right-unit-law-mul-pointed-equiv-H-Spaceᵉ eᵉ =
    preserves-right-unit-law-mul-pointed-map-H-Spaceᵉ Mᵉ Nᵉ
      ( pointed-map-pointed-equivᵉ eᵉ)

  preserves-coherence-unit-laws-mul-pointed-equiv-H-Spaceᵉ :
    (eᵉ : pointed-type-H-Spaceᵉ Mᵉ ≃∗ᵉ pointed-type-H-Spaceᵉ Nᵉ) →
    (μᵉ : preserves-mul-pointed-equiv-H-Spaceᵉ eᵉ) →
    (νᵉ : preserves-left-unit-law-mul-pointed-equiv-H-Spaceᵉ eᵉ μᵉ) →
    (ρᵉ : preserves-right-unit-law-mul-pointed-equiv-H-Spaceᵉ eᵉ μᵉ) → UUᵉ l2ᵉ
  preserves-coherence-unit-laws-mul-pointed-equiv-H-Spaceᵉ eᵉ =
    preserves-coherence-unit-laws-mul-pointed-map-H-Spaceᵉ Mᵉ Nᵉ
      ( pointed-map-pointed-equivᵉ eᵉ)

  preserves-unital-mul-pointed-equiv-H-Spaceᵉ :
    (eᵉ : pointed-type-H-Spaceᵉ Mᵉ ≃∗ᵉ pointed-type-H-Spaceᵉ Nᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-unital-mul-pointed-equiv-H-Spaceᵉ eᵉ =
    preserves-unital-mul-pointed-map-H-Spaceᵉ Mᵉ Nᵉ (pointed-map-pointed-equivᵉ eᵉ)
```

### Equivalences of H-spaces

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : H-Spaceᵉ l1ᵉ) (Nᵉ : H-Spaceᵉ l2ᵉ)
  where

  equiv-H-Spaceᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equiv-H-Spaceᵉ =
    Σᵉ ( pointed-type-H-Spaceᵉ Mᵉ ≃∗ᵉ pointed-type-H-Spaceᵉ Nᵉ)
      ( preserves-unital-mul-pointed-equiv-H-Spaceᵉ Mᵉ Nᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Mᵉ : H-Spaceᵉ l1ᵉ} {Nᵉ : H-Spaceᵉ l2ᵉ} (eᵉ : equiv-H-Spaceᵉ Mᵉ Nᵉ)
  where

  pointed-equiv-equiv-H-Spaceᵉ : pointed-type-H-Spaceᵉ Mᵉ ≃∗ᵉ pointed-type-H-Spaceᵉ Nᵉ
  pointed-equiv-equiv-H-Spaceᵉ = pr1ᵉ eᵉ

  map-equiv-H-Spaceᵉ : type-H-Spaceᵉ Mᵉ → type-H-Spaceᵉ Nᵉ
  map-equiv-H-Spaceᵉ = map-pointed-equivᵉ pointed-equiv-equiv-H-Spaceᵉ

  preserves-unit-equiv-H-Spaceᵉ :
    map-equiv-H-Spaceᵉ (unit-H-Spaceᵉ Mᵉ) ＝ᵉ unit-H-Spaceᵉ Nᵉ
  preserves-unit-equiv-H-Spaceᵉ =
    preserves-point-pointed-equivᵉ pointed-equiv-equiv-H-Spaceᵉ

  preserves-unital-mul-equiv-H-Spaceᵉ :
    preserves-unital-mul-pointed-equiv-H-Spaceᵉ Mᵉ Nᵉ pointed-equiv-equiv-H-Spaceᵉ
  preserves-unital-mul-equiv-H-Spaceᵉ = pr2ᵉ eᵉ

  preserves-mul-equiv-H-Spaceᵉ :
    preserves-mul-pointed-equiv-H-Spaceᵉ Mᵉ Nᵉ pointed-equiv-equiv-H-Spaceᵉ
  preserves-mul-equiv-H-Spaceᵉ =
    pr1ᵉ preserves-unital-mul-equiv-H-Spaceᵉ

  preserves-left-unit-law-mul-equiv-H-Spaceᵉ :
    preserves-left-unit-law-mul-pointed-equiv-H-Spaceᵉ Mᵉ Nᵉ
      ( pointed-equiv-equiv-H-Spaceᵉ)
      ( preserves-mul-equiv-H-Spaceᵉ)
  preserves-left-unit-law-mul-equiv-H-Spaceᵉ =
    pr1ᵉ (pr2ᵉ preserves-unital-mul-equiv-H-Spaceᵉ)

  preserves-right-unit-law-mul-equiv-H-Spaceᵉ :
    preserves-right-unit-law-mul-pointed-equiv-H-Spaceᵉ Mᵉ Nᵉ
      ( pointed-equiv-equiv-H-Spaceᵉ)
      ( preserves-mul-equiv-H-Spaceᵉ)
  preserves-right-unit-law-mul-equiv-H-Spaceᵉ =
    pr1ᵉ (pr2ᵉ (pr2ᵉ preserves-unital-mul-equiv-H-Spaceᵉ))

  preserves-coherence-unit-laws-mul-equiv-H-Spaceᵉ :
    preserves-coherence-unit-laws-mul-pointed-equiv-H-Spaceᵉ Mᵉ Nᵉ
      ( pointed-equiv-equiv-H-Spaceᵉ)
      ( preserves-mul-equiv-H-Spaceᵉ)
      ( preserves-left-unit-law-mul-equiv-H-Spaceᵉ)
      ( preserves-right-unit-law-mul-equiv-H-Spaceᵉ)
  preserves-coherence-unit-laws-mul-equiv-H-Spaceᵉ =
    pr2ᵉ (pr2ᵉ (pr2ᵉ preserves-unital-mul-equiv-H-Spaceᵉ))
```