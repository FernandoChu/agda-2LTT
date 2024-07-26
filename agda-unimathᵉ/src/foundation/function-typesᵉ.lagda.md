# Function types

```agda
module foundation.function-typesᵉ where

open import foundation-core.function-typesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.dependent-identificationsᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Properties

### Transport in a family of function types

Considerᵉ twoᵉ typeᵉ familiesᵉ `B`ᵉ andᵉ `C`ᵉ overᵉ `A`,ᵉ anᵉ identificationᵉ `pᵉ : xᵉ ＝ᵉ y`ᵉ
in `A`ᵉ andᵉ twoᵉ functionsᵉ

```text
  fᵉ : Bᵉ xᵉ → Cᵉ xᵉ
  gᵉ : Bᵉ yᵉ → Cᵉ y.ᵉ
```

Thenᵉ theᵉ typeᵉ ofᵉ dependentᵉ identificationsᵉ fromᵉ `f`ᵉ to `g`ᵉ overᵉ `p`ᵉ canᵉ beᵉ
computedᵉ asᵉ

```text
  ((bᵉ : Bᵉ xᵉ) → trᵉ Cᵉ pᵉ (fᵉ bᵉ) ＝ᵉ gᵉ (trᵉ Bᵉ pᵉ bᵉ))
  ≃ᵉ dependent-identificationᵉ (xᵉ ↦ᵉ Bᵉ xᵉ → Cᵉ xᵉ) fᵉ g.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ : Aᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : Aᵉ → UUᵉ l3ᵉ)
  where

  tr-function-typeᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (fᵉ : Bᵉ xᵉ → Cᵉ xᵉ) →
    trᵉ (λ aᵉ → Bᵉ aᵉ → Cᵉ aᵉ) pᵉ fᵉ ＝ᵉ (trᵉ Cᵉ pᵉ ∘ᵉ (fᵉ ∘ᵉ trᵉ Bᵉ (invᵉ pᵉ)))
  tr-function-typeᵉ reflᵉ fᵉ = reflᵉ

  compute-dependent-identification-function-typeᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (fᵉ : Bᵉ xᵉ → Cᵉ xᵉ) (gᵉ : Bᵉ yᵉ → Cᵉ yᵉ) →
    ((bᵉ : Bᵉ xᵉ) → trᵉ Cᵉ pᵉ (fᵉ bᵉ) ＝ᵉ gᵉ (trᵉ Bᵉ pᵉ bᵉ)) ≃ᵉ
    dependent-identificationᵉ (λ aᵉ → Bᵉ aᵉ → Cᵉ aᵉ) pᵉ fᵉ gᵉ
  compute-dependent-identification-function-typeᵉ reflᵉ fᵉ gᵉ =
    inv-equivᵉ equiv-funextᵉ

  map-compute-dependent-identification-function-typeᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (fᵉ : Bᵉ xᵉ → Cᵉ xᵉ) (gᵉ : Bᵉ yᵉ → Cᵉ yᵉ) →
    ((bᵉ : Bᵉ xᵉ) → trᵉ Cᵉ pᵉ (fᵉ bᵉ) ＝ᵉ gᵉ (trᵉ Bᵉ pᵉ bᵉ)) →
    dependent-identificationᵉ (λ aᵉ → Bᵉ aᵉ → Cᵉ aᵉ) pᵉ fᵉ gᵉ
  map-compute-dependent-identification-function-typeᵉ pᵉ fᵉ gᵉ =
    map-equivᵉ (compute-dependent-identification-function-typeᵉ pᵉ fᵉ gᵉ)
```

### Transport in a family of function types with fixed codomain

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ : Aᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : UUᵉ l3ᵉ)
  where

  compute-dependent-identification-function-type-fixed-codomainᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (fᵉ : Bᵉ xᵉ → Cᵉ) (gᵉ : Bᵉ yᵉ → Cᵉ) →
    ((bᵉ : Bᵉ xᵉ) → fᵉ bᵉ ＝ᵉ gᵉ (trᵉ Bᵉ pᵉ bᵉ)) ≃ᵉ
    dependent-identificationᵉ (λ aᵉ → Bᵉ aᵉ → Cᵉ) pᵉ fᵉ gᵉ
  compute-dependent-identification-function-type-fixed-codomainᵉ reflᵉ fᵉ gᵉ =
    inv-equivᵉ equiv-funextᵉ

  map-compute-dependent-identification-function-type-fixed-codomainᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (fᵉ : Bᵉ xᵉ → Cᵉ) (gᵉ : Bᵉ yᵉ → Cᵉ) →
    ((bᵉ : Bᵉ xᵉ) → fᵉ bᵉ ＝ᵉ gᵉ (trᵉ Bᵉ pᵉ bᵉ)) →
    dependent-identificationᵉ (λ aᵉ → Bᵉ aᵉ → Cᵉ) pᵉ fᵉ gᵉ
  map-compute-dependent-identification-function-type-fixed-codomainᵉ pᵉ fᵉ gᵉ =
    map-equivᵉ
      ( compute-dependent-identification-function-type-fixed-codomainᵉ pᵉ fᵉ gᵉ)
```

### Relation between `compute-dependent-identification-function-type` and `preserves-tr`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {i0ᵉ i1ᵉ : Iᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
  (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ)
  where

  preserves-tr-apd-functionᵉ :
    (pᵉ : i0ᵉ ＝ᵉ i1ᵉ) (aᵉ : Aᵉ i0ᵉ) →
    map-inv-equivᵉ
      ( compute-dependent-identification-function-typeᵉ Aᵉ Bᵉ pᵉ (fᵉ i0ᵉ) (fᵉ i1ᵉ))
      ( apdᵉ fᵉ pᵉ) aᵉ ＝ᵉ
    inv-htpyᵉ (preserves-trᵉ fᵉ pᵉ) aᵉ
  preserves-tr-apd-functionᵉ reflᵉ = refl-htpyᵉ
```

### Computation of dependent identifications of functions over homotopies

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  { Sᵉ : UUᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} {Pᵉ : Xᵉ → UUᵉ l3ᵉ} (Yᵉ : UUᵉ l4ᵉ)
  { iᵉ : Sᵉ → Xᵉ}
  where

  equiv-htpy-dependent-function-dependent-identification-function-typeᵉ :
    { jᵉ : Sᵉ → Xᵉ} (Hᵉ : iᵉ ~ᵉ jᵉ) →
    ( kᵉ : (sᵉ : Sᵉ) → Pᵉ (iᵉ sᵉ) → Yᵉ)
    ( lᵉ : (sᵉ : Sᵉ) → Pᵉ (jᵉ sᵉ) → Yᵉ) →
    ( sᵉ : Sᵉ) →
    ( kᵉ sᵉ ~ᵉ (lᵉ sᵉ ∘ᵉ trᵉ Pᵉ (Hᵉ sᵉ))) ≃ᵉ
    ( dependent-identificationᵉ
      ( λ xᵉ → Pᵉ xᵉ → Yᵉ)
      ( Hᵉ sᵉ)
      ( kᵉ sᵉ)
      ( lᵉ sᵉ))
  equiv-htpy-dependent-function-dependent-identification-function-typeᵉ =
    ind-htpyᵉ iᵉ
      ( λ jᵉ Hᵉ →
        ( kᵉ : (sᵉ : Sᵉ) → Pᵉ (iᵉ sᵉ) → Yᵉ) →
        ( lᵉ : (sᵉ : Sᵉ) → Pᵉ (jᵉ sᵉ) → Yᵉ) →
        ( sᵉ : Sᵉ) →
        ( kᵉ sᵉ ~ᵉ (lᵉ sᵉ ∘ᵉ trᵉ Pᵉ (Hᵉ sᵉ))) ≃ᵉ
        ( dependent-identificationᵉ
          ( λ xᵉ → Pᵉ xᵉ → Yᵉ)
          ( Hᵉ sᵉ)
          ( kᵉ sᵉ)
          ( lᵉ sᵉ)))
      ( λ kᵉ lᵉ sᵉ → inv-equivᵉ (equiv-funextᵉ))

  compute-equiv-htpy-dependent-function-dependent-identification-function-typeᵉ :
    { jᵉ : Sᵉ → Xᵉ} (Hᵉ : iᵉ ~ᵉ jᵉ) →
    ( hᵉ : (xᵉ : Xᵉ) → Pᵉ xᵉ → Yᵉ) →
    ( sᵉ : Sᵉ) →
    ( map-equivᵉ
      ( equiv-htpy-dependent-function-dependent-identification-function-typeᵉ Hᵉ
        ( hᵉ ∘ᵉ iᵉ)
        ( hᵉ ∘ᵉ jᵉ)
        ( sᵉ))
      ( λ tᵉ → apᵉ (ind-Σᵉ hᵉ) (eq-pair-Σᵉ (Hᵉ sᵉ) reflᵉ))) ＝ᵉ
    ( apdᵉ hᵉ (Hᵉ sᵉ))
  compute-equiv-htpy-dependent-function-dependent-identification-function-typeᵉ =
    ind-htpyᵉ iᵉ
      ( λ jᵉ Hᵉ →
        ( hᵉ : (xᵉ : Xᵉ) → Pᵉ xᵉ → Yᵉ) →
        ( sᵉ : Sᵉ) →
        ( map-equivᵉ
          ( equiv-htpy-dependent-function-dependent-identification-function-typeᵉ
            ( Hᵉ)
            ( hᵉ ∘ᵉ iᵉ)
            ( hᵉ ∘ᵉ jᵉ)
            ( sᵉ))
          ( λ tᵉ → apᵉ (ind-Σᵉ hᵉ) (eq-pair-Σᵉ (Hᵉ sᵉ) reflᵉ))) ＝ᵉ
        ( apdᵉ hᵉ (Hᵉ sᵉ)))
      ( λ hᵉ sᵉ →
        ( apᵉ
          ( λ fᵉ → map-equivᵉ (fᵉ (hᵉ ∘ᵉ iᵉ) (hᵉ ∘ᵉ iᵉ) sᵉ) refl-htpyᵉ)
          ( compute-ind-htpyᵉ iᵉ
            ( λ jᵉ Hᵉ →
              ( kᵉ : (sᵉ : Sᵉ) → Pᵉ (iᵉ sᵉ) → Yᵉ) →
              ( lᵉ : (sᵉ : Sᵉ) → Pᵉ (jᵉ sᵉ) → Yᵉ) →
              ( sᵉ : Sᵉ) →
              ( kᵉ sᵉ ~ᵉ (lᵉ sᵉ ∘ᵉ trᵉ Pᵉ (Hᵉ sᵉ))) ≃ᵉ
              ( dependent-identificationᵉ
                ( λ xᵉ → Pᵉ xᵉ → Yᵉ)
                ( Hᵉ sᵉ)
                ( kᵉ sᵉ)
                ( lᵉ sᵉ)))
            ( λ kᵉ lᵉ sᵉ → inv-equivᵉ (equiv-funextᵉ)))) ∙ᵉ
        ( eq-htpy-refl-htpyᵉ (hᵉ (iᵉ sᵉ))))
```

## See also

### Table of files about function types, composition, and equivalences

{{#includeᵉ tables/composition.mdᵉ}}