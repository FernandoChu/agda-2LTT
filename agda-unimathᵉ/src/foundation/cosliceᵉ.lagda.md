# Morphisms in the coslice category of types

```agda
module foundation.cosliceᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-homotopiesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ spanᵉ ofᵉ mapsᵉ

```text
      Xᵉ
     /ᵉ \ᵉ
  fᵉ /ᵉ   \ᵉ gᵉ
   ∨ᵉ     ∨ᵉ
  Aᵉ       B,ᵉ
```

weᵉ defineᵉ aᵉ morphismᵉ betweenᵉ theᵉ mapsᵉ in theᵉ cosliceᵉ categoryᵉ ofᵉ typesᵉ to beᵉ aᵉ
mapᵉ `hᵉ : Aᵉ → B`ᵉ togetherᵉ with aᵉ coherenceᵉ triangleᵉ `(hᵉ ∘ᵉ fᵉ) ~ᵉ g`ᵉ:

```text
      Xᵉ
     /ᵉ \ᵉ
  fᵉ /ᵉ   \ᵉ gᵉ
   ∨ᵉ     ∨ᵉ
  Aᵉ ---->ᵉ B.ᵉ
      hᵉ
```

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} (fᵉ : Xᵉ → Aᵉ) (gᵉ : Xᵉ → Bᵉ)
  where

  hom-cosliceᵉ = Σᵉ (Aᵉ → Bᵉ) (λ hᵉ → hᵉ ∘ᵉ fᵉ ~ᵉ gᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {fᵉ : Xᵉ → Aᵉ} {gᵉ : Xᵉ → Bᵉ}
  where

  map-hom-cosliceᵉ : hom-cosliceᵉ fᵉ gᵉ → Aᵉ → Bᵉ
  map-hom-cosliceᵉ = pr1ᵉ

  triangle-hom-cosliceᵉ :
    (hᵉ : hom-cosliceᵉ fᵉ gᵉ) → map-hom-cosliceᵉ hᵉ ∘ᵉ fᵉ ~ᵉ gᵉ
  triangle-hom-cosliceᵉ = pr2ᵉ
```

## Properties

### Characterizing the identity type of coslice morphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {fᵉ : Xᵉ → Aᵉ} {gᵉ : Xᵉ → Bᵉ}
  where

  coherence-htpy-hom-cosliceᵉ :
    (hᵉ kᵉ : hom-cosliceᵉ fᵉ gᵉ) →
    map-hom-cosliceᵉ hᵉ ~ᵉ map-hom-cosliceᵉ kᵉ → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  coherence-htpy-hom-cosliceᵉ hᵉ kᵉ Hᵉ =
    coherence-triangle-homotopiesᵉ
      ( triangle-hom-cosliceᵉ hᵉ)
      ( triangle-hom-cosliceᵉ kᵉ)
      ( Hᵉ ·rᵉ fᵉ)

  htpy-hom-cosliceᵉ :
    (hᵉ kᵉ : hom-cosliceᵉ fᵉ gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  htpy-hom-cosliceᵉ hᵉ kᵉ =
    Σᵉ ( map-hom-cosliceᵉ hᵉ ~ᵉ map-hom-cosliceᵉ kᵉ)
      ( coherence-htpy-hom-cosliceᵉ hᵉ kᵉ)

  extensionality-hom-cosliceᵉ :
    (hᵉ kᵉ : hom-cosliceᵉ fᵉ gᵉ) → (hᵉ ＝ᵉ kᵉ) ≃ᵉ htpy-hom-cosliceᵉ hᵉ kᵉ
  extensionality-hom-cosliceᵉ (hᵉ ,ᵉ Hᵉ) =
    extensionality-Σᵉ
      ( λ {h'ᵉ : Aᵉ → Bᵉ} (H'ᵉ : h'ᵉ ∘ᵉ fᵉ ~ᵉ gᵉ) (Kᵉ : hᵉ ~ᵉ h'ᵉ) → Hᵉ ~ᵉ ((Kᵉ ·rᵉ fᵉ) ∙hᵉ H'ᵉ))
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( λ h'ᵉ → equiv-funextᵉ)
      ( λ H'ᵉ → equiv-funextᵉ)

  eq-htpy-hom-cosliceᵉ :
    ( hᵉ kᵉ : hom-cosliceᵉ fᵉ gᵉ)
    ( Hᵉ : map-hom-cosliceᵉ hᵉ ~ᵉ map-hom-cosliceᵉ kᵉ)
    ( Kᵉ : coherence-htpy-hom-cosliceᵉ hᵉ kᵉ Hᵉ) →
    hᵉ ＝ᵉ kᵉ
  eq-htpy-hom-cosliceᵉ hᵉ kᵉ Hᵉ Kᵉ =
    map-inv-equivᵉ (extensionality-hom-cosliceᵉ hᵉ kᵉ) (Hᵉ ,ᵉ Kᵉ)
```