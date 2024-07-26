# Fibered dependent type theories

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module type-theories.fibered-dependent-type-theoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import type-theories.dependent-type-theoriesᵉ
```

</details>

## Bifibered systems

```agda
open dependentᵉ
module fiberedᵉ where

  record bifibered-systemᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (l7ᵉ l8ᵉ : Level) {Aᵉ : systemᵉ l1ᵉ l2ᵉ}
    (Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ) (Cᵉ : fibered-systemᵉ l5ᵉ l6ᵉ Aᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ lsuc l7ᵉ ⊔ lsuc l8ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ)
        (Zᵉ : fibered-system.typeᵉ Cᵉ Xᵉ) → UUᵉ l7ᵉ
      elementᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} {Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ}
        {Zᵉ : fibered-system.typeᵉ Cᵉ Xᵉ} {xᵉ : system.elementᵉ Aᵉ Xᵉ}
        (Wᵉ : typeᵉ Yᵉ Zᵉ) (yᵉ : fibered-system.elementᵉ Bᵉ Yᵉ xᵉ)
        (zᵉ : fibered-system.elementᵉ Cᵉ Zᵉ xᵉ) → UUᵉ l8ᵉ
      sliceᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} {Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ}
        {Zᵉ : fibered-system.typeᵉ Cᵉ Xᵉ} → typeᵉ Yᵉ Zᵉ →
        bifibered-systemᵉ l7ᵉ l8ᵉ
          ( fibered-system.sliceᵉ Bᵉ Yᵉ)
          ( fibered-system.sliceᵉ Cᵉ Zᵉ)

  total-fibered-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ}
    {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ} {Cᵉ : fibered-systemᵉ l5ᵉ l6ᵉ Aᵉ}
    (Dᵉ : bifibered-systemᵉ l7ᵉ l8ᵉ Bᵉ Cᵉ) →
    fibered-systemᵉ (l5ᵉ ⊔ l7ᵉ) (l6ᵉ ⊔ l8ᵉ) (total-systemᵉ Aᵉ Bᵉ)
  fibered-system.typeᵉ (total-fibered-systemᵉ {Cᵉ = Cᵉ} Dᵉ) Xᵉ =
    Σᵉ (fibered-system.typeᵉ Cᵉ (pr1ᵉ Xᵉ)) (bifibered-system.typeᵉ Dᵉ (pr2ᵉ Xᵉ))
  fibered-system.elementᵉ (total-fibered-systemᵉ {Cᵉ = Cᵉ} Dᵉ)
    {pairᵉ Xᵉ Yᵉ} (pairᵉ Zᵉ Wᵉ) (pairᵉ xᵉ yᵉ) =
    Σᵉ (fibered-system.elementᵉ Cᵉ Zᵉ xᵉ) (bifibered-system.elementᵉ Dᵉ Wᵉ yᵉ)
  fibered-system.sliceᵉ (total-fibered-systemᵉ Dᵉ) {pairᵉ Xᵉ Yᵉ} (pairᵉ Zᵉ Wᵉ) =
    total-fibered-systemᵉ (bifibered-system.sliceᵉ Dᵉ Wᵉ)

  record section-fibered-systemᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ}
    {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ} {Cᵉ : fibered-systemᵉ l5ᵉ l6ᵉ Aᵉ}
    (fᵉ : section-systemᵉ Cᵉ) (Dᵉ : bifibered-systemᵉ l7ᵉ l8ᵉ Bᵉ Cᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l7ᵉ ⊔ l8ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        bifibered-system.typeᵉ Dᵉ Yᵉ (section-system.typeᵉ fᵉ Xᵉ)
      elementᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} {Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ} →
        {xᵉ : system.elementᵉ Aᵉ Xᵉ} (yᵉ : fibered-system.elementᵉ Bᵉ Yᵉ xᵉ) →
        bifibered-system.elementᵉ Dᵉ
          ( typeᵉ Yᵉ)
          ( yᵉ)
          ( section-system.elementᵉ fᵉ xᵉ)
      sliceᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        section-fibered-systemᵉ
          ( section-system.sliceᵉ fᵉ Xᵉ)
          ( bifibered-system.sliceᵉ Dᵉ (typeᵉ Yᵉ))

  total-section-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ}
    {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ} {Cᵉ : fibered-systemᵉ l5ᵉ l6ᵉ Aᵉ}
    {Dᵉ : bifibered-systemᵉ l7ᵉ l8ᵉ Bᵉ Cᵉ} {fᵉ : section-systemᵉ Cᵉ}
    (gᵉ : section-fibered-systemᵉ fᵉ Dᵉ) →
    section-systemᵉ (total-fibered-systemᵉ Dᵉ)
  section-system.typeᵉ (total-section-systemᵉ {fᵉ = fᵉ} gᵉ) (pairᵉ Xᵉ Yᵉ) =
    pairᵉ (section-system.typeᵉ fᵉ Xᵉ) (section-fibered-system.typeᵉ gᵉ Yᵉ)
  section-system.elementᵉ (total-section-systemᵉ {fᵉ = fᵉ} gᵉ)
    {pairᵉ Xᵉ Yᵉ} (pairᵉ xᵉ yᵉ) =
    pairᵉ (section-system.elementᵉ fᵉ xᵉ) (section-fibered-system.elementᵉ gᵉ yᵉ)
  section-system.sliceᵉ (total-section-systemᵉ gᵉ) (pairᵉ Xᵉ Yᵉ) =
    total-section-systemᵉ (section-fibered-system.sliceᵉ gᵉ Yᵉ)
```

### Homotopies of sections of fibered systems

```agda
  double-trᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
    (Dᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ → UUᵉ l4ᵉ) {xᵉ yᵉ : Aᵉ} (pᵉ : Idᵉ xᵉ yᵉ)
    {uᵉ : Bᵉ xᵉ} {u'ᵉ : Bᵉ yᵉ} (qᵉ : Idᵉ (trᵉ Bᵉ pᵉ uᵉ) u'ᵉ) {vᵉ : Cᵉ xᵉ} {v'ᵉ : Cᵉ yᵉ}
    (rᵉ : Idᵉ (trᵉ Cᵉ pᵉ vᵉ) v'ᵉ) → Dᵉ xᵉ uᵉ vᵉ → Dᵉ yᵉ u'ᵉ v'ᵉ
  double-trᵉ Dᵉ reflᵉ reflᵉ reflᵉ dᵉ = dᵉ

  tr-bifibered-system-sliceᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ}
    {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ} {Cᵉ : fibered-systemᵉ l5ᵉ l6ᵉ Aᵉ}
    (Dᵉ : bifibered-systemᵉ l7ᵉ l8ᵉ Bᵉ Cᵉ) {Xᵉ : system.typeᵉ Aᵉ}
    (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) {Zᵉ Z'ᵉ : fibered-system.typeᵉ Cᵉ Xᵉ}
    {dᵉ : bifibered-system.typeᵉ Dᵉ Yᵉ Zᵉ} {d'ᵉ : bifibered-system.typeᵉ Dᵉ Yᵉ Z'ᵉ}
    (pᵉ : Idᵉ Zᵉ Z'ᵉ) (qᵉ : Idᵉ (trᵉ (bifibered-system.typeᵉ Dᵉ Yᵉ) pᵉ dᵉ) d'ᵉ) →
    Idᵉ
      ( trᵉ
        ( bifibered-systemᵉ l7ᵉ l8ᵉ (fibered-system.sliceᵉ Bᵉ Yᵉ))
        ( apᵉ (fibered-system.sliceᵉ Cᵉ) pᵉ)
        ( bifibered-system.sliceᵉ Dᵉ dᵉ))
      ( bifibered-system.sliceᵉ Dᵉ (trᵉ (bifibered-system.typeᵉ Dᵉ Yᵉ) pᵉ dᵉ))
  tr-bifibered-system-sliceᵉ Dᵉ Yᵉ reflᵉ reflᵉ = reflᵉ

  Eq-bifibered-system'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ}
    {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ} {Cᵉ C'ᵉ : fibered-systemᵉ l5ᵉ l6ᵉ Aᵉ}
    (Dᵉ : bifibered-systemᵉ l7ᵉ l8ᵉ Bᵉ Cᵉ) (D'ᵉ : bifibered-systemᵉ l7ᵉ l8ᵉ Bᵉ C'ᵉ)
    (αᵉ : Idᵉ Cᵉ C'ᵉ) (βᵉ : Idᵉ (trᵉ (bifibered-systemᵉ l7ᵉ l8ᵉ Bᵉ) αᵉ Dᵉ) D'ᵉ)
    (fᵉ : section-systemᵉ Cᵉ) (f'ᵉ : section-systemᵉ C'ᵉ)
    (gᵉ : section-fibered-systemᵉ fᵉ Dᵉ) (g'ᵉ : section-fibered-systemᵉ f'ᵉ D'ᵉ) →
    bifibered-systemᵉ l7ᵉ l8ᵉ Bᵉ (Eq-fibered-system'ᵉ αᵉ fᵉ f'ᵉ)
  bifibered-system.typeᵉ
    ( Eq-bifibered-system'ᵉ Dᵉ .Dᵉ reflᵉ reflᵉ fᵉ f'ᵉ gᵉ g'ᵉ) {Xᵉ} Yᵉ pᵉ =
    Idᵉ
      ( trᵉ (bifibered-system.typeᵉ Dᵉ Yᵉ) pᵉ (section-fibered-system.typeᵉ gᵉ Yᵉ))
      ( section-fibered-system.typeᵉ g'ᵉ Yᵉ)
  bifibered-system.elementᵉ
    ( Eq-bifibered-system'ᵉ {Aᵉ = Aᵉ} {Cᵉ = Cᵉ} Dᵉ .Dᵉ reflᵉ reflᵉ fᵉ f'ᵉ gᵉ g'ᵉ)
    {Xᵉ} {Yᵉ} {pᵉ} {xᵉ} αᵉ yᵉ qᵉ =
      Idᵉ
        ( double-trᵉ
          ( λ Zᵉ uᵉ → bifibered-system.elementᵉ Dᵉ {Zᵉ = Zᵉ} uᵉ yᵉ)
          ( pᵉ)
          ( αᵉ)
          ( qᵉ)
          ( section-fibered-system.elementᵉ gᵉ yᵉ))
        ( section-fibered-system.elementᵉ g'ᵉ yᵉ)
  bifibered-system.sliceᵉ
    ( Eq-bifibered-system'ᵉ {Cᵉ = Cᵉ} Dᵉ .Dᵉ reflᵉ reflᵉ fᵉ f'ᵉ gᵉ g'ᵉ) {Xᵉ} {Yᵉ} {αᵉ} βᵉ =
    Eq-bifibered-system'ᵉ
      ( bifibered-system.sliceᵉ Dᵉ (section-fibered-system.typeᵉ gᵉ Yᵉ))
      ( bifibered-system.sliceᵉ Dᵉ (section-fibered-system.typeᵉ g'ᵉ Yᵉ))
      ( apᵉ (fibered-system.sliceᵉ Cᵉ) αᵉ)
      ( tr-bifibered-system-sliceᵉ Dᵉ Yᵉ αᵉ βᵉ ∙ᵉ apᵉ (bifibered-system.sliceᵉ Dᵉ) βᵉ)
      ( section-system.sliceᵉ fᵉ Xᵉ)
      ( section-system.sliceᵉ f'ᵉ Xᵉ)
      ( section-fibered-system.sliceᵉ gᵉ Yᵉ)
      ( section-fibered-system.sliceᵉ g'ᵉ Yᵉ)

  htpy-section-fibered-system'ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ}
    {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ} {Cᵉ C'ᵉ : fibered-systemᵉ l5ᵉ l6ᵉ Aᵉ}
    {Dᵉ : bifibered-systemᵉ l7ᵉ l8ᵉ Bᵉ Cᵉ} {D'ᵉ : bifibered-systemᵉ l7ᵉ l8ᵉ Bᵉ C'ᵉ}
    {fᵉ : section-systemᵉ Cᵉ} {f'ᵉ : section-systemᵉ C'ᵉ}
    {αᵉ : Idᵉ Cᵉ C'ᵉ} (βᵉ : Idᵉ (trᵉ (bifibered-systemᵉ l7ᵉ l8ᵉ Bᵉ) αᵉ Dᵉ) D'ᵉ)
    (Hᵉ : htpy-section-system'ᵉ αᵉ fᵉ f'ᵉ)
    (gᵉ : section-fibered-systemᵉ fᵉ Dᵉ) (hᵉ : section-fibered-systemᵉ f'ᵉ D'ᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l7ᵉ ⊔ l8ᵉ)
  htpy-section-fibered-system'ᵉ {Dᵉ = Dᵉ} {D'ᵉ} {fᵉ} {f'ᵉ} {αᵉ} βᵉ Hᵉ gᵉ hᵉ =
    section-fibered-systemᵉ Hᵉ (Eq-bifibered-system'ᵉ Dᵉ D'ᵉ αᵉ βᵉ fᵉ f'ᵉ gᵉ hᵉ)

  htpy-section-fibered-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ}
    {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ} {Cᵉ : fibered-systemᵉ l5ᵉ l6ᵉ Aᵉ}
    {Dᵉ : bifibered-systemᵉ l7ᵉ l8ᵉ Bᵉ Cᵉ} {fᵉ f'ᵉ : section-systemᵉ Cᵉ}
    (Hᵉ : htpy-section-systemᵉ fᵉ f'ᵉ)
    (gᵉ : section-fibered-systemᵉ fᵉ Dᵉ) (hᵉ : section-fibered-systemᵉ f'ᵉ Dᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l7ᵉ ⊔ l8ᵉ)
  htpy-section-fibered-systemᵉ Hᵉ gᵉ hᵉ =
    htpy-section-fibered-system'ᵉ {αᵉ = reflᵉ} reflᵉ Hᵉ gᵉ hᵉ
```

### Morphisms of fibered systems

```agda
  constant-bifibered-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ}
    (Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ) {Cᵉ : systemᵉ l5ᵉ l6ᵉ}
    (Dᵉ : fibered-systemᵉ l7ᵉ l8ᵉ Cᵉ) →
    bifibered-systemᵉ l7ᵉ l8ᵉ Bᵉ (constant-fibered-systemᵉ Aᵉ Cᵉ)
  bifibered-system.typeᵉ (constant-bifibered-systemᵉ Bᵉ Dᵉ) Yᵉ Zᵉ =
    fibered-system.typeᵉ Dᵉ Zᵉ
  bifibered-system.elementᵉ (constant-bifibered-systemᵉ Bᵉ Dᵉ) {Zᵉ = Zᵉ} Wᵉ yᵉ zᵉ =
    fibered-system.elementᵉ Dᵉ Wᵉ zᵉ
  bifibered-system.sliceᵉ (constant-bifibered-systemᵉ Bᵉ Dᵉ) {Xᵉ = Xᵉ} {Yᵉ} {Zᵉ} Wᵉ =
    constant-bifibered-systemᵉ
      ( fibered-system.sliceᵉ Bᵉ Yᵉ)
      ( fibered-system.sliceᵉ Dᵉ Wᵉ)

  hom-fibered-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {A'ᵉ : systemᵉ l3ᵉ l4ᵉ}
    (fᵉ : hom-systemᵉ Aᵉ A'ᵉ) (Bᵉ : fibered-systemᵉ l5ᵉ l6ᵉ Aᵉ)
    (B'ᵉ : fibered-systemᵉ l7ᵉ l8ᵉ A'ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ)
  hom-fibered-systemᵉ fᵉ Bᵉ B'ᵉ =
    section-fibered-systemᵉ fᵉ (constant-bifibered-systemᵉ Bᵉ B'ᵉ)

  id-hom-fibered-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} (Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ) →
    hom-fibered-systemᵉ (id-hom-systemᵉ Aᵉ) Bᵉ Bᵉ
  section-fibered-system.typeᵉ (id-hom-fibered-systemᵉ Bᵉ) = idᵉ
  section-fibered-system.elementᵉ (id-hom-fibered-systemᵉ Bᵉ) = idᵉ
  section-fibered-system.sliceᵉ (id-hom-fibered-systemᵉ Bᵉ) Yᵉ =
    id-hom-fibered-systemᵉ (fibered-system.sliceᵉ Bᵉ Yᵉ)

  comp-hom-fibered-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ l10ᵉ l11ᵉ l12ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ} {Cᵉ : systemᵉ l5ᵉ l6ᵉ}
    {gᵉ : hom-systemᵉ Bᵉ Cᵉ} {fᵉ : hom-systemᵉ Aᵉ Bᵉ}
    {Dᵉ : fibered-systemᵉ l7ᵉ l8ᵉ Aᵉ} {Eᵉ : fibered-systemᵉ l9ᵉ l10ᵉ Bᵉ}
    {Fᵉ : fibered-systemᵉ l11ᵉ l12ᵉ Cᵉ}
    (kᵉ : hom-fibered-systemᵉ gᵉ Eᵉ Fᵉ) (hᵉ : hom-fibered-systemᵉ fᵉ Dᵉ Eᵉ) →
    hom-fibered-systemᵉ (comp-hom-systemᵉ gᵉ fᵉ) Dᵉ Fᵉ
  section-fibered-system.typeᵉ (comp-hom-fibered-systemᵉ kᵉ hᵉ) Yᵉ =
    section-fibered-system.typeᵉ kᵉ
      ( section-fibered-system.typeᵉ hᵉ Yᵉ)
  section-fibered-system.elementᵉ (comp-hom-fibered-systemᵉ kᵉ hᵉ) yᵉ =
    section-fibered-system.elementᵉ kᵉ
      ( section-fibered-system.elementᵉ hᵉ yᵉ)
  section-fibered-system.sliceᵉ (comp-hom-fibered-systemᵉ kᵉ hᵉ) Yᵉ =
    comp-hom-fibered-systemᵉ
      ( section-fibered-system.sliceᵉ kᵉ (section-fibered-system.typeᵉ hᵉ Yᵉ))
      ( section-fibered-system.sliceᵉ hᵉ Yᵉ)

  htpy-hom-fibered-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ}
    {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ} {Cᵉ : systemᵉ l5ᵉ l6ᵉ} {Dᵉ : fibered-systemᵉ l7ᵉ l8ᵉ Cᵉ}
    {fᵉ f'ᵉ : hom-systemᵉ Aᵉ Cᵉ} (Hᵉ : htpy-hom-systemᵉ fᵉ f'ᵉ)
    (gᵉ : hom-fibered-systemᵉ fᵉ Bᵉ Dᵉ) (g'ᵉ : hom-fibered-systemᵉ f'ᵉ Bᵉ Dᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l7ᵉ ⊔ l8ᵉ)
  htpy-hom-fibered-systemᵉ Hᵉ gᵉ g'ᵉ = htpy-section-fibered-systemᵉ Hᵉ gᵉ g'ᵉ
```

### Weakening structure on fibered systems

```agda
  record fibered-weakeningᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} (Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ)
    (Wᵉ : weakeningᵉ Aᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        hom-fibered-systemᵉ
          ( weakening.typeᵉ Wᵉ Xᵉ)
          ( Bᵉ)
          ( fibered-system.sliceᵉ Bᵉ Yᵉ)
      sliceᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        fibered-weakeningᵉ
          ( fibered-system.sliceᵉ Bᵉ Yᵉ)
          ( weakening.sliceᵉ Wᵉ Xᵉ)

  record preserves-fibered-weakeningᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {Cᵉ : systemᵉ l5ᵉ l6ᵉ} {Dᵉ : fibered-systemᵉ l7ᵉ l8ᵉ Cᵉ}
    {WAᵉ : weakeningᵉ Aᵉ} {WCᵉ : weakeningᵉ Cᵉ}
    (WBᵉ : fibered-weakeningᵉ Bᵉ WAᵉ) (WDᵉ : fibered-weakeningᵉ Dᵉ WCᵉ)
    {fᵉ : hom-systemᵉ Aᵉ Cᵉ} (Wfᵉ : preserves-weakeningᵉ WAᵉ WCᵉ fᵉ)
    (gᵉ : hom-fibered-systemᵉ fᵉ Bᵉ Dᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l7ᵉ ⊔ l8ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        htpy-hom-fibered-systemᵉ
          ( preserves-weakening.typeᵉ Wfᵉ Xᵉ)
          ( comp-hom-fibered-systemᵉ
            ( section-fibered-system.sliceᵉ gᵉ Yᵉ)
            ( fibered-weakening.typeᵉ WBᵉ Yᵉ))
          ( comp-hom-fibered-systemᵉ
            ( fibered-weakening.typeᵉ WDᵉ
              ( section-fibered-system.typeᵉ gᵉ Yᵉ))
            ( gᵉ))
      sliceᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        preserves-fibered-weakeningᵉ
          ( fibered-weakening.sliceᵉ WBᵉ Yᵉ)
          ( fibered-weakening.sliceᵉ WDᵉ (section-fibered-system.typeᵉ gᵉ Yᵉ))
          ( preserves-weakening.sliceᵉ Wfᵉ Xᵉ)
          ( section-fibered-system.sliceᵉ gᵉ Yᵉ)
```

### Substitution structures on fibered systems

```agda
  record fibered-substitutionᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} (Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ)
    (Sᵉ : substitutionᵉ Aᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} {Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ}
        {xᵉ : system.elementᵉ Aᵉ Xᵉ} (yᵉ : fibered-system.elementᵉ Bᵉ Yᵉ xᵉ) →
        hom-fibered-systemᵉ
          ( substitution.typeᵉ Sᵉ xᵉ)
          ( fibered-system.sliceᵉ Bᵉ Yᵉ)
          ( Bᵉ)
      sliceᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        fibered-substitutionᵉ
          ( fibered-system.sliceᵉ Bᵉ Yᵉ)
          ( substitution.sliceᵉ Sᵉ Xᵉ)

  record preserves-fibered-substitutionᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ}
    {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ} {Cᵉ : systemᵉ l5ᵉ l6ᵉ}
    {Dᵉ : fibered-systemᵉ l7ᵉ l8ᵉ Cᵉ} {SAᵉ : substitutionᵉ Aᵉ} {SCᵉ : substitutionᵉ Cᵉ}
    (SBᵉ : fibered-substitutionᵉ Bᵉ SAᵉ) (SDᵉ : fibered-substitutionᵉ Dᵉ SCᵉ)
    {fᵉ : hom-systemᵉ Aᵉ Cᵉ} (Sfᵉ : preserves-substitutionᵉ SAᵉ SCᵉ fᵉ)
    (gᵉ : hom-fibered-systemᵉ fᵉ Bᵉ Dᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l7ᵉ ⊔ l8ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} {Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ}
        {xᵉ : system.elementᵉ Aᵉ Xᵉ} (yᵉ : fibered-system.elementᵉ Bᵉ Yᵉ xᵉ) →
        htpy-hom-fibered-systemᵉ
          ( preserves-substitution.typeᵉ Sfᵉ xᵉ)
          ( comp-hom-fibered-systemᵉ
            ( gᵉ)
            ( fibered-substitution.typeᵉ SBᵉ yᵉ))
          ( comp-hom-fibered-systemᵉ
            ( fibered-substitution.typeᵉ SDᵉ
              ( section-fibered-system.elementᵉ gᵉ yᵉ))
            ( section-fibered-system.sliceᵉ gᵉ Yᵉ))
      sliceᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        preserves-fibered-substitutionᵉ
          ( fibered-substitution.sliceᵉ SBᵉ Yᵉ)
          ( fibered-substitution.sliceᵉ SDᵉ
            ( section-fibered-system.typeᵉ gᵉ Yᵉ))
          ( preserves-substitution.sliceᵉ Sfᵉ Xᵉ)
          ( section-fibered-system.sliceᵉ gᵉ Yᵉ)
```

### Generic element structures on fibered systems equipped with a weakening structure

Weᵉ defineᵉ whatᵉ itᵉ meansᵉ forᵉ aᵉ fiberedᵉ systemᵉ equippedᵉ with fiberedᵉ weakeningᵉ
structureᵉ overᵉ aᵉ systemᵉ equippedᵉ with weakeningᵉ structureᵉ andᵉ theᵉ structureᵉ ofᵉ
genericᵉ elementsᵉ to beᵉ equippedᵉ with genericᵉ elements.ᵉ

```agda
  record fibered-generic-elementᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {WAᵉ : weakeningᵉ Aᵉ} (Wᵉ : fibered-weakeningᵉ Bᵉ WAᵉ)
    (δᵉ : generic-elementᵉ WAᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        fibered-system.elementᵉ
          ( fibered-system.sliceᵉ Bᵉ Yᵉ)
          ( section-fibered-system.typeᵉ (fibered-weakening.typeᵉ Wᵉ Yᵉ) Yᵉ)
          ( generic-element.typeᵉ δᵉ Xᵉ)
      sliceᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        fibered-generic-elementᵉ
          ( fibered-weakening.sliceᵉ Wᵉ Yᵉ)
          ( generic-element.sliceᵉ δᵉ Xᵉ)

  record preserves-fibered-generic-elementᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {Cᵉ : systemᵉ l5ᵉ l6ᵉ} {Dᵉ : fibered-systemᵉ l7ᵉ l8ᵉ Cᵉ}
    {WAᵉ : weakeningᵉ Aᵉ} {WCᵉ : weakeningᵉ Cᵉ}
    {WBᵉ : fibered-weakeningᵉ Bᵉ WAᵉ} {WDᵉ : fibered-weakeningᵉ Dᵉ WCᵉ}
    {δAᵉ : generic-elementᵉ WAᵉ} {δCᵉ : generic-elementᵉ WCᵉ}
    (δBᵉ : fibered-generic-elementᵉ WBᵉ δAᵉ) (δDᵉ : fibered-generic-elementᵉ WDᵉ δCᵉ)
    {fᵉ : hom-systemᵉ Aᵉ Cᵉ} {Wfᵉ : preserves-weakeningᵉ WAᵉ WCᵉ fᵉ}
    (δfᵉ : preserves-generic-elementᵉ δAᵉ δCᵉ Wfᵉ)
    {gᵉ : hom-fibered-systemᵉ fᵉ Bᵉ Dᵉ}
    (Wgᵉ : preserves-fibered-weakeningᵉ WBᵉ WDᵉ Wfᵉ gᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l7ᵉ ⊔ l8ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        Idᵉ
          ( double-trᵉ
            ( λ Zᵉ uᵉ vᵉ →
              fibered-system.elementᵉ
              ( fibered-system.sliceᵉ Dᵉ
                ( section-fibered-system.typeᵉ gᵉ Yᵉ))
              {Zᵉ} uᵉ vᵉ)
            ( section-system.typeᵉ (preserves-weakening.typeᵉ Wfᵉ Xᵉ) Xᵉ)
            ( section-fibered-system.typeᵉ
              ( preserves-fibered-weakening.typeᵉ Wgᵉ Yᵉ) Yᵉ)
            ( preserves-generic-element.typeᵉ δfᵉ Xᵉ)
            ( section-fibered-system.elementᵉ
              ( section-fibered-system.sliceᵉ gᵉ Yᵉ)
              ( fibered-generic-element.typeᵉ δBᵉ Yᵉ)))
          ( fibered-generic-element.typeᵉ δDᵉ
            ( section-fibered-system.typeᵉ gᵉ Yᵉ))
      sliceᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        preserves-fibered-generic-elementᵉ
          ( fibered-generic-element.sliceᵉ δBᵉ Yᵉ)
          ( fibered-generic-element.sliceᵉ δDᵉ
            ( section-fibered-system.typeᵉ gᵉ Yᵉ))
          ( preserves-generic-element.sliceᵉ δfᵉ Xᵉ)
          ( preserves-fibered-weakening.sliceᵉ Wgᵉ Yᵉ)
```

### Fibered dependent type theories

```agda
  record fibered-weakening-preserves-weakeningᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {WAᵉ : weakeningᵉ Aᵉ} (WWAᵉ : weakening-preserves-weakeningᵉ WAᵉ)
    (Wᵉ : fibered-weakeningᵉ Bᵉ WAᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        preserves-fibered-weakeningᵉ
          ( Wᵉ)
          ( fibered-weakening.sliceᵉ Wᵉ Yᵉ)
          ( weakening-preserves-weakening.typeᵉ WWAᵉ Xᵉ)
          ( fibered-weakening.typeᵉ Wᵉ Yᵉ)
      sliceᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        fibered-weakening-preserves-weakeningᵉ
          ( weakening-preserves-weakening.sliceᵉ WWAᵉ Xᵉ)
          ( fibered-weakening.sliceᵉ Wᵉ Yᵉ)

  record fibered-substitution-preserves-substitutionᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {SAᵉ : substitutionᵉ Aᵉ} (SSAᵉ : substitution-preserves-substitutionᵉ SAᵉ)
    (Sᵉ : fibered-substitutionᵉ Bᵉ SAᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} {Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ}
        {xᵉ : system.elementᵉ Aᵉ Xᵉ} (yᵉ : fibered-system.elementᵉ Bᵉ Yᵉ xᵉ) →
        preserves-fibered-substitutionᵉ
          ( fibered-substitution.sliceᵉ Sᵉ Yᵉ)
          ( Sᵉ)
          ( substitution-preserves-substitution.typeᵉ SSAᵉ xᵉ)
          ( fibered-substitution.typeᵉ Sᵉ yᵉ)
      sliceᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        fibered-substitution-preserves-substitutionᵉ
          ( substitution-preserves-substitution.sliceᵉ SSAᵉ Xᵉ)
          ( fibered-substitution.sliceᵉ Sᵉ Yᵉ)

  record fibered-weakening-preserves-substitutionᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {WAᵉ : weakeningᵉ Aᵉ} {SAᵉ : substitutionᵉ Aᵉ}
    (WSAᵉ : weakening-preserves-substitutionᵉ SAᵉ WAᵉ)
    (Wᵉ : fibered-weakeningᵉ Bᵉ WAᵉ) (Sᵉ : fibered-substitutionᵉ Bᵉ SAᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        preserves-fibered-substitutionᵉ
          ( Sᵉ)
          ( fibered-substitution.sliceᵉ Sᵉ Yᵉ)
          ( weakening-preserves-substitution.typeᵉ WSAᵉ Xᵉ)
          ( fibered-weakening.typeᵉ Wᵉ Yᵉ)
      sliceᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        fibered-weakening-preserves-substitutionᵉ
          ( weakening-preserves-substitution.sliceᵉ WSAᵉ Xᵉ)
          ( fibered-weakening.sliceᵉ Wᵉ Yᵉ)
          ( fibered-substitution.sliceᵉ Sᵉ Yᵉ)

  record fibered-substitution-preserves-weakeningᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {WAᵉ : weakeningᵉ Aᵉ} {SAᵉ : substitutionᵉ Aᵉ}
    (SWAᵉ : substitution-preserves-weakeningᵉ WAᵉ SAᵉ)
    (Wᵉ : fibered-weakeningᵉ Bᵉ WAᵉ) (Sᵉ : fibered-substitutionᵉ Bᵉ SAᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} {Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ}
        {xᵉ : system.elementᵉ Aᵉ Xᵉ} (yᵉ : fibered-system.elementᵉ Bᵉ Yᵉ xᵉ) →
        preserves-fibered-weakeningᵉ
          ( fibered-weakening.sliceᵉ Wᵉ Yᵉ)
          ( Wᵉ)
          ( substitution-preserves-weakening.typeᵉ SWAᵉ xᵉ)
          ( fibered-substitution.typeᵉ Sᵉ yᵉ)
      sliceᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        fibered-substitution-preserves-weakeningᵉ
          ( substitution-preserves-weakening.sliceᵉ SWAᵉ Xᵉ)
          ( fibered-weakening.sliceᵉ Wᵉ Yᵉ)
          ( fibered-substitution.sliceᵉ Sᵉ Yᵉ)

  record fibered-weakening-preserves-generic-elementᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {WAᵉ : weakeningᵉ Aᵉ} {δAᵉ : generic-elementᵉ WAᵉ}
    {WWAᵉ : weakening-preserves-weakeningᵉ WAᵉ}
    (WδAᵉ : weakening-preserves-generic-elementᵉ WAᵉ WWAᵉ δAᵉ)
    {Wᵉ : fibered-weakeningᵉ Bᵉ WAᵉ}
    (WWBᵉ : fibered-weakening-preserves-weakeningᵉ WWAᵉ Wᵉ)
    (δᵉ : fibered-generic-elementᵉ Wᵉ δAᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        preserves-fibered-generic-elementᵉ
          ( δᵉ)
          ( fibered-generic-element.sliceᵉ δᵉ Yᵉ)
          ( weakening-preserves-generic-element.typeᵉ WδAᵉ Xᵉ)
          ( fibered-weakening-preserves-weakening.typeᵉ WWBᵉ Yᵉ)
      sliceᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        fibered-weakening-preserves-generic-elementᵉ
          ( weakening-preserves-generic-element.sliceᵉ WδAᵉ Xᵉ)
          ( fibered-weakening-preserves-weakening.sliceᵉ WWBᵉ Yᵉ)
          ( fibered-generic-element.sliceᵉ δᵉ Yᵉ)

  record fibered-substitution-preserves-generic-elementᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {WAᵉ : weakeningᵉ Aᵉ} {SAᵉ : substitutionᵉ Aᵉ} {δAᵉ : generic-elementᵉ WAᵉ}
    {SWAᵉ : substitution-preserves-weakeningᵉ WAᵉ SAᵉ}
    (SδAᵉ : substitution-preserves-generic-elementᵉ WAᵉ δAᵉ SAᵉ SWAᵉ)
    {WBᵉ : fibered-weakeningᵉ Bᵉ WAᵉ} {SBᵉ : fibered-substitutionᵉ Bᵉ SAᵉ}
    (SWBᵉ : fibered-substitution-preserves-weakeningᵉ SWAᵉ WBᵉ SBᵉ)
    (δBᵉ : fibered-generic-elementᵉ WBᵉ δAᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} {Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ}
        {xᵉ : system.elementᵉ Aᵉ Xᵉ} (yᵉ : fibered-system.elementᵉ Bᵉ Yᵉ xᵉ) →
        preserves-fibered-generic-elementᵉ
          ( fibered-generic-element.sliceᵉ δBᵉ Yᵉ)
          ( δBᵉ)
          ( substitution-preserves-generic-element.typeᵉ SδAᵉ xᵉ)
          ( fibered-substitution-preserves-weakening.typeᵉ SWBᵉ yᵉ)
      sliceᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        fibered-substitution-preserves-generic-elementᵉ
          ( substitution-preserves-generic-element.sliceᵉ SδAᵉ Xᵉ)
          ( fibered-substitution-preserves-weakening.sliceᵉ SWBᵉ Yᵉ)
          ( fibered-generic-element.sliceᵉ δBᵉ Yᵉ)

  record fibered-substitution-cancels-weakeningᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {WAᵉ : weakeningᵉ Aᵉ} {SAᵉ : substitutionᵉ Aᵉ}
    (S!WAᵉ : substitution-cancels-weakeningᵉ WAᵉ SAᵉ)
    (WBᵉ : fibered-weakeningᵉ Bᵉ WAᵉ) (SBᵉ : fibered-substitutionᵉ Bᵉ SAᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} {Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ}
        {xᵉ : system.elementᵉ Aᵉ Xᵉ} (yᵉ : fibered-system.elementᵉ Bᵉ Yᵉ xᵉ) →
        htpy-hom-fibered-systemᵉ
          ( substitution-cancels-weakening.typeᵉ S!WAᵉ xᵉ)
          ( comp-hom-fibered-systemᵉ
            ( fibered-substitution.typeᵉ SBᵉ yᵉ)
            ( fibered-weakening.typeᵉ WBᵉ Yᵉ))
          ( id-hom-fibered-systemᵉ Bᵉ)
      sliceᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        fibered-substitution-cancels-weakeningᵉ
          ( substitution-cancels-weakening.sliceᵉ S!WAᵉ Xᵉ)
          ( fibered-weakening.sliceᵉ WBᵉ Yᵉ)
          ( fibered-substitution.sliceᵉ SBᵉ Yᵉ)

  record fibered-generic-element-is-identityᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {WAᵉ : weakeningᵉ Aᵉ} {SAᵉ : substitutionᵉ Aᵉ} {δAᵉ : generic-elementᵉ WAᵉ}
    (S!WAᵉ : substitution-cancels-weakeningᵉ WAᵉ SAᵉ)
    (δidAᵉ : generic-element-is-identityᵉ WAᵉ SAᵉ δAᵉ S!WAᵉ)
    {WBᵉ : fibered-weakeningᵉ Bᵉ WAᵉ} {SBᵉ : fibered-substitutionᵉ Bᵉ SAᵉ}
    (δBᵉ : fibered-generic-elementᵉ WBᵉ δAᵉ)
    (S!WBᵉ : fibered-substitution-cancels-weakeningᵉ S!WAᵉ WBᵉ SBᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} {Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ}
        {xᵉ : system.elementᵉ Aᵉ Xᵉ} (yᵉ : fibered-system.elementᵉ Bᵉ Yᵉ xᵉ) →
        Idᵉ ( double-trᵉ
              ( λ αᵉ βᵉ γᵉ → fibered-system.elementᵉ Bᵉ {Xᵉ = αᵉ} βᵉ γᵉ)
              ( section-system.typeᵉ
                ( substitution-cancels-weakening.typeᵉ S!WAᵉ xᵉ)
                ( Xᵉ))
              ( section-fibered-system.typeᵉ
                ( fibered-substitution-cancels-weakening.typeᵉ S!WBᵉ yᵉ)
                ( Yᵉ))
              ( generic-element-is-identity.typeᵉ δidAᵉ xᵉ)
              ( section-fibered-system.elementᵉ
                ( fibered-substitution.typeᵉ SBᵉ yᵉ)
                ( fibered-generic-element.typeᵉ δBᵉ Yᵉ)))
            ( yᵉ)
      sliceᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        fibered-generic-element-is-identityᵉ
          ( substitution-cancels-weakening.sliceᵉ S!WAᵉ Xᵉ)
          ( generic-element-is-identity.sliceᵉ δidAᵉ Xᵉ)
          ( fibered-generic-element.sliceᵉ δBᵉ Yᵉ)
          ( fibered-substitution-cancels-weakening.sliceᵉ S!WBᵉ Yᵉ)

  record fibered-substitution-by-generic-elementᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {WAᵉ : weakeningᵉ Aᵉ} {SAᵉ : substitutionᵉ Aᵉ} {δAᵉ : generic-elementᵉ WAᵉ}
    (Sδ!ᵉ : substitution-by-generic-elementᵉ WAᵉ SAᵉ δAᵉ)
    {WBᵉ : fibered-weakeningᵉ Bᵉ WAᵉ} (SBᵉ : fibered-substitutionᵉ Bᵉ SAᵉ)
    (δBᵉ : fibered-generic-elementᵉ WBᵉ δAᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        htpy-hom-fibered-systemᵉ
          ( substitution-by-generic-element.typeᵉ Sδ!ᵉ Xᵉ)
          ( comp-hom-fibered-systemᵉ
            ( fibered-substitution.typeᵉ
              ( fibered-substitution.sliceᵉ SBᵉ Yᵉ)
              ( fibered-generic-element.typeᵉ δBᵉ Yᵉ))
            ( fibered-weakening.typeᵉ
              ( fibered-weakening.sliceᵉ WBᵉ Yᵉ)
              ( section-fibered-system.typeᵉ
                ( fibered-weakening.typeᵉ WBᵉ Yᵉ)
                ( Yᵉ))))
          ( id-hom-fibered-systemᵉ (fibered-system.sliceᵉ Bᵉ Yᵉ))
      sliceᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (Yᵉ : fibered-system.typeᵉ Bᵉ Xᵉ) →
        fibered-substitution-by-generic-elementᵉ
          ( substitution-by-generic-element.sliceᵉ Sδ!ᵉ Xᵉ)
          ( fibered-substitution.sliceᵉ SBᵉ Yᵉ)
          ( fibered-generic-element.sliceᵉ δBᵉ Yᵉ)
```

---ᵉ

## Fibered dependent type theories

```agda
  record fibered-type-theoryᵉ
    {l1ᵉ l2ᵉ : Level} (l3ᵉ l4ᵉ : Level) (Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ)
    where
    coinductiveᵉ
    field
      sysᵉ : fibered-systemᵉ l3ᵉ l4ᵉ (type-theory.sysᵉ Aᵉ)
      Wᵉ : fibered-weakeningᵉ sysᵉ (type-theory.Wᵉ Aᵉ)
      Sᵉ : fibered-substitutionᵉ sysᵉ (type-theory.Sᵉ Aᵉ)
      δᵉ : fibered-generic-elementᵉ Wᵉ (type-theory.δᵉ Aᵉ)
      WWᵉ : fibered-weakening-preserves-weakeningᵉ (type-theory.WWᵉ Aᵉ) Wᵉ
      SSᵉ : fibered-substitution-preserves-substitutionᵉ (type-theory.SSᵉ Aᵉ) Sᵉ
      WSᵉ : fibered-weakening-preserves-substitutionᵉ (type-theory.WSᵉ Aᵉ) Wᵉ Sᵉ
      SWᵉ : fibered-substitution-preserves-weakeningᵉ (type-theory.SWᵉ Aᵉ) Wᵉ Sᵉ
      Wδᵉ : fibered-weakening-preserves-generic-elementᵉ (type-theory.Wδᵉ Aᵉ) WWᵉ δᵉ
      Sδᵉ :
        fibered-substitution-preserves-generic-elementᵉ (type-theory.Sδᵉ Aᵉ) SWᵉ δᵉ
      S!Wᵉ : fibered-substitution-cancels-weakeningᵉ (type-theory.S!Wᵉ Aᵉ) Wᵉ Sᵉ
      δidᵉ : fibered-generic-element-is-identityᵉ
              (type-theory.S!Wᵉ Aᵉ) (type-theory.δidᵉ Aᵉ) δᵉ S!Wᵉ
      Sδ!ᵉ : fibered-substitution-by-generic-elementᵉ (type-theory.Sδ!ᵉ Aᵉ) Sᵉ δᵉ

{-ᵉ
  total-type-theoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ}
    (Bᵉ : fibered-type-theoryᵉ l3ᵉ l4ᵉ Aᵉ) → type-theoryᵉ (l1ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l4ᵉ)
  type-theory.sysᵉ (total-type-theoryᵉ {Aᵉ = Aᵉ} Bᵉ) =
    total-systemᵉ (type-theory.sysᵉ Aᵉ) (fibered-type-theory.sysᵉ Bᵉ)
  type-theory.Wᵉ (total-type-theoryᵉ {Aᵉ = Aᵉ} Bᵉ) = {!!ᵉ}
  type-theory.Sᵉ (total-type-theoryᵉ {Aᵉ = Aᵉ} Bᵉ) = {!!ᵉ}
  type-theory.δᵉ (total-type-theoryᵉ {Aᵉ = Aᵉ} Bᵉ) = {!!ᵉ}
  type-theory.WWᵉ (total-type-theoryᵉ {Aᵉ = Aᵉ} Bᵉ) = {!!ᵉ}
  type-theory.SSᵉ (total-type-theoryᵉ {Aᵉ = Aᵉ} Bᵉ) = {!!ᵉ}
  type-theory.WSᵉ (total-type-theoryᵉ {Aᵉ = Aᵉ} Bᵉ) = {!!ᵉ}
  type-theory.SWᵉ (total-type-theoryᵉ {Aᵉ = Aᵉ} Bᵉ) = {!!ᵉ}
  type-theory.Wδᵉ (total-type-theoryᵉ {Aᵉ = Aᵉ} Bᵉ) = {!!ᵉ}
  type-theory.Sδᵉ (total-type-theoryᵉ {Aᵉ = Aᵉ} Bᵉ) = {!!ᵉ}
  type-theory.S!Wᵉ (total-type-theoryᵉ {Aᵉ = Aᵉ} Bᵉ) = {!!ᵉ}
  type-theory.δidᵉ (total-type-theoryᵉ {Aᵉ = Aᵉ} Bᵉ) = {!!ᵉ}
  type-theory.Sδ!ᵉ (total-type-theoryᵉ {Aᵉ = Aᵉ} Bᵉ) = {!!ᵉ}
-ᵉ}

{-ᵉ
  slice-fibered-type-theoryᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ}
-ᵉ}
```

---ᵉ

## Subtype theories

```agda
{-ᵉ
  record is-subtype-theoryᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ}
    (Bᵉ : fibered-type-theoryᵉ l3ᵉ l4ᵉ Aᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ  :
        ( (Xᵉ : system.typeᵉ (type-theory.sysᵉ Aᵉ)) →
          is-propᵉ (fibered-system.typeᵉ (fibered-type-theory.sysᵉ Bᵉ) Xᵉ)) ×ᵉ
        ( (Xᵉ : system.typeᵉ (type-theory.sysᵉ Aᵉ))
          ( Yᵉ : fibered-system.typeᵉ (fibered-type-theory.sysᵉ Bᵉ) Xᵉ)
          ( xᵉ : system.elementᵉ (type-theory.sysᵉ Aᵉ) Xᵉ) →
          is-propᵉ (fibered-system.elementᵉ (fibered-type-theory.sysᵉ Bᵉ) Yᵉ xᵉ))
      sliceᵉ :
        (Xᵉ : system.typeᵉ (type-theory.sysᵉ Aᵉ)) →
        is-subtype-theoryᵉ (slice-fibered-type-theoryᵉ Bᵉ Xᵉ)
-ᵉ}
```