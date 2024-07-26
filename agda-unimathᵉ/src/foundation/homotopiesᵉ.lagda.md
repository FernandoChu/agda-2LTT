# Homotopies

```agda
module foundation.homotopiesᵉ where

open import foundation-core.homotopiesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functionsᵉ
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.path-algebraᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-squares-of-identificationsᵉ
open import foundation-core.dependent-identificationsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
open import foundation-core.whiskering-homotopies-concatenationᵉ
```

</details>

## Idea

Aᵉ homotopyᵉ ofᵉ identificationsᵉ isᵉ aᵉ pointwiseᵉ equalityᵉ betweenᵉ dependentᵉ
functions.ᵉ Weᵉ definedᵉ homotopiesᵉ in
[`foundation-core.homotopies`](foundation-core.homotopies.md).ᵉ Inᵉ thisᵉ file,ᵉ weᵉ
record someᵉ propertiesᵉ ofᵉ homotopiesᵉ thatᵉ requireᵉ functionᵉ extensionality,ᵉ
equivalences,ᵉ orᵉ other.ᵉ

## Properties

### Inverting homotopies is an equivalence

```agda
is-equiv-inv-htpyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → is-equivᵉ (inv-htpyᵉ {fᵉ = fᵉ} {gᵉ = gᵉ})
is-equiv-inv-htpyᵉ fᵉ gᵉ =
  is-equiv-is-invertibleᵉ
    ( inv-htpyᵉ)
    ( λ Hᵉ → eq-htpyᵉ (λ xᵉ → inv-invᵉ (Hᵉ xᵉ)))
    ( λ Hᵉ → eq-htpyᵉ (λ xᵉ → inv-invᵉ (Hᵉ xᵉ)))

equiv-inv-htpyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → (fᵉ ~ᵉ gᵉ) ≃ᵉ (gᵉ ~ᵉ fᵉ)
pr1ᵉ (equiv-inv-htpyᵉ fᵉ gᵉ) = inv-htpyᵉ
pr2ᵉ (equiv-inv-htpyᵉ fᵉ gᵉ) = is-equiv-inv-htpyᵉ fᵉ gᵉ
```

### Concatenating homotopies by a fixed homotopy is an equivalence

#### Concatenating from the left

```agda
is-equiv-concat-htpyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) →
  (hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → is-equivᵉ (concat-htpyᵉ Hᵉ hᵉ)
is-equiv-concat-htpyᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ} {fᵉ} =
  ind-htpyᵉ fᵉ
    ( λ gᵉ Hᵉ → (hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → is-equivᵉ (concat-htpyᵉ Hᵉ hᵉ))
    ( λ hᵉ → is-equiv-idᵉ)

equiv-concat-htpyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) (hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) →
  (gᵉ ~ᵉ hᵉ) ≃ᵉ (fᵉ ~ᵉ hᵉ)
pr1ᵉ (equiv-concat-htpyᵉ Hᵉ hᵉ) = concat-htpyᵉ Hᵉ hᵉ
pr2ᵉ (equiv-concat-htpyᵉ Hᵉ hᵉ) = is-equiv-concat-htpyᵉ Hᵉ hᵉ
```

#### Concatenating from the right

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) {gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (Kᵉ : gᵉ ~ᵉ hᵉ)
  where

  is-section-concat-inv-htpy'ᵉ :
    ((concat-htpy'ᵉ fᵉ Kᵉ) ∘ᵉ (concat-inv-htpy'ᵉ fᵉ Kᵉ)) ~ᵉ idᵉ
  is-section-concat-inv-htpy'ᵉ Lᵉ =
    eq-htpyᵉ (λ xᵉ → is-section-inv-concat'ᵉ (Kᵉ xᵉ) (Lᵉ xᵉ))

  is-retraction-concat-inv-htpy'ᵉ :
    ((concat-inv-htpy'ᵉ fᵉ Kᵉ) ∘ᵉ (concat-htpy'ᵉ fᵉ Kᵉ)) ~ᵉ idᵉ
  is-retraction-concat-inv-htpy'ᵉ Lᵉ =
    eq-htpyᵉ (λ xᵉ → is-retraction-inv-concat'ᵉ (Kᵉ xᵉ) (Lᵉ xᵉ))

  is-equiv-concat-htpy'ᵉ : is-equivᵉ (concat-htpy'ᵉ fᵉ Kᵉ)
  is-equiv-concat-htpy'ᵉ =
    is-equiv-is-invertibleᵉ
      ( concat-inv-htpy'ᵉ fᵉ Kᵉ)
      ( is-section-concat-inv-htpy'ᵉ)
      ( is-retraction-concat-inv-htpy'ᵉ)

  equiv-concat-htpy'ᵉ : (fᵉ ~ᵉ gᵉ) ≃ᵉ (fᵉ ~ᵉ hᵉ)
  pr1ᵉ equiv-concat-htpy'ᵉ = concat-htpy'ᵉ fᵉ Kᵉ
  pr2ᵉ equiv-concat-htpy'ᵉ = is-equiv-concat-htpy'ᵉ
```

### Binary concatenation

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  {fᵉ gᵉ hᵉ kᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  is-binary-equiv-concat-htpyᵉ :
    is-binary-equivᵉ (λ (Hᵉ : fᵉ ~ᵉ gᵉ) (Kᵉ : gᵉ ~ᵉ hᵉ) → Hᵉ ∙hᵉ Kᵉ)
  pr1ᵉ is-binary-equiv-concat-htpyᵉ Kᵉ = is-equiv-concat-htpy'ᵉ fᵉ Kᵉ
  pr2ᵉ is-binary-equiv-concat-htpyᵉ Hᵉ = is-equiv-concat-htpyᵉ Hᵉ hᵉ

  equiv-binary-concat-htpyᵉ :
    (Hᵉ : fᵉ ~ᵉ gᵉ) (Kᵉ : hᵉ ~ᵉ kᵉ) → (gᵉ ~ᵉ hᵉ) ≃ᵉ (fᵉ ~ᵉ kᵉ)
  equiv-binary-concat-htpyᵉ Hᵉ Kᵉ = equiv-concat-htpy'ᵉ fᵉ Kᵉ ∘eᵉ equiv-concat-htpyᵉ Hᵉ hᵉ
```

### Horizontal composition of homotopies

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ : (aᵉ : Aᵉ) → Bᵉ aᵉ}
  where

  horizontal-concat-htpy²ᵉ :
    { Hᵉ H'ᵉ : fᵉ ~ᵉ gᵉ} → Hᵉ ~ᵉ H'ᵉ →
    { Kᵉ K'ᵉ : gᵉ ~ᵉ hᵉ} → Kᵉ ~ᵉ K'ᵉ →
    ( Hᵉ ∙hᵉ Kᵉ) ~ᵉ (H'ᵉ ∙hᵉ K'ᵉ)
  horizontal-concat-htpy²ᵉ αᵉ βᵉ xᵉ = horizontal-concat-Id²ᵉ (αᵉ xᵉ) (βᵉ xᵉ)
```

### Unit laws for horizontal concatenation of homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ : (aᵉ : Aᵉ) → Bᵉ aᵉ}
  {Hᵉ H'ᵉ : fᵉ ~ᵉ gᵉ}
  where

  compute-right-refl-htpy-horizontal-concat-htpy²ᵉ :
    (αᵉ : Hᵉ ~ᵉ H'ᵉ) (Kᵉ : gᵉ ~ᵉ hᵉ) →
    horizontal-concat-htpy²ᵉ αᵉ refl-htpyᵉ ~ᵉ right-whisker-concat-htpyᵉ αᵉ Kᵉ
  compute-right-refl-htpy-horizontal-concat-htpy²ᵉ αᵉ Kᵉ xᵉ =
    compute-right-refl-horizontal-concat-Id²ᵉ (αᵉ xᵉ)

  compute-left-refl-htpy-horizontal-concat-htpy²ᵉ :
    (Kᵉ : hᵉ ~ᵉ fᵉ) (αᵉ : Hᵉ ~ᵉ H'ᵉ) →
    horizontal-concat-htpy²ᵉ refl-htpyᵉ αᵉ ~ᵉ left-whisker-concat-htpyᵉ Kᵉ αᵉ
  compute-left-refl-htpy-horizontal-concat-htpy²ᵉ Kᵉ αᵉ xᵉ =
    compute-left-refl-horizontal-concat-Id²ᵉ (αᵉ xᵉ)
```

### Vertical inverses distribute over horizontal concatenation

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ : (aᵉ : Aᵉ) → Bᵉ aᵉ}
  {Hᵉ H'ᵉ : fᵉ ~ᵉ gᵉ} {Kᵉ K'ᵉ : gᵉ ~ᵉ hᵉ}
  where

  distributive-inv-horizontal-concat-htpy²ᵉ :
    (αᵉ : Hᵉ ~ᵉ H'ᵉ) (βᵉ : Kᵉ ~ᵉ Kᵉ) →
    inv-htpyᵉ (horizontal-concat-htpy²ᵉ αᵉ βᵉ) ~ᵉ
    horizontal-concat-htpy²ᵉ (inv-htpyᵉ αᵉ) (inv-htpyᵉ βᵉ)
  distributive-inv-horizontal-concat-htpy²ᵉ αᵉ βᵉ xᵉ =
    distributive-inv-horizontal-concat-Id²ᵉ (αᵉ xᵉ) (βᵉ xᵉ)
```

### The interchange law for horizontal composition of homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ : (aᵉ : Aᵉ) → Bᵉ aᵉ}
  {Hᵉ H'ᵉ H''ᵉ : fᵉ ~ᵉ gᵉ} (αᵉ : Hᵉ ~ᵉ H'ᵉ) (α'ᵉ : H'ᵉ ~ᵉ H''ᵉ) {Kᵉ K'ᵉ K''ᵉ : gᵉ ~ᵉ hᵉ}
  (βᵉ : Kᵉ ~ᵉ K'ᵉ) (β'ᵉ : K'ᵉ ~ᵉ K''ᵉ)
  where

  interchange-htpy²ᵉ :
    horizontal-concat-htpy²ᵉ (αᵉ ∙hᵉ α'ᵉ) (βᵉ ∙hᵉ β'ᵉ) ~ᵉ
    (horizontal-concat-htpy²ᵉ αᵉ βᵉ) ∙hᵉ (horizontal-concat-htpy²ᵉ α'ᵉ β'ᵉ)
  interchange-htpy²ᵉ xᵉ = interchange-Id²ᵉ (αᵉ xᵉ) (α'ᵉ xᵉ) (βᵉ xᵉ) (β'ᵉ xᵉ)
```

### Three dimensional concatenation of homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ : (aᵉ : Aᵉ) → Bᵉ aᵉ}
  where

  z-concat-htpy³ᵉ :
    {Hᵉ Kᵉ : fᵉ ~ᵉ gᵉ} {Lᵉ Mᵉ : gᵉ ~ᵉ hᵉ} {αᵉ βᵉ : Hᵉ ~ᵉ Kᵉ} {δᵉ εᵉ : Lᵉ ~ᵉ Mᵉ}
    (γᵉ : αᵉ ~ᵉ βᵉ) (ηᵉ : δᵉ ~ᵉ εᵉ) →
    horizontal-concat-htpy²ᵉ αᵉ δᵉ ~ᵉ horizontal-concat-htpy²ᵉ βᵉ εᵉ
  z-concat-htpy³ᵉ γᵉ ηᵉ xᵉ = z-concat-Id³ᵉ (γᵉ xᵉ) (ηᵉ xᵉ)
```

### Transposing homotopies is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (Hᵉ : fᵉ ~ᵉ gᵉ) (Kᵉ : gᵉ ~ᵉ hᵉ) (Lᵉ : fᵉ ~ᵉ hᵉ)
  where

  is-equiv-left-transpose-htpy-concatᵉ :
    is-equivᵉ (left-transpose-htpy-concatᵉ Hᵉ Kᵉ Lᵉ)
  is-equiv-left-transpose-htpy-concatᵉ =
    is-equiv-map-Π-is-fiberwise-equivᵉ
      ( λ xᵉ → is-equiv-left-transpose-eq-concatᵉ (Hᵉ xᵉ) (Kᵉ xᵉ) (Lᵉ xᵉ))

  equiv-left-transpose-htpy-concatᵉ : ((Hᵉ ∙hᵉ Kᵉ) ~ᵉ Lᵉ) ≃ᵉ (Kᵉ ~ᵉ ((inv-htpyᵉ Hᵉ) ∙hᵉ Lᵉ))
  pr1ᵉ equiv-left-transpose-htpy-concatᵉ = left-transpose-htpy-concatᵉ Hᵉ Kᵉ Lᵉ
  pr2ᵉ equiv-left-transpose-htpy-concatᵉ = is-equiv-left-transpose-htpy-concatᵉ

  is-equiv-right-transpose-htpy-concatᵉ :
    is-equivᵉ (right-transpose-htpy-concatᵉ Hᵉ Kᵉ Lᵉ)
  is-equiv-right-transpose-htpy-concatᵉ =
    is-equiv-map-Π-is-fiberwise-equivᵉ
      ( λ xᵉ → is-equiv-right-transpose-eq-concatᵉ (Hᵉ xᵉ) (Kᵉ xᵉ) (Lᵉ xᵉ))

  equiv-right-transpose-htpy-concatᵉ : ((Hᵉ ∙hᵉ Kᵉ) ~ᵉ Lᵉ) ≃ᵉ (Hᵉ ~ᵉ (Lᵉ ∙hᵉ (inv-htpyᵉ Kᵉ)))
  pr1ᵉ equiv-right-transpose-htpy-concatᵉ = right-transpose-htpy-concatᵉ Hᵉ Kᵉ Lᵉ
  pr2ᵉ equiv-right-transpose-htpy-concatᵉ = is-equiv-right-transpose-htpy-concatᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (Hᵉ : fᵉ ~ᵉ hᵉ) (Kᵉ : fᵉ ~ᵉ gᵉ) (Lᵉ : gᵉ ~ᵉ hᵉ)
  where

  equiv-left-transpose-htpy-concat'ᵉ : (Hᵉ ~ᵉ Kᵉ ∙hᵉ Lᵉ) ≃ᵉ (inv-htpyᵉ Kᵉ ∙hᵉ Hᵉ ~ᵉ Lᵉ)
  equiv-left-transpose-htpy-concat'ᵉ =
    ( equiv-inv-htpyᵉ Lᵉ ((inv-htpyᵉ Kᵉ) ∙hᵉ Hᵉ)) ∘eᵉ
    ( equiv-left-transpose-htpy-concatᵉ Kᵉ Lᵉ Hᵉ) ∘eᵉ
    ( equiv-inv-htpyᵉ Hᵉ (Kᵉ ∙hᵉ Lᵉ))

  equiv-right-transpose-htpy-concat'ᵉ : (Hᵉ ~ᵉ Kᵉ ∙hᵉ Lᵉ) ≃ᵉ (Hᵉ ∙hᵉ inv-htpyᵉ Lᵉ ~ᵉ Kᵉ)
  equiv-right-transpose-htpy-concat'ᵉ =
    ( equiv-inv-htpyᵉ Kᵉ (Hᵉ ∙hᵉ (inv-htpyᵉ Lᵉ))) ∘eᵉ
    ( equiv-right-transpose-htpy-concatᵉ Kᵉ Lᵉ Hᵉ) ∘eᵉ
    ( equiv-inv-htpyᵉ Hᵉ (Kᵉ ∙hᵉ Lᵉ))
```

### Computing dependent-identifications in the type family `eq-value` of dependent functions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ)
  where

  is-equiv-map-compute-dependent-identification-eq-valueᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : eq-valueᵉ fᵉ gᵉ xᵉ) (rᵉ : eq-valueᵉ fᵉ gᵉ yᵉ) →
    is-equivᵉ (map-compute-dependent-identification-eq-valueᵉ fᵉ gᵉ pᵉ qᵉ rᵉ)
  is-equiv-map-compute-dependent-identification-eq-valueᵉ reflᵉ qᵉ rᵉ =
    is-equiv-compᵉ
      ( invᵉ)
      ( concat'ᵉ rᵉ (right-unitᵉ ∙ᵉ ap-idᵉ qᵉ))
      ( is-equiv-concat'ᵉ rᵉ (right-unitᵉ ∙ᵉ ap-idᵉ qᵉ))
      ( is-equiv-invᵉ rᵉ qᵉ)

  compute-dependent-identification-eq-valueᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : eq-valueᵉ fᵉ gᵉ xᵉ) (rᵉ : eq-valueᵉ fᵉ gᵉ yᵉ) →
    coherence-square-identificationsᵉ (apᵉ (trᵉ Bᵉ pᵉ) qᵉ) (apdᵉ fᵉ pᵉ) (apdᵉ gᵉ pᵉ) rᵉ ≃ᵉ
    dependent-identificationᵉ (eq-valueᵉ fᵉ gᵉ) pᵉ qᵉ rᵉ
  pr1ᵉ (compute-dependent-identification-eq-valueᵉ pᵉ qᵉ rᵉ) =
    map-compute-dependent-identification-eq-valueᵉ fᵉ gᵉ pᵉ qᵉ rᵉ
  pr2ᵉ (compute-dependent-identification-eq-valueᵉ pᵉ qᵉ rᵉ) =
    is-equiv-map-compute-dependent-identification-eq-valueᵉ pᵉ qᵉ rᵉ

  map-inv-compute-dependent-identification-eq-valueᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : eq-valueᵉ fᵉ gᵉ xᵉ) (rᵉ : eq-valueᵉ fᵉ gᵉ yᵉ) →
    dependent-identificationᵉ (eq-valueᵉ fᵉ gᵉ) pᵉ qᵉ rᵉ →
    coherence-square-identificationsᵉ (apᵉ (trᵉ Bᵉ pᵉ) qᵉ) (apdᵉ fᵉ pᵉ) (apdᵉ gᵉ pᵉ) rᵉ
  map-inv-compute-dependent-identification-eq-valueᵉ pᵉ qᵉ rᵉ =
    map-inv-equivᵉ (compute-dependent-identification-eq-valueᵉ pᵉ qᵉ rᵉ)
```

### Computing dependent-identifications in the type family `eq-value` of ordinary functions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ gᵉ : Aᵉ → Bᵉ)
  where

  is-equiv-map-compute-dependent-identification-eq-value-functionᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : eq-valueᵉ fᵉ gᵉ xᵉ) (rᵉ : eq-valueᵉ fᵉ gᵉ yᵉ) →
    is-equivᵉ (map-compute-dependent-identification-eq-value-functionᵉ fᵉ gᵉ pᵉ qᵉ rᵉ)
  is-equiv-map-compute-dependent-identification-eq-value-functionᵉ reflᵉ qᵉ rᵉ =
    is-equiv-compᵉ
      ( invᵉ)
      ( concat'ᵉ rᵉ right-unitᵉ)
      ( is-equiv-concat'ᵉ rᵉ right-unitᵉ)
      ( is-equiv-invᵉ rᵉ qᵉ)

  compute-dependent-identification-eq-value-functionᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : fᵉ xᵉ ＝ᵉ gᵉ xᵉ) (rᵉ : fᵉ yᵉ ＝ᵉ gᵉ yᵉ) →
    coherence-square-identificationsᵉ qᵉ (apᵉ fᵉ pᵉ) (apᵉ gᵉ pᵉ) rᵉ ≃ᵉ
    dependent-identificationᵉ (eq-valueᵉ fᵉ gᵉ) pᵉ qᵉ rᵉ
  pr1ᵉ (compute-dependent-identification-eq-value-functionᵉ pᵉ qᵉ rᵉ) =
    map-compute-dependent-identification-eq-value-functionᵉ fᵉ gᵉ pᵉ qᵉ rᵉ
  pr2ᵉ (compute-dependent-identification-eq-value-functionᵉ pᵉ qᵉ rᵉ) =
    is-equiv-map-compute-dependent-identification-eq-value-functionᵉ pᵉ qᵉ rᵉ

  map-inv-compute-dependent-identification-eq-value-functionᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : fᵉ xᵉ ＝ᵉ gᵉ xᵉ) (rᵉ : fᵉ yᵉ ＝ᵉ gᵉ yᵉ) →
    dependent-identificationᵉ (eq-valueᵉ fᵉ gᵉ) pᵉ qᵉ rᵉ →
    coherence-square-identificationsᵉ qᵉ (apᵉ fᵉ pᵉ) (apᵉ gᵉ pᵉ) rᵉ
  map-inv-compute-dependent-identification-eq-value-functionᵉ pᵉ qᵉ rᵉ =
    map-inv-equivᵉ (compute-dependent-identification-eq-value-functionᵉ pᵉ qᵉ rᵉ)
```

### Relation between between `compute-dependent-identification-eq-value-function` and `nat-htpy`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {a0ᵉ a1ᵉ : Aᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ gᵉ : Aᵉ → Bᵉ)
  (Hᵉ : fᵉ ~ᵉ gᵉ)
  where

  nat-htpy-apd-htpyᵉ :
    (pᵉ : a0ᵉ ＝ᵉ a1ᵉ) →
    (map-inv-equivᵉ (compute-dependent-identification-eq-value-functionᵉ
      fᵉ gᵉ pᵉ (Hᵉ a0ᵉ) (Hᵉ a1ᵉ))) (apdᵉ Hᵉ pᵉ) ＝ᵉ invᵉ (nat-htpyᵉ Hᵉ pᵉ)
  nat-htpy-apd-htpyᵉ reflᵉ =
    invᵉ
      ( apᵉ
        ( map-inv-equivᵉ
          ( compute-dependent-identification-eq-value-functionᵉ fᵉ gᵉ reflᵉ
            ( Hᵉ a0ᵉ)
            ( Hᵉ a0ᵉ)))
        ( apᵉ invᵉ (left-invᵉ right-unitᵉ))) ∙ᵉ
      ( is-retraction-map-inv-equivᵉ
        ( compute-dependent-identification-eq-value-functionᵉ fᵉ gᵉ reflᵉ
          ( Hᵉ a0ᵉ)
          ( Hᵉ a1ᵉ))
        ( invᵉ right-unitᵉ))
```

### Action on identifications at `eq-htpy`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ}
  {hᵉ kᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  compute-eq-htpy-apᵉ :
    (pᵉ : hᵉ ~ᵉ kᵉ) →
    eq-htpyᵉ (λ iᵉ → apᵉ (fᵉ iᵉ) (pᵉ iᵉ)) ＝ᵉ apᵉ (map-Πᵉ fᵉ) (eq-htpyᵉ pᵉ)
  compute-eq-htpy-apᵉ =
    ind-htpyᵉ
      ( hᵉ)
      ( λ kᵉ pᵉ → eq-htpyᵉ (λ iᵉ → apᵉ (fᵉ iᵉ) (pᵉ iᵉ)) ＝ᵉ apᵉ (map-Πᵉ fᵉ) (eq-htpyᵉ pᵉ))
      ( eq-htpy-refl-htpyᵉ (map-Πᵉ fᵉ hᵉ) ∙ᵉ
        invᵉ (ap²ᵉ (map-Πᵉ fᵉ) (eq-htpy-refl-htpyᵉ hᵉ)))
```

## See also

-ᵉ [Multivariableᵉ homotopies](foundation.multivariable-homotopies.md).ᵉ
-ᵉ Theᵉ [whiskeringᵉ operations](foundation.whiskering-homotopies-composition.mdᵉ)
  onᵉ homotopies.ᵉ