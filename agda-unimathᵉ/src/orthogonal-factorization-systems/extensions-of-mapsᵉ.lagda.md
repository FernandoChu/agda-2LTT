# Extensions of maps

```agda
module orthogonal-factorization-systems.extensions-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.monomorphismsᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.precomposition-dependent-functionsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.torsorial-type-familiesᵉ

open import orthogonal-factorization-systems.local-typesᵉ
```

</details>

## Idea

Anᵉ **extension**ᵉ ofᵉ aᵉ mapᵉ `fᵉ : (xᵉ : Aᵉ) → Pᵉ x`ᵉ alongᵉ aᵉ mapᵉ `iᵉ : Aᵉ → B`ᵉ isᵉ aᵉ mapᵉ
`gᵉ : (yᵉ : Bᵉ) → Qᵉ y`ᵉ suchᵉ thatᵉ `Q`ᵉ restrictsᵉ alongᵉ `i`ᵉ to `P`ᵉ andᵉ `g`ᵉ restrictsᵉ
alongᵉ `i`ᵉ to `f`.ᵉ

```text
  Aᵉ
  |  \ᵉ
  iᵉ    fᵉ
  |      \ᵉ
  ∨ᵉ       ∨ᵉ
  Bᵉ -ᵉ gᵉ ->ᵉ Pᵉ
```

## Definition

### Extensions of dependent functions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (iᵉ : Aᵉ → Bᵉ)
  where

  is-extensionᵉ :
    {Pᵉ : Bᵉ → UUᵉ l3ᵉ} →
    ((xᵉ : Aᵉ) → Pᵉ (iᵉ xᵉ)) → ((yᵉ : Bᵉ) → Pᵉ yᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  is-extensionᵉ fᵉ gᵉ = fᵉ ~ᵉ (gᵉ ∘ᵉ iᵉ)

  extension-dependent-typeᵉ :
    (Pᵉ : Bᵉ → UUᵉ l3ᵉ) →
    ((xᵉ : Aᵉ) → Pᵉ (iᵉ xᵉ)) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  extension-dependent-typeᵉ Pᵉ fᵉ = Σᵉ ((yᵉ : Bᵉ) → Pᵉ yᵉ) (is-extensionᵉ fᵉ)

  extensionᵉ :
    {Xᵉ : UUᵉ l3ᵉ} → (Aᵉ → Xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  extensionᵉ {Xᵉ} = extension-dependent-typeᵉ (λ _ → Xᵉ)

  total-extension-dependent-typeᵉ : (Pᵉ : Bᵉ → UUᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  total-extension-dependent-typeᵉ Pᵉ =
    Σᵉ ((xᵉ : Aᵉ) → Pᵉ (iᵉ xᵉ)) (extension-dependent-typeᵉ Pᵉ)

  total-extensionᵉ : (Xᵉ : UUᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  total-extensionᵉ Xᵉ = total-extension-dependent-typeᵉ (λ _ → Xᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {iᵉ : Aᵉ → Bᵉ}
  {Pᵉ : Bᵉ → UUᵉ l3ᵉ} {fᵉ : (xᵉ : Aᵉ) → Pᵉ (iᵉ xᵉ)}
  where

  map-extensionᵉ : extension-dependent-typeᵉ iᵉ Pᵉ fᵉ → (yᵉ : Bᵉ) → Pᵉ yᵉ
  map-extensionᵉ = pr1ᵉ

  is-extension-map-extensionᵉ :
    (Eᵉ : extension-dependent-typeᵉ iᵉ Pᵉ fᵉ) → is-extensionᵉ iᵉ fᵉ (map-extensionᵉ Eᵉ)
  is-extension-map-extensionᵉ = pr2ᵉ
```

## Operations

### Vertical composition of extensions of maps

```text
  Aᵉ
  |  \ᵉ
  iᵉ    fᵉ
  |      \ᵉ
  ∨ᵉ       ∨ᵉ
  Bᵉ -ᵉ gᵉ ->ᵉ Pᵉ
  |       ∧ᵉ
  jᵉ      /ᵉ
  |    hᵉ
  ∨ᵉ  /ᵉ
  Cᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Pᵉ : Cᵉ → UUᵉ l4ᵉ}
  {iᵉ : Aᵉ → Bᵉ} {jᵉ : Bᵉ → Cᵉ}
  {fᵉ : (xᵉ : Aᵉ) → Pᵉ (jᵉ (iᵉ xᵉ))} {gᵉ : (xᵉ : Bᵉ) → Pᵉ (jᵉ xᵉ)} {hᵉ : (xᵉ : Cᵉ) → Pᵉ xᵉ}
  where

  is-extension-comp-verticalᵉ :
    is-extensionᵉ jᵉ gᵉ hᵉ → is-extensionᵉ iᵉ fᵉ gᵉ → is-extensionᵉ (jᵉ ∘ᵉ iᵉ) fᵉ hᵉ
  is-extension-comp-verticalᵉ Hᵉ Gᵉ xᵉ = Gᵉ xᵉ ∙ᵉ Hᵉ (iᵉ xᵉ)
```

### Horizontal composition of extensions of maps

```text
           Aᵉ
        /ᵉ  |  \ᵉ
      fᵉ    gᵉ    hᵉ
    /ᵉ      |      \ᵉ
   ∨ᵉ       ∨ᵉ       ∨ᵉ
  Bᵉ -ᵉ iᵉ ->ᵉ Cᵉ -ᵉ jᵉ ->ᵉ Pᵉ
```

#### Horizontal composition of extensions of dependent functions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Pᵉ : Cᵉ → UUᵉ l4ᵉ}
  {fᵉ : Aᵉ → Bᵉ} {gᵉ : Aᵉ → Cᵉ} {hᵉ : (xᵉ : Aᵉ) → Pᵉ (gᵉ xᵉ)}
  {iᵉ : Bᵉ → Cᵉ} {jᵉ : (zᵉ : Cᵉ) → Pᵉ zᵉ}
  where

  is-extension-dependent-type-comp-horizontalᵉ :
    (Iᵉ : is-extensionᵉ fᵉ gᵉ iᵉ) →
    is-extensionᵉ gᵉ hᵉ jᵉ → is-extensionᵉ fᵉ (λ xᵉ → trᵉ Pᵉ (Iᵉ xᵉ) (hᵉ xᵉ)) (jᵉ ∘ᵉ iᵉ)
  is-extension-dependent-type-comp-horizontalᵉ Iᵉ Jᵉ xᵉ =
    apᵉ (trᵉ Pᵉ (Iᵉ xᵉ)) (Jᵉ xᵉ) ∙ᵉ apdᵉ jᵉ (Iᵉ xᵉ)
```

#### Horizontal composition of extensions of ordinary maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  {fᵉ : Aᵉ → Bᵉ} {gᵉ : Aᵉ → Cᵉ} {hᵉ : Aᵉ → Xᵉ}
  {iᵉ : Bᵉ → Cᵉ} {jᵉ : Cᵉ → Xᵉ}
  where

  is-extension-comp-horizontalᵉ :
    (Iᵉ : is-extensionᵉ fᵉ gᵉ iᵉ) → is-extensionᵉ gᵉ hᵉ jᵉ → is-extensionᵉ fᵉ hᵉ (jᵉ ∘ᵉ iᵉ)
  is-extension-comp-horizontalᵉ Iᵉ Jᵉ xᵉ = (Jᵉ xᵉ) ∙ᵉ apᵉ jᵉ (Iᵉ xᵉ)
```

### Left whiskering of extensions of maps

```text
  Aᵉ
  |  \ᵉ
  iᵉ    fᵉ
  |      \ᵉ
  ∨ᵉ       ∨ᵉ
  Bᵉ -ᵉ gᵉ ->ᵉ Cᵉ -ᵉ hᵉ ->ᵉ Pᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Pᵉ : Cᵉ → UUᵉ l4ᵉ}
  {iᵉ : Aᵉ → Bᵉ} {fᵉ : Aᵉ → Cᵉ} {gᵉ : Bᵉ → Cᵉ}
  where

  is-extension-left-whiskerᵉ :
    (hᵉ : (xᵉ : Cᵉ) → Pᵉ xᵉ) (Fᵉ : is-extensionᵉ iᵉ fᵉ gᵉ) →
    (is-extensionᵉ iᵉ (λ xᵉ → trᵉ Pᵉ (Fᵉ xᵉ) (hᵉ (fᵉ xᵉ))) (hᵉ ∘ᵉ gᵉ))
  is-extension-left-whiskerᵉ hᵉ Fᵉ = apdᵉ hᵉ ∘ᵉ Fᵉ
```

### Right whiskering of extensions of maps

```text
  Xᵉ -ᵉ hᵉ ->ᵉ Aᵉ
           |  \ᵉ
           iᵉ    fᵉ
           |      \ᵉ
           ∨ᵉ       ∨ᵉ
           Bᵉ -ᵉ gᵉ ->ᵉ Pᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Pᵉ : Bᵉ → UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  {iᵉ : Aᵉ → Bᵉ} {fᵉ : (xᵉ : Aᵉ) → Pᵉ (iᵉ xᵉ)} {gᵉ : (yᵉ : Bᵉ) → Pᵉ yᵉ}
  where

  is-extension-right-whiskerᵉ :
    (Fᵉ : is-extensionᵉ iᵉ fᵉ gᵉ) (hᵉ : Xᵉ → Aᵉ) → is-extensionᵉ (iᵉ ∘ᵉ hᵉ) (fᵉ ∘ᵉ hᵉ) gᵉ
  is-extension-right-whiskerᵉ Fᵉ hᵉ = Fᵉ ∘ᵉ hᵉ
```

### Postcomposition of extensions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  where

  postcomp-extensionᵉ :
    (fᵉ : Aᵉ → Bᵉ) (iᵉ : Aᵉ → Xᵉ) (gᵉ : Xᵉ → Yᵉ) →
    extensionᵉ fᵉ iᵉ → extensionᵉ fᵉ (gᵉ ∘ᵉ iᵉ)
  postcomp-extensionᵉ fᵉ iᵉ gᵉ =
    map-Σᵉ (is-extensionᵉ fᵉ (gᵉ ∘ᵉ iᵉ)) (postcompᵉ Bᵉ gᵉ) (λ jᵉ Hᵉ → gᵉ ·lᵉ Hᵉ)
```

## Properties

### Characterizing identifications of extensions of maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (iᵉ : Aᵉ → Bᵉ)
  {Pᵉ : Bᵉ → UUᵉ l3ᵉ}
  (fᵉ : (xᵉ : Aᵉ) → Pᵉ (iᵉ xᵉ))
  where

  coherence-htpy-extensionᵉ :
    (eᵉ e'ᵉ : extension-dependent-typeᵉ iᵉ Pᵉ fᵉ) →
    map-extensionᵉ eᵉ ~ᵉ map-extensionᵉ e'ᵉ → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  coherence-htpy-extensionᵉ eᵉ e'ᵉ Kᵉ =
    (is-extension-map-extensionᵉ eᵉ ∙hᵉ (Kᵉ ·rᵉ iᵉ)) ~ᵉ is-extension-map-extensionᵉ e'ᵉ

  htpy-extensionᵉ : (eᵉ e'ᵉ : extension-dependent-typeᵉ iᵉ Pᵉ fᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  htpy-extensionᵉ eᵉ e'ᵉ =
    Σᵉ ( map-extensionᵉ eᵉ ~ᵉ map-extensionᵉ e'ᵉ)
      ( coherence-htpy-extensionᵉ eᵉ e'ᵉ)

  refl-htpy-extensionᵉ :
    (eᵉ : extension-dependent-typeᵉ iᵉ Pᵉ fᵉ) → htpy-extensionᵉ eᵉ eᵉ
  pr1ᵉ (refl-htpy-extensionᵉ eᵉ) = refl-htpyᵉ
  pr2ᵉ (refl-htpy-extensionᵉ eᵉ) = right-unit-htpyᵉ

  htpy-eq-extensionᵉ :
    (eᵉ e'ᵉ : extension-dependent-typeᵉ iᵉ Pᵉ fᵉ) → eᵉ ＝ᵉ e'ᵉ → htpy-extensionᵉ eᵉ e'ᵉ
  htpy-eq-extensionᵉ eᵉ .eᵉ reflᵉ = refl-htpy-extensionᵉ eᵉ

  is-torsorial-htpy-extensionᵉ :
    (eᵉ : extension-dependent-typeᵉ iᵉ Pᵉ fᵉ) → is-torsorialᵉ (htpy-extensionᵉ eᵉ)
  is-torsorial-htpy-extensionᵉ eᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (map-extensionᵉ eᵉ))
      ( map-extensionᵉ eᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-htpyᵉ (is-extension-map-extensionᵉ eᵉ ∙hᵉ refl-htpyᵉ))

  is-equiv-htpy-eq-extensionᵉ :
    (eᵉ e'ᵉ : extension-dependent-typeᵉ iᵉ Pᵉ fᵉ) → is-equivᵉ (htpy-eq-extensionᵉ eᵉ e'ᵉ)
  is-equiv-htpy-eq-extensionᵉ eᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-extensionᵉ eᵉ)
      ( htpy-eq-extensionᵉ eᵉ)

  extensionality-extensionᵉ :
    (eᵉ e'ᵉ : extension-dependent-typeᵉ iᵉ Pᵉ fᵉ) → (eᵉ ＝ᵉ e'ᵉ) ≃ᵉ (htpy-extensionᵉ eᵉ e'ᵉ)
  pr1ᵉ (extensionality-extensionᵉ eᵉ e'ᵉ) = htpy-eq-extensionᵉ eᵉ e'ᵉ
  pr2ᵉ (extensionality-extensionᵉ eᵉ e'ᵉ) = is-equiv-htpy-eq-extensionᵉ eᵉ e'ᵉ

  eq-htpy-extensionᵉ :
    (eᵉ e'ᵉ : extension-dependent-typeᵉ iᵉ Pᵉ fᵉ)
    (Hᵉ : map-extensionᵉ eᵉ ~ᵉ map-extensionᵉ e'ᵉ) →
    coherence-htpy-extensionᵉ eᵉ e'ᵉ Hᵉ → eᵉ ＝ᵉ e'ᵉ
  eq-htpy-extensionᵉ eᵉ e'ᵉ Hᵉ Kᵉ =
    map-inv-equivᵉ (extensionality-extensionᵉ eᵉ e'ᵉ) (Hᵉ ,ᵉ Kᵉ)
```

### The total type of extensions is equivalent to `(y : B) → P y`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (iᵉ : Aᵉ → Bᵉ)
  where

  inv-compute-total-extension-dependent-typeᵉ :
    {Pᵉ : Bᵉ → UUᵉ l3ᵉ} → total-extension-dependent-typeᵉ iᵉ Pᵉ ≃ᵉ ((yᵉ : Bᵉ) → Pᵉ yᵉ)
  inv-compute-total-extension-dependent-typeᵉ =
    ( right-unit-law-Σ-is-contrᵉ (λ fᵉ → is-torsorial-htpy'ᵉ (fᵉ ∘ᵉ iᵉ))) ∘eᵉ
    ( equiv-left-swap-Σᵉ)

  compute-total-extension-dependent-typeᵉ :
    {Pᵉ : Bᵉ → UUᵉ l3ᵉ} → ((yᵉ : Bᵉ) → Pᵉ yᵉ) ≃ᵉ total-extension-dependent-typeᵉ iᵉ Pᵉ
  compute-total-extension-dependent-typeᵉ =
    inv-equivᵉ (inv-compute-total-extension-dependent-typeᵉ)

  inv-compute-total-extensionᵉ :
    {Xᵉ : UUᵉ l3ᵉ} → total-extensionᵉ iᵉ Xᵉ ≃ᵉ (Bᵉ → Xᵉ)
  inv-compute-total-extensionᵉ = inv-compute-total-extension-dependent-typeᵉ

  compute-total-extensionᵉ :
    {Xᵉ : UUᵉ l3ᵉ} → (Bᵉ → Xᵉ) ≃ᵉ total-extensionᵉ iᵉ Xᵉ
  compute-total-extensionᵉ = compute-total-extension-dependent-typeᵉ
```

### The truncation level of the type of extensions is bounded by the truncation level of the codomains

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (iᵉ : Aᵉ → Bᵉ)
  where

  is-trunc-is-extension-dependent-typeᵉ :
    {Pᵉ : Bᵉ → UUᵉ l3ᵉ} (fᵉ : (xᵉ : Aᵉ) → Pᵉ (iᵉ xᵉ)) →
    ((xᵉ : Aᵉ) → is-truncᵉ (succ-𝕋ᵉ kᵉ) (Pᵉ (iᵉ xᵉ))) →
    (gᵉ : (xᵉ : Bᵉ) → Pᵉ xᵉ) → is-truncᵉ kᵉ (is-extensionᵉ iᵉ fᵉ gᵉ)
  is-trunc-is-extension-dependent-typeᵉ fᵉ is-trunc-Pᵉ gᵉ =
    is-trunc-Πᵉ kᵉ λ xᵉ → is-trunc-Pᵉ xᵉ (fᵉ xᵉ) (gᵉ (iᵉ xᵉ))

  is-trunc-extension-dependent-typeᵉ :
    {Pᵉ : Bᵉ → UUᵉ l3ᵉ} (fᵉ : (xᵉ : Aᵉ) → Pᵉ (iᵉ xᵉ)) →
    ((xᵉ : Bᵉ) → is-truncᵉ kᵉ (Pᵉ xᵉ)) → is-truncᵉ kᵉ (extension-dependent-typeᵉ iᵉ Pᵉ fᵉ)
  is-trunc-extension-dependent-typeᵉ fᵉ is-trunc-Pᵉ =
    is-trunc-Σᵉ
      ( is-trunc-Πᵉ kᵉ is-trunc-Pᵉ)
      ( is-trunc-is-extension-dependent-typeᵉ fᵉ
        ( is-trunc-succ-is-truncᵉ kᵉ ∘ᵉ (is-trunc-Pᵉ ∘ᵉ iᵉ)))

  is-trunc-total-extension-dependent-typeᵉ :
    {Pᵉ : Bᵉ → UUᵉ l3ᵉ} →
    ((xᵉ : Bᵉ) → is-truncᵉ kᵉ (Pᵉ xᵉ)) →
    is-truncᵉ kᵉ (total-extension-dependent-typeᵉ iᵉ Pᵉ)
  is-trunc-total-extension-dependent-typeᵉ {Pᵉ} is-trunc-Pᵉ =
    is-trunc-equiv'ᵉ kᵉ
      ( (yᵉ : Bᵉ) → Pᵉ yᵉ)
      ( compute-total-extension-dependent-typeᵉ iᵉ)
      ( is-trunc-Πᵉ kᵉ is-trunc-Pᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (iᵉ : Aᵉ → Bᵉ)
  where

  is-contr-is-extensionᵉ :
    {Pᵉ : Bᵉ → UUᵉ l3ᵉ} (fᵉ : (xᵉ : Aᵉ) → Pᵉ (iᵉ xᵉ)) →
    ((xᵉ : Aᵉ) → is-propᵉ (Pᵉ (iᵉ xᵉ))) →
    (gᵉ : (xᵉ : Bᵉ) → Pᵉ xᵉ) → is-contrᵉ (is-extensionᵉ iᵉ fᵉ gᵉ)
  is-contr-is-extensionᵉ fᵉ is-prop-Pᵉ gᵉ =
    is-contr-Πᵉ λ xᵉ → is-prop-Pᵉ xᵉ (fᵉ xᵉ) (gᵉ (iᵉ xᵉ))

  is-prop-is-extensionᵉ :
    {Pᵉ : Bᵉ → UUᵉ l3ᵉ} (fᵉ : (xᵉ : Aᵉ) → Pᵉ (iᵉ xᵉ)) →
    ((xᵉ : Aᵉ) → is-setᵉ (Pᵉ (iᵉ xᵉ))) →
    (gᵉ : (xᵉ : Bᵉ) → Pᵉ xᵉ) → is-propᵉ (is-extensionᵉ iᵉ fᵉ gᵉ)
  is-prop-is-extensionᵉ fᵉ is-set-Pᵉ gᵉ =
    is-prop-Πᵉ (λ xᵉ → is-set-Pᵉ xᵉ (fᵉ xᵉ) (gᵉ (iᵉ xᵉ)))
```

### Every map has a unique extension along `i` if and only if `P` is `i`-local

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (iᵉ : Aᵉ → Bᵉ)
  {lᵉ : Level} (Pᵉ : Bᵉ → UUᵉ lᵉ)
  where

  equiv-fiber'-precomp-extension-dependent-typeᵉ :
    (fᵉ : (xᵉ : Aᵉ) → Pᵉ (iᵉ xᵉ)) →
    fiber'ᵉ (precomp-Πᵉ iᵉ Pᵉ) fᵉ ≃ᵉ extension-dependent-typeᵉ iᵉ Pᵉ fᵉ
  equiv-fiber'-precomp-extension-dependent-typeᵉ fᵉ =
    equiv-totᵉ (λ gᵉ → equiv-funextᵉ {fᵉ = fᵉ} {gᵉ ∘ᵉ iᵉ})

  equiv-fiber-precomp-extension-dependent-typeᵉ :
    (fᵉ : (xᵉ : Aᵉ) → Pᵉ (iᵉ xᵉ)) →
    fiberᵉ (precomp-Πᵉ iᵉ Pᵉ) fᵉ ≃ᵉ extension-dependent-typeᵉ iᵉ Pᵉ fᵉ
  equiv-fiber-precomp-extension-dependent-typeᵉ fᵉ =
    ( equiv-fiber'-precomp-extension-dependent-typeᵉ fᵉ) ∘eᵉ
    ( equiv-fiberᵉ (precomp-Πᵉ iᵉ Pᵉ) fᵉ)

  equiv-is-contr-extension-dependent-type-is-local-dependent-typeᵉ :
    is-local-dependent-typeᵉ iᵉ Pᵉ ≃ᵉ
    ((fᵉ : (xᵉ : Aᵉ) → Pᵉ (iᵉ xᵉ)) → is-contrᵉ (extension-dependent-typeᵉ iᵉ Pᵉ fᵉ))
  equiv-is-contr-extension-dependent-type-is-local-dependent-typeᵉ =
    ( equiv-Π-equiv-familyᵉ
      ( equiv-is-contr-equivᵉ ∘ᵉ equiv-fiber-precomp-extension-dependent-typeᵉ)) ∘eᵉ
    ( equiv-is-contr-map-is-equivᵉ (precomp-Πᵉ iᵉ Pᵉ))

  is-contr-extension-dependent-type-is-local-dependent-typeᵉ :
    is-local-dependent-typeᵉ iᵉ Pᵉ →
    (fᵉ : (xᵉ : Aᵉ) → Pᵉ (iᵉ xᵉ)) → is-contrᵉ (extension-dependent-typeᵉ iᵉ Pᵉ fᵉ)
  is-contr-extension-dependent-type-is-local-dependent-typeᵉ =
    map-equivᵉ equiv-is-contr-extension-dependent-type-is-local-dependent-typeᵉ

  is-local-dependent-type-is-contr-extension-dependent-typeᵉ :
    ((fᵉ : (xᵉ : Aᵉ) → Pᵉ (iᵉ xᵉ)) → is-contrᵉ (extension-dependent-typeᵉ iᵉ Pᵉ fᵉ)) →
    is-local-dependent-typeᵉ iᵉ Pᵉ
  is-local-dependent-type-is-contr-extension-dependent-typeᵉ =
    map-inv-equivᵉ
      equiv-is-contr-extension-dependent-type-is-local-dependent-typeᵉ
```

## Examples

### Every map is an extension of itself along the identity

```agda
is-extension-selfᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Pᵉ : Aᵉ → UUᵉ l2ᵉ}
  (fᵉ : (xᵉ : Aᵉ) → Pᵉ xᵉ) → is-extensionᵉ idᵉ fᵉ fᵉ
is-extension-selfᵉ _ = refl-htpyᵉ
```

### The identity is an extension of every map along themselves

```agda
is-extension-along-selfᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (fᵉ : Aᵉ → Bᵉ) → is-extensionᵉ fᵉ fᵉ idᵉ
is-extension-along-selfᵉ _ = refl-htpyᵉ
```

### Postcomposition of extensions by an embedding is an embedding

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  where

  is-emb-postcomp-extensionᵉ :
    (fᵉ : Aᵉ → Bᵉ) (iᵉ : Aᵉ → Xᵉ) (gᵉ : Xᵉ → Yᵉ) → is-embᵉ gᵉ →
    is-embᵉ (postcomp-extensionᵉ fᵉ iᵉ gᵉ)
  is-emb-postcomp-extensionᵉ fᵉ iᵉ gᵉ Hᵉ =
    is-emb-map-Σᵉ
      ( is-extensionᵉ fᵉ (gᵉ ∘ᵉ iᵉ))
      ( is-mono-is-embᵉ gᵉ Hᵉ Bᵉ)
      ( λ jᵉ →
        is-emb-is-equivᵉ
          ( is-equiv-map-Π-is-fiberwise-equivᵉ
            ( λ xᵉ → Hᵉ (iᵉ xᵉ) (jᵉ (fᵉ xᵉ)))))
```

## See also

-ᵉ [`orthogonal-factorization-systems.lifts-of-maps`](orthogonal-factorization-systems.lifts-of-maps.mdᵉ)
  forᵉ theᵉ dualᵉ notion.ᵉ