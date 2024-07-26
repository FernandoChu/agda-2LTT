# Morphisms in the slice category of types

```agda
module foundation.sliceᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-homotopiesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.families-of-equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ

open import trees.polynomial-endofunctorsᵉ
```

</details>

## Idea

Theᵉ sliceᵉ ofᵉ aᵉ categoryᵉ overᵉ anᵉ objectᵉ Xᵉ isᵉ theᵉ categoryᵉ ofᵉ morphismsᵉ intoᵉ X.ᵉ Aᵉ
morphismᵉ in theᵉ sliceᵉ fromᵉ `fᵉ : Aᵉ → X`ᵉ to `gᵉ : Bᵉ → X`ᵉ consistsᵉ ofᵉ aᵉ functionᵉ
`hᵉ : Aᵉ → B`ᵉ suchᵉ thatᵉ theᵉ triangleᵉ `fᵉ ~ᵉ gᵉ ∘ᵉ h`ᵉ commutes.ᵉ Weᵉ makeᵉ theseᵉ
definitionsᵉ forᵉ types.ᵉ

## Definition

### The objects of the slice category of types

```agda
Sliceᵉ : (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc lᵉ)
Sliceᵉ lᵉ = type-polynomial-endofunctorᵉ (UUᵉ lᵉ) (λ Xᵉ → Xᵉ)
```

### The morphisms in the slice category of types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  where

  hom-sliceᵉ :
    (Aᵉ → Xᵉ) → (Bᵉ → Xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  hom-sliceᵉ fᵉ gᵉ = Σᵉ (Aᵉ → Bᵉ) (λ hᵉ → fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ))

  map-hom-sliceᵉ :
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) → hom-sliceᵉ fᵉ gᵉ → Aᵉ → Bᵉ
  map-hom-sliceᵉ fᵉ gᵉ hᵉ = pr1ᵉ hᵉ

  triangle-hom-sliceᵉ :
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : hom-sliceᵉ fᵉ gᵉ) →
    fᵉ ~ᵉ gᵉ ∘ᵉ map-hom-sliceᵉ fᵉ gᵉ hᵉ
  triangle-hom-sliceᵉ fᵉ gᵉ hᵉ = pr2ᵉ hᵉ
```

## Properties

### We characterize the identity type of hom-slice

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  coherence-htpy-hom-sliceᵉ :
    (hᵉ h'ᵉ : hom-sliceᵉ fᵉ gᵉ) →
    map-hom-sliceᵉ fᵉ gᵉ hᵉ ~ᵉ map-hom-sliceᵉ fᵉ gᵉ h'ᵉ →
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-htpy-hom-sliceᵉ hᵉ h'ᵉ Hᵉ =
      coherence-triangle-homotopies'ᵉ
        ( triangle-hom-sliceᵉ fᵉ gᵉ h'ᵉ)
        ( gᵉ ·lᵉ Hᵉ)
        ( triangle-hom-sliceᵉ fᵉ gᵉ hᵉ)

  htpy-hom-sliceᵉ : (hᵉ h'ᵉ : hom-sliceᵉ fᵉ gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  htpy-hom-sliceᵉ hᵉ h'ᵉ =
    Σᵉ ( map-hom-sliceᵉ fᵉ gᵉ hᵉ ~ᵉ map-hom-sliceᵉ fᵉ gᵉ h'ᵉ)
      ( coherence-htpy-hom-sliceᵉ hᵉ h'ᵉ)

  extensionality-hom-sliceᵉ :
    (hᵉ h'ᵉ : hom-sliceᵉ fᵉ gᵉ) → (hᵉ ＝ᵉ h'ᵉ) ≃ᵉ htpy-hom-sliceᵉ hᵉ h'ᵉ
  extensionality-hom-sliceᵉ (pairᵉ hᵉ Hᵉ) =
    extensionality-Σᵉ
      ( λ {h'ᵉ} H'ᵉ (Kᵉ : hᵉ ~ᵉ h'ᵉ) → (Hᵉ ∙hᵉ (gᵉ ·lᵉ Kᵉ)) ~ᵉ H'ᵉ)
      ( refl-htpyᵉ)
      ( right-unit-htpyᵉ)
      ( λ h'ᵉ → equiv-funextᵉ)
      ( λ H'ᵉ → equiv-concat-htpyᵉ right-unit-htpyᵉ H'ᵉ ∘eᵉ equiv-funextᵉ)

  eq-htpy-hom-sliceᵉ :
    (hᵉ h'ᵉ : hom-sliceᵉ fᵉ gᵉ) → htpy-hom-sliceᵉ hᵉ h'ᵉ → hᵉ ＝ᵉ h'ᵉ
  eq-htpy-hom-sliceᵉ hᵉ h'ᵉ = map-inv-equivᵉ (extensionality-hom-sliceᵉ hᵉ h'ᵉ)
```

```agda
comp-hom-sliceᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Cᵉ → Xᵉ) →
  hom-sliceᵉ gᵉ hᵉ → hom-sliceᵉ fᵉ gᵉ → hom-sliceᵉ fᵉ hᵉ
pr1ᵉ (comp-hom-sliceᵉ fᵉ gᵉ hᵉ jᵉ iᵉ) = map-hom-sliceᵉ gᵉ hᵉ jᵉ ∘ᵉ map-hom-sliceᵉ fᵉ gᵉ iᵉ
pr2ᵉ (comp-hom-sliceᵉ fᵉ gᵉ hᵉ jᵉ iᵉ) =
  ( triangle-hom-sliceᵉ fᵉ gᵉ iᵉ) ∙hᵉ
  ( (triangle-hom-sliceᵉ gᵉ hᵉ jᵉ) ·rᵉ (map-hom-sliceᵉ fᵉ gᵉ iᵉ))

id-hom-sliceᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Xᵉ) → hom-sliceᵉ fᵉ fᵉ
pr1ᵉ (id-hom-sliceᵉ fᵉ) = idᵉ
pr2ᵉ (id-hom-sliceᵉ fᵉ) = refl-htpyᵉ

is-equiv-hom-sliceᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) → hom-sliceᵉ fᵉ gᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
is-equiv-hom-sliceᵉ fᵉ gᵉ hᵉ = is-equivᵉ (map-hom-sliceᵉ fᵉ gᵉ hᵉ)
```

### Morphisms in the slice are equivalently described as families of maps between fibers

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  where

  fiberwise-homᵉ : (Aᵉ → Xᵉ) → (Bᵉ → Xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  fiberwise-homᵉ fᵉ gᵉ = (xᵉ : Xᵉ) → fiberᵉ fᵉ xᵉ → fiberᵉ gᵉ xᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  fiberwise-hom-hom-sliceᵉ : hom-sliceᵉ fᵉ gᵉ → fiberwise-homᵉ fᵉ gᵉ
  fiberwise-hom-hom-sliceᵉ (pairᵉ hᵉ Hᵉ) = fiber-triangleᵉ fᵉ gᵉ hᵉ Hᵉ

  hom-slice-fiberwise-homᵉ : fiberwise-homᵉ fᵉ gᵉ → hom-sliceᵉ fᵉ gᵉ
  pr1ᵉ (hom-slice-fiberwise-homᵉ αᵉ) aᵉ = pr1ᵉ (αᵉ (fᵉ aᵉ) (pairᵉ aᵉ reflᵉ))
  pr2ᵉ (hom-slice-fiberwise-homᵉ αᵉ) aᵉ = invᵉ (pr2ᵉ (αᵉ (fᵉ aᵉ) (pairᵉ aᵉ reflᵉ)))

  is-section-hom-slice-fiberwise-hom-eq-htpyᵉ :
    (αᵉ : fiberwise-homᵉ fᵉ gᵉ) (xᵉ : Xᵉ) →
    (fiberwise-hom-hom-sliceᵉ (hom-slice-fiberwise-homᵉ αᵉ) xᵉ) ~ᵉ (αᵉ xᵉ)
  is-section-hom-slice-fiberwise-hom-eq-htpyᵉ αᵉ .(fᵉ aᵉ) (pairᵉ aᵉ reflᵉ) =
    eq-pair-eq-fiberᵉ (inv-invᵉ (pr2ᵉ (αᵉ (fᵉ aᵉ) (pairᵉ aᵉ reflᵉ))))

  is-section-hom-slice-fiberwise-homᵉ :
    (fiberwise-hom-hom-sliceᵉ ∘ᵉ hom-slice-fiberwise-homᵉ) ~ᵉ idᵉ
  is-section-hom-slice-fiberwise-homᵉ αᵉ =
    eq-htpyᵉ (λ xᵉ → eq-htpyᵉ (is-section-hom-slice-fiberwise-hom-eq-htpyᵉ αᵉ xᵉ))

  is-retraction-hom-slice-fiberwise-homᵉ :
    (hom-slice-fiberwise-homᵉ ∘ᵉ fiberwise-hom-hom-sliceᵉ) ~ᵉ idᵉ
  is-retraction-hom-slice-fiberwise-homᵉ (pairᵉ hᵉ Hᵉ) =
    eq-pair-eq-fiberᵉ (eq-htpyᵉ (inv-invᵉ ∘ᵉ Hᵉ))

  abstract
    is-equiv-fiberwise-hom-hom-sliceᵉ : is-equivᵉ (fiberwise-hom-hom-sliceᵉ)
    is-equiv-fiberwise-hom-hom-sliceᵉ =
      is-equiv-is-invertibleᵉ
        ( hom-slice-fiberwise-homᵉ)
        ( is-section-hom-slice-fiberwise-homᵉ)
        ( is-retraction-hom-slice-fiberwise-homᵉ)

  equiv-fiberwise-hom-hom-sliceᵉ : hom-sliceᵉ fᵉ gᵉ ≃ᵉ fiberwise-homᵉ fᵉ gᵉ
  pr1ᵉ equiv-fiberwise-hom-hom-sliceᵉ = fiberwise-hom-hom-sliceᵉ
  pr2ᵉ equiv-fiberwise-hom-hom-sliceᵉ = is-equiv-fiberwise-hom-hom-sliceᵉ

  abstract
    is-equiv-hom-slice-fiberwise-homᵉ : is-equivᵉ hom-slice-fiberwise-homᵉ
    is-equiv-hom-slice-fiberwise-homᵉ =
      is-equiv-is-invertibleᵉ
        ( fiberwise-hom-hom-sliceᵉ)
        ( is-retraction-hom-slice-fiberwise-homᵉ)
        ( is-section-hom-slice-fiberwise-homᵉ)

  equiv-hom-slice-fiberwise-homᵉ :
    fiberwise-homᵉ fᵉ gᵉ ≃ᵉ hom-sliceᵉ fᵉ gᵉ
  pr1ᵉ equiv-hom-slice-fiberwise-homᵉ = hom-slice-fiberwise-homᵉ
  pr2ᵉ equiv-hom-slice-fiberwise-homᵉ = is-equiv-hom-slice-fiberwise-homᵉ
```

### A morphism in the slice over `X` is an equivalence if and only if the induced map between fibers is a fiberwise equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  where

  equiv-sliceᵉ : (Aᵉ → Xᵉ) → (Bᵉ → Xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  equiv-sliceᵉ fᵉ gᵉ = Σᵉ (Aᵉ ≃ᵉ Bᵉ) (λ eᵉ → fᵉ ~ᵉ (gᵉ ∘ᵉ map-equivᵉ eᵉ))

  hom-equiv-sliceᵉ :
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) → equiv-sliceᵉ fᵉ gᵉ → hom-sliceᵉ fᵉ gᵉ
  pr1ᵉ (hom-equiv-sliceᵉ fᵉ gᵉ eᵉ) = pr1ᵉ (pr1ᵉ eᵉ)
  pr2ᵉ (hom-equiv-sliceᵉ fᵉ gᵉ eᵉ) = pr2ᵉ eᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  abstract
    is-fiberwise-equiv-fiberwise-equiv-equiv-sliceᵉ :
      (tᵉ : hom-sliceᵉ fᵉ gᵉ) → is-equivᵉ (pr1ᵉ tᵉ) →
      is-fiberwise-equivᵉ (fiberwise-hom-hom-sliceᵉ fᵉ gᵉ tᵉ)
    is-fiberwise-equiv-fiberwise-equiv-equiv-sliceᵉ (pairᵉ hᵉ Hᵉ) =
      is-fiberwise-equiv-is-equiv-triangleᵉ fᵉ gᵉ hᵉ Hᵉ

  abstract
    is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-sliceᵉ :
      (tᵉ : hom-sliceᵉ fᵉ gᵉ) →
      ((xᵉ : Xᵉ) → is-equivᵉ (fiberwise-hom-hom-sliceᵉ fᵉ gᵉ tᵉ xᵉ)) →
      is-equivᵉ (pr1ᵉ tᵉ)
    is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-sliceᵉ
      (pairᵉ hᵉ Hᵉ) =
      is-equiv-triangle-is-fiberwise-equivᵉ fᵉ gᵉ hᵉ Hᵉ

  equiv-fiberwise-equiv-equiv-sliceᵉ :
    equiv-sliceᵉ fᵉ gᵉ ≃ᵉ fiberwise-equivᵉ (fiberᵉ fᵉ) (fiberᵉ gᵉ)
  equiv-fiberwise-equiv-equiv-sliceᵉ =
    equiv-Σᵉ is-fiberwise-equivᵉ (equiv-fiberwise-hom-hom-sliceᵉ fᵉ gᵉ) αᵉ ∘eᵉ
    equiv-right-swap-Σᵉ
    where
    αᵉ :
      (hᵉ : hom-sliceᵉ fᵉ gᵉ) →
      is-equivᵉ (pr1ᵉ hᵉ) ≃ᵉ
      is-fiberwise-equivᵉ (map-equivᵉ (equiv-fiberwise-hom-hom-sliceᵉ fᵉ gᵉ) hᵉ)
    αᵉ hᵉ =
      equiv-iff-is-propᵉ
        ( is-property-is-equivᵉ _)
        ( is-prop-Πᵉ (λ _ → is-property-is-equivᵉ _))
        ( is-fiberwise-equiv-fiberwise-equiv-equiv-sliceᵉ hᵉ)
        ( is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-sliceᵉ hᵉ)

  equiv-equiv-slice-fiberwise-equivᵉ :
    fiberwise-equivᵉ (fiberᵉ fᵉ) (fiberᵉ gᵉ) ≃ᵉ equiv-sliceᵉ fᵉ gᵉ
  equiv-equiv-slice-fiberwise-equivᵉ =
    inv-equivᵉ equiv-fiberwise-equiv-equiv-sliceᵉ

  fiberwise-equiv-equiv-sliceᵉ :
    equiv-sliceᵉ fᵉ gᵉ → fiberwise-equivᵉ (fiberᵉ fᵉ) (fiberᵉ gᵉ)
  fiberwise-equiv-equiv-sliceᵉ =
    map-equivᵉ equiv-fiberwise-equiv-equiv-sliceᵉ

  equiv-fam-equiv-equiv-sliceᵉ :
    equiv-sliceᵉ fᵉ gᵉ ≃ᵉ ((xᵉ : Xᵉ) → fiberᵉ fᵉ xᵉ ≃ᵉ fiberᵉ gᵉ xᵉ) --ᵉ fam-equivᵉ (fiberᵉ fᵉ) (fiberᵉ gᵉ)
  equiv-fam-equiv-equiv-sliceᵉ =
    inv-distributive-Π-Σᵉ ∘eᵉ equiv-fiberwise-equiv-equiv-sliceᵉ
```

### The type of slice morphisms into an embedding is a proposition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  where

  abstract
    is-prop-hom-sliceᵉ :
      (fᵉ : Aᵉ → Xᵉ) (iᵉ : Bᵉ ↪ᵉ Xᵉ) → is-propᵉ (hom-sliceᵉ fᵉ (map-embᵉ iᵉ))
    is-prop-hom-sliceᵉ fᵉ iᵉ =
      is-prop-is-equivᵉ
        ( is-equiv-fiberwise-hom-hom-sliceᵉ fᵉ (map-embᵉ iᵉ))
        ( is-prop-Πᵉ
          ( λ xᵉ → is-prop-Πᵉ
            ( λ pᵉ → is-prop-map-is-embᵉ (is-emb-map-embᵉ iᵉ) xᵉ)))

  abstract
    is-equiv-hom-slice-embᵉ :
      (fᵉ : Aᵉ ↪ᵉ Xᵉ) (gᵉ : Bᵉ ↪ᵉ Xᵉ) (hᵉ : hom-sliceᵉ (map-embᵉ fᵉ) (map-embᵉ gᵉ)) →
      hom-sliceᵉ (map-embᵉ gᵉ) (map-embᵉ fᵉ) →
      is-equiv-hom-sliceᵉ (map-embᵉ fᵉ) (map-embᵉ gᵉ) hᵉ
    is-equiv-hom-slice-embᵉ fᵉ gᵉ hᵉ iᵉ =
      is-equiv-is-invertibleᵉ
        ( map-hom-sliceᵉ (map-embᵉ gᵉ) (map-embᵉ fᵉ) iᵉ)
        ( λ yᵉ →
          is-injective-embᵉ gᵉ
          ( invᵉ
            ( ( triangle-hom-sliceᵉ
                ( map-embᵉ gᵉ)
                ( map-embᵉ fᵉ)
                ( iᵉ)
                ( yᵉ)) ∙ᵉ
              ( triangle-hom-sliceᵉ
                ( map-embᵉ fᵉ)
                ( map-embᵉ gᵉ)
                ( hᵉ)
                ( map-hom-sliceᵉ (map-embᵉ gᵉ) (map-embᵉ fᵉ) iᵉ yᵉ)))))
        ( λ xᵉ →
          is-injective-embᵉ fᵉ
          ( invᵉ
            ( ( triangle-hom-sliceᵉ (map-embᵉ fᵉ) (map-embᵉ gᵉ) hᵉ xᵉ) ∙ᵉ
              ( triangle-hom-sliceᵉ (map-embᵉ gᵉ) (map-embᵉ fᵉ) iᵉ
                ( map-hom-sliceᵉ
                  ( map-embᵉ fᵉ)
                  ( map-embᵉ gᵉ)
                  ( hᵉ)
                  ( xᵉ))))))
```

### Characterization of the identity type of `Slice l A`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  equiv-slice'ᵉ : (fᵉ gᵉ : Sliceᵉ l2ᵉ Aᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equiv-slice'ᵉ fᵉ gᵉ = equiv-sliceᵉ (pr2ᵉ fᵉ) (pr2ᵉ gᵉ)

  id-equiv-Sliceᵉ : (fᵉ : Sliceᵉ l2ᵉ Aᵉ) → equiv-slice'ᵉ fᵉ fᵉ
  pr1ᵉ (id-equiv-Sliceᵉ fᵉ) = id-equivᵉ
  pr2ᵉ (id-equiv-Sliceᵉ fᵉ) = refl-htpyᵉ

  equiv-eq-Sliceᵉ : (fᵉ gᵉ : Sliceᵉ l2ᵉ Aᵉ) → fᵉ ＝ᵉ gᵉ → equiv-slice'ᵉ fᵉ gᵉ
  equiv-eq-Sliceᵉ fᵉ .fᵉ reflᵉ = id-equiv-Sliceᵉ fᵉ
```

### Univalence in a slice

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  abstract
    is-torsorial-equiv-slice'ᵉ :
      (fᵉ : Sliceᵉ l2ᵉ Aᵉ) → is-torsorialᵉ (equiv-slice'ᵉ fᵉ)
    is-torsorial-equiv-slice'ᵉ (pairᵉ Xᵉ fᵉ) =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-equivᵉ Xᵉ)
        ( pairᵉ Xᵉ id-equivᵉ)
        ( is-torsorial-htpyᵉ fᵉ)

  abstract
    is-equiv-equiv-eq-Sliceᵉ :
      (fᵉ gᵉ : Sliceᵉ l2ᵉ Aᵉ) → is-equivᵉ (equiv-eq-Sliceᵉ fᵉ gᵉ)
    is-equiv-equiv-eq-Sliceᵉ fᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-equiv-slice'ᵉ fᵉ)
        ( equiv-eq-Sliceᵉ fᵉ)

  extensionality-Sliceᵉ :
    (fᵉ gᵉ : Sliceᵉ l2ᵉ Aᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ equiv-slice'ᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-Sliceᵉ fᵉ gᵉ) = equiv-eq-Sliceᵉ fᵉ gᵉ
  pr2ᵉ (extensionality-Sliceᵉ fᵉ gᵉ) = is-equiv-equiv-eq-Sliceᵉ fᵉ gᵉ

  eq-equiv-sliceᵉ :
    (fᵉ gᵉ : Sliceᵉ l2ᵉ Aᵉ) → equiv-slice'ᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-equiv-sliceᵉ fᵉ gᵉ =
    map-inv-is-equivᵉ (is-equiv-equiv-eq-Sliceᵉ fᵉ gᵉ)
```

## See also

-ᵉ Forᵉ theᵉ formallyᵉ dualᵉ notionᵉ seeᵉ
  [`foundation.coslice`](foundation.coslice.md).ᵉ
-ᵉ Forᵉ slicesᵉ in theᵉ contextᵉ ofᵉ categoryᵉ theoryᵉ seeᵉ
  [`category-theory.slice-precategories`](category-theory.slice-precategories.md).ᵉ
-ᵉ Forᵉ fiberedᵉ mapsᵉ seeᵉ [`foundation.fibered-maps`](foundation.fibered-maps.md).ᵉ