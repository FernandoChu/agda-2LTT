# Invertible maps

```agda
module foundation.invertible-mapsᵉ where

open import foundation-core.invertible-mapsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-triangles-of-homotopiesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.full-subtypesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-algebraᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.coherently-invertible-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ

open import synthetic-homotopy-theory.free-loopsᵉ
```

</details>

## Properties

### Characterizing equality of invertible maps

#### Characterizing equality of `is-inverse`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ}
  where

  htpy-is-inverseᵉ : (sᵉ tᵉ : is-inverseᵉ fᵉ gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-is-inverseᵉ sᵉ tᵉ = (pr1ᵉ sᵉ ~ᵉ pr1ᵉ tᵉ) ×ᵉ (pr2ᵉ sᵉ ~ᵉ pr2ᵉ tᵉ)

  extensionality-is-inverseᵉ :
    {sᵉ tᵉ : is-inverseᵉ fᵉ gᵉ} → (sᵉ ＝ᵉ tᵉ) ≃ᵉ htpy-is-inverseᵉ sᵉ tᵉ
  extensionality-is-inverseᵉ {sᵉ} {tᵉ} =
    equiv-productᵉ equiv-funextᵉ equiv-funextᵉ ∘eᵉ equiv-pair-eqᵉ sᵉ tᵉ

  htpy-eq-is-inverseᵉ : {sᵉ tᵉ : is-inverseᵉ fᵉ gᵉ} → sᵉ ＝ᵉ tᵉ → htpy-is-inverseᵉ sᵉ tᵉ
  htpy-eq-is-inverseᵉ = map-equivᵉ extensionality-is-inverseᵉ

  eq-htpy-is-inverseᵉ : {sᵉ tᵉ : is-inverseᵉ fᵉ gᵉ} → htpy-is-inverseᵉ sᵉ tᵉ → sᵉ ＝ᵉ tᵉ
  eq-htpy-is-inverseᵉ = map-inv-equivᵉ extensionality-is-inverseᵉ
```

#### Characterizing equality of `is-invertible`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  coherence-htpy-is-invertibleᵉ :
    (sᵉ tᵉ : is-invertibleᵉ fᵉ) →
    map-inv-is-invertibleᵉ sᵉ ~ᵉ map-inv-is-invertibleᵉ tᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-htpy-is-invertibleᵉ sᵉ tᵉ Hᵉ =
    ( coherence-htpy-sectionᵉ {fᵉ = fᵉ}
      ( section-is-invertibleᵉ sᵉ)
      ( section-is-invertibleᵉ tᵉ)
      ( Hᵉ)) ×ᵉ
    ( coherence-htpy-retractionᵉ
      ( retraction-is-invertibleᵉ sᵉ)
      ( retraction-is-invertibleᵉ tᵉ)
      ( Hᵉ))

  htpy-is-invertibleᵉ : (sᵉ tᵉ : is-invertibleᵉ fᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-is-invertibleᵉ sᵉ tᵉ =
    Σᵉ ( map-inv-is-invertibleᵉ sᵉ ~ᵉ map-inv-is-invertibleᵉ tᵉ)
      ( coherence-htpy-is-invertibleᵉ sᵉ tᵉ)

  refl-htpy-is-invertibleᵉ : (sᵉ : is-invertibleᵉ fᵉ) → htpy-is-invertibleᵉ sᵉ sᵉ
  pr1ᵉ (refl-htpy-is-invertibleᵉ sᵉ) = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ (refl-htpy-is-invertibleᵉ sᵉ)) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ (refl-htpy-is-invertibleᵉ sᵉ)) = refl-htpyᵉ

  htpy-eq-is-invertibleᵉ :
    (sᵉ tᵉ : is-invertibleᵉ fᵉ) → sᵉ ＝ᵉ tᵉ → htpy-is-invertibleᵉ sᵉ tᵉ
  htpy-eq-is-invertibleᵉ sᵉ .sᵉ reflᵉ = refl-htpy-is-invertibleᵉ sᵉ

  is-torsorial-htpy-is-invertibleᵉ :
    (sᵉ : is-invertibleᵉ fᵉ) → is-torsorialᵉ (htpy-is-invertibleᵉ sᵉ)
  is-torsorial-htpy-is-invertibleᵉ sᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (map-inv-is-invertibleᵉ sᵉ))
      ( map-inv-is-invertibleᵉ sᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpyᵉ (is-section-map-inv-is-invertibleᵉ sᵉ))
        ( is-section-map-inv-is-invertibleᵉ sᵉ ,ᵉ refl-htpyᵉ)
        (is-torsorial-htpyᵉ (is-retraction-map-inv-is-invertibleᵉ sᵉ)))

  is-equiv-htpy-eq-is-invertibleᵉ :
    (sᵉ tᵉ : is-invertibleᵉ fᵉ) → is-equivᵉ (htpy-eq-is-invertibleᵉ sᵉ tᵉ)
  is-equiv-htpy-eq-is-invertibleᵉ sᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-is-invertibleᵉ sᵉ)
      ( htpy-eq-is-invertibleᵉ sᵉ)

  extensionality-is-invertibleᵉ :
    (sᵉ tᵉ : is-invertibleᵉ fᵉ) → (sᵉ ＝ᵉ tᵉ) ≃ᵉ (htpy-is-invertibleᵉ sᵉ tᵉ)
  pr1ᵉ (extensionality-is-invertibleᵉ sᵉ tᵉ) = htpy-eq-is-invertibleᵉ sᵉ tᵉ
  pr2ᵉ (extensionality-is-invertibleᵉ sᵉ tᵉ) = is-equiv-htpy-eq-is-invertibleᵉ sᵉ tᵉ

  eq-htpy-is-invertibleᵉ :
    (sᵉ tᵉ : is-invertibleᵉ fᵉ) → htpy-is-invertibleᵉ sᵉ tᵉ → sᵉ ＝ᵉ tᵉ
  eq-htpy-is-invertibleᵉ sᵉ tᵉ = map-inv-equivᵉ (extensionality-is-invertibleᵉ sᵉ tᵉ)
```

#### Characterizing equality of `invertible-map`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  coherence-htpy-invertible-mapᵉ :
    (sᵉ tᵉ : invertible-mapᵉ Aᵉ Bᵉ) →
    map-invertible-mapᵉ sᵉ ~ᵉ map-invertible-mapᵉ tᵉ →
    map-inv-invertible-mapᵉ sᵉ ~ᵉ map-inv-invertible-mapᵉ tᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-htpy-invertible-mapᵉ sᵉ tᵉ Hᵉ Iᵉ =
    ( coherence-triangle-homotopiesᵉ
      ( is-section-map-inv-invertible-mapᵉ sᵉ)
      ( is-section-map-inv-invertible-mapᵉ tᵉ)
      ( horizontal-concat-htpyᵉ Hᵉ Iᵉ)) ×ᵉ
    ( coherence-triangle-homotopiesᵉ
      ( is-retraction-map-inv-invertible-mapᵉ sᵉ)
      ( is-retraction-map-inv-invertible-mapᵉ tᵉ)
      ( horizontal-concat-htpyᵉ Iᵉ Hᵉ))

  htpy-invertible-mapᵉ : (sᵉ tᵉ : invertible-mapᵉ Aᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-invertible-mapᵉ sᵉ tᵉ =
    Σᵉ ( map-invertible-mapᵉ sᵉ ~ᵉ map-invertible-mapᵉ tᵉ)
      ( λ Hᵉ →
        Σᵉ ( map-inv-invertible-mapᵉ sᵉ ~ᵉ map-inv-invertible-mapᵉ tᵉ)
          ( coherence-htpy-invertible-mapᵉ sᵉ tᵉ Hᵉ))

  refl-htpy-invertible-mapᵉ : (sᵉ : invertible-mapᵉ Aᵉ Bᵉ) → htpy-invertible-mapᵉ sᵉ sᵉ
  pr1ᵉ (refl-htpy-invertible-mapᵉ sᵉ) = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ (refl-htpy-invertible-mapᵉ sᵉ)) = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (refl-htpy-invertible-mapᵉ sᵉ))) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (refl-htpy-invertible-mapᵉ sᵉ))) = refl-htpyᵉ

  htpy-eq-invertible-mapᵉ :
    (sᵉ tᵉ : invertible-mapᵉ Aᵉ Bᵉ) → sᵉ ＝ᵉ tᵉ → htpy-invertible-mapᵉ sᵉ tᵉ
  htpy-eq-invertible-mapᵉ sᵉ .sᵉ reflᵉ = refl-htpy-invertible-mapᵉ sᵉ

  is-torsorial-htpy-invertible-mapᵉ :
    (sᵉ : invertible-mapᵉ Aᵉ Bᵉ) → is-torsorialᵉ (htpy-invertible-mapᵉ sᵉ)
  is-torsorial-htpy-invertible-mapᵉ sᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (map-invertible-mapᵉ sᵉ))
      ( map-invertible-mapᵉ sᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpyᵉ (map-inv-invertible-mapᵉ sᵉ))
        ( map-inv-invertible-mapᵉ sᵉ ,ᵉ refl-htpyᵉ)
        ( is-torsorial-Eq-structureᵉ
          ( is-torsorial-htpyᵉ (is-section-map-inv-invertible-mapᵉ sᵉ))
          ( is-section-map-inv-invertible-mapᵉ sᵉ ,ᵉ refl-htpyᵉ)
          ( is-torsorial-htpyᵉ (is-retraction-map-inv-invertible-mapᵉ sᵉ))))

  is-equiv-htpy-eq-invertible-mapᵉ :
    (sᵉ tᵉ : invertible-mapᵉ Aᵉ Bᵉ) → is-equivᵉ (htpy-eq-invertible-mapᵉ sᵉ tᵉ)
  is-equiv-htpy-eq-invertible-mapᵉ sᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-invertible-mapᵉ sᵉ)
      ( htpy-eq-invertible-mapᵉ sᵉ)

  extensionality-invertible-mapᵉ :
    (sᵉ tᵉ : invertible-mapᵉ Aᵉ Bᵉ) → (sᵉ ＝ᵉ tᵉ) ≃ᵉ (htpy-invertible-mapᵉ sᵉ tᵉ)
  pr1ᵉ (extensionality-invertible-mapᵉ sᵉ tᵉ) = htpy-eq-invertible-mapᵉ sᵉ tᵉ
  pr2ᵉ (extensionality-invertible-mapᵉ sᵉ tᵉ) = is-equiv-htpy-eq-invertible-mapᵉ sᵉ tᵉ

  eq-htpy-invertible-mapᵉ :
    (sᵉ tᵉ : invertible-mapᵉ Aᵉ Bᵉ) → htpy-invertible-mapᵉ sᵉ tᵉ → sᵉ ＝ᵉ tᵉ
  eq-htpy-invertible-mapᵉ sᵉ tᵉ = map-inv-equivᵉ (extensionality-invertible-mapᵉ sᵉ tᵉ)
```

### If the domains are `k`-truncated, then the type of inverses is `k`-truncated

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-trunc-is-inverseᵉ :
    (fᵉ : Aᵉ → Bᵉ) (gᵉ : Bᵉ → Aᵉ) →
    is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) Bᵉ →
    is-truncᵉ kᵉ (is-inverseᵉ fᵉ gᵉ)
  is-trunc-is-inverseᵉ fᵉ gᵉ is-trunc-Aᵉ is-trunc-Bᵉ =
    is-trunc-productᵉ kᵉ
      ( is-trunc-Πᵉ kᵉ (λ xᵉ → is-trunc-Bᵉ (fᵉ (gᵉ xᵉ)) xᵉ))
      ( is-trunc-Πᵉ kᵉ (λ xᵉ → is-trunc-Aᵉ (gᵉ (fᵉ xᵉ)) xᵉ))

  is-trunc-is-invertibleᵉ :
    (fᵉ : Aᵉ → Bᵉ) →
    is-truncᵉ kᵉ Aᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) Bᵉ →
    is-truncᵉ kᵉ (is-invertibleᵉ fᵉ)
  is-trunc-is-invertibleᵉ fᵉ is-trunc-Aᵉ is-trunc-Bᵉ =
    is-trunc-Σᵉ
      ( is-trunc-function-typeᵉ kᵉ is-trunc-Aᵉ)
      ( λ gᵉ →
        is-trunc-is-inverseᵉ fᵉ gᵉ
          ( is-trunc-succ-is-truncᵉ kᵉ is-trunc-Aᵉ)
          ( is-trunc-Bᵉ))

  is-trunc-invertible-mapᵉ :
    is-truncᵉ kᵉ Aᵉ → is-truncᵉ kᵉ Bᵉ →
    is-truncᵉ kᵉ (invertible-mapᵉ Aᵉ Bᵉ)
  is-trunc-invertible-mapᵉ is-trunc-Aᵉ is-trunc-Bᵉ =
    is-trunc-Σᵉ
      ( is-trunc-function-typeᵉ kᵉ is-trunc-Bᵉ)
      ( λ fᵉ →
        is-trunc-is-invertibleᵉ fᵉ
          ( is-trunc-Aᵉ)
          ( is-trunc-succ-is-truncᵉ kᵉ is-trunc-Bᵉ))
```

### The type `is-invertible id` is equivalent to `id ~ id`

```agda
is-invertible-id-htpy-id-idᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) →
  (idᵉ {Aᵉ = Aᵉ} ~ᵉ idᵉ {Aᵉ = Aᵉ}) → is-invertibleᵉ (idᵉ {Aᵉ = Aᵉ})
pr1ᵉ (is-invertible-id-htpy-id-idᵉ Aᵉ Hᵉ) = idᵉ
pr1ᵉ (pr2ᵉ (is-invertible-id-htpy-id-idᵉ Aᵉ Hᵉ)) = refl-htpyᵉ
pr2ᵉ (pr2ᵉ (is-invertible-id-htpy-id-idᵉ Aᵉ Hᵉ)) = Hᵉ

triangle-is-invertible-id-htpy-id-idᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) →
  ( is-invertible-id-htpy-id-idᵉ Aᵉ) ~ᵉ
    ( ( map-associative-Σᵉ
        ( Aᵉ → Aᵉ)
        ( λ gᵉ → (idᵉ ∘ᵉ gᵉ) ~ᵉ idᵉ)
        ( λ sᵉ → (pr1ᵉ sᵉ ∘ᵉ idᵉ) ~ᵉ idᵉ)) ∘ᵉ
      ( map-inv-left-unit-law-Σ-is-contrᵉ
        { Bᵉ = λ sᵉ → (pr1ᵉ sᵉ ∘ᵉ idᵉ) ~ᵉ idᵉ}
        ( is-contr-section-is-equivᵉ (is-equiv-idᵉ {ᵉ_} {Aᵉ}))
        ( pairᵉ idᵉ refl-htpyᵉ)))
triangle-is-invertible-id-htpy-id-idᵉ Aᵉ Hᵉ = reflᵉ

abstract
  is-equiv-is-invertible-id-htpy-id-idᵉ :
    {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → is-equivᵉ (is-invertible-id-htpy-id-idᵉ Aᵉ)
  is-equiv-is-invertible-id-htpy-id-idᵉ Aᵉ =
    is-equiv-left-map-triangleᵉ
      ( is-invertible-id-htpy-id-idᵉ Aᵉ)
      ( map-associative-Σᵉ
        ( Aᵉ → Aᵉ)
        ( λ gᵉ → (idᵉ ∘ᵉ gᵉ) ~ᵉ idᵉ)
        ( λ sᵉ → (pr1ᵉ sᵉ ∘ᵉ idᵉ) ~ᵉ idᵉ))
      ( map-inv-left-unit-law-Σ-is-contrᵉ
        ( is-contr-section-is-equivᵉ is-equiv-idᵉ)
        ( pairᵉ idᵉ refl-htpyᵉ))
      ( triangle-is-invertible-id-htpy-id-idᵉ Aᵉ)
      ( is-equiv-map-inv-left-unit-law-Σ-is-contrᵉ
        ( is-contr-section-is-equivᵉ is-equiv-idᵉ)
        ( pairᵉ idᵉ refl-htpyᵉ))
      ( is-equiv-map-associative-Σᵉ _ _ _)
```

### The type of invertible maps is equivalent to the type of free loops on equivalences

#### The type of invertible equivalences is equivalent to the type of invertible maps

**Proof:**ᵉ Sinceᵉ everyᵉ invertibleᵉ mapᵉ isᵉ anᵉ equivalence,ᵉ theᵉ `Σ`-typeᵉ ofᵉ
invertibleᵉ mapsᵉ whichᵉ areᵉ equivalencesᵉ formsᵉ aᵉ fullᵉ subtypeᵉ ofᵉ theᵉ typeᵉ ofᵉ
invertibleᵉ maps.ᵉ Swappingᵉ theᵉ orderᵉ ofᵉ `Σ`-typesᵉ thenᵉ showsᵉ thatᵉ theᵉ `Σ`-typeᵉ ofᵉ
invertibleᵉ mapsᵉ whichᵉ areᵉ equivalencesᵉ isᵉ equivalentᵉ to theᵉ `Σ`-typeᵉ ofᵉ
equivalencesᵉ whichᵉ areᵉ invertible.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-equiv-prop-is-invertibleᵉ : (invertible-mapᵉ Aᵉ Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-equiv-prop-is-invertibleᵉ = is-equiv-Propᵉ ∘ᵉ map-invertible-mapᵉ

  is-full-subtype-is-equiv-prop-is-invertibleᵉ :
    is-full-subtypeᵉ is-equiv-prop-is-invertibleᵉ
  is-full-subtype-is-equiv-prop-is-invertibleᵉ =
    is-equiv-is-invertible'ᵉ ∘ᵉ is-invertible-map-invertible-mapᵉ

  equiv-invertible-equivalence-invertible-mapᵉ :
    Σᵉ (Aᵉ ≃ᵉ Bᵉ) (is-invertibleᵉ ∘ᵉ map-equivᵉ) ≃ᵉ invertible-mapᵉ Aᵉ Bᵉ
  equiv-invertible-equivalence-invertible-mapᵉ =
    ( equiv-inclusion-is-full-subtypeᵉ
      ( is-equiv-prop-is-invertibleᵉ)
      ( is-full-subtype-is-equiv-prop-is-invertibleᵉ)) ∘eᵉ
    ( equiv-right-swap-Σᵉ)
```

#### The type of free loops on equivalences is equivalent to the type of invertible equivalences

**Proof:**ᵉ First,ᵉ associatingᵉ theᵉ orderᵉ ofᵉ `Σ`-typesᵉ showsᵉ thatᵉ aᵉ functionᵉ beingᵉ
invertibleᵉ isᵉ equivalentᵉ to itᵉ havingᵉ aᵉ section,ᵉ suchᵉ thatᵉ thisᵉ sectionᵉ isᵉ alsoᵉ
itsᵉ retraction.ᵉ Now,ᵉ sinceᵉ equivalencesᵉ haveᵉ aᵉ contractibleᵉ typeᵉ ofᵉ sections,ᵉ aᵉ
proofᵉ ofᵉ invertibilityᵉ ofᵉ theᵉ underlyingᵉ mapᵉ `f`ᵉ ofᵉ anᵉ equivalenceᵉ contractsᵉ to
justᵉ aᵉ singleᵉ homotopyᵉ `gᵉ ∘ᵉ fᵉ ~ᵉ id`,ᵉ showingᵉ thatᵉ aᵉ sectionᵉ `g`ᵉ ofᵉ `f`ᵉ isᵉ alsoᵉ
itsᵉ retraction.ᵉ Asᵉ `g`ᵉ isᵉ aᵉ section,ᵉ composingᵉ onᵉ theᵉ leftᵉ with `f`ᵉ andᵉ
cancelingᵉ `fᵉ ∘ᵉ g`ᵉ yieldsᵉ aᵉ loopᵉ `fᵉ ~ᵉ f`.ᵉ Byᵉ equivalenceᵉ extensionality,ᵉ thisᵉ
loopᵉ mayᵉ beᵉ liftedᵉ to aᵉ loopᵉ onᵉ theᵉ entireᵉ equivalence.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  equiv-is-retraction-section-is-invertibleᵉ :
    (fᵉ : Aᵉ → Bᵉ) →
    Σᵉ (sectionᵉ fᵉ) (λ gᵉ → (map-sectionᵉ fᵉ gᵉ) ∘ᵉ fᵉ ~ᵉ idᵉ) ≃ᵉ is-invertibleᵉ fᵉ
  equiv-is-retraction-section-is-invertibleᵉ fᵉ =
    associative-Σᵉ
      ( Bᵉ → Aᵉ)
      ( λ gᵉ → fᵉ ∘ᵉ gᵉ ~ᵉ idᵉ)
      ( λ gᵉ → (map-sectionᵉ fᵉ gᵉ) ∘ᵉ fᵉ ~ᵉ idᵉ)

  equiv-free-loop-equivalence-invertible-equivalenceᵉ :
    free-loopᵉ (Aᵉ ≃ᵉ Bᵉ) ≃ᵉ Σᵉ (Aᵉ ≃ᵉ Bᵉ) (is-invertibleᵉ ∘ᵉ map-equivᵉ)
  equiv-free-loop-equivalence-invertible-equivalenceᵉ =
    ( equiv-totᵉ
      ( equiv-is-retraction-section-is-invertibleᵉ ∘ᵉ map-equivᵉ)) ∘eᵉ
    ( equiv-totᵉ
      ( λ fᵉ →
        ( inv-left-unit-law-Σ-is-contrᵉ
          ( is-contr-section-is-equivᵉ (is-equiv-map-equivᵉ fᵉ))
          ( section-is-equivᵉ (is-equiv-map-equivᵉ fᵉ))) ∘eᵉ
        ( inv-equivᵉ
          ( equiv-htpy-postcomp-htpyᵉ
            ( fᵉ)
            ( map-section-is-equivᵉ (is-equiv-map-equivᵉ fᵉ) ∘ᵉ map-equivᵉ fᵉ)
            ( idᵉ))) ∘eᵉ
        ( equiv-concat-htpyᵉ
          ( is-section-map-section-map-equivᵉ fᵉ ·rᵉ map-equivᵉ fᵉ)
          ( map-equivᵉ fᵉ)))) ∘eᵉ
    ( equiv-totᵉ (λ fᵉ → extensionality-equivᵉ fᵉ fᵉ))
```

#### The equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  equiv-free-loop-equivalence-invertible-mapᵉ :
    free-loopᵉ (Aᵉ ≃ᵉ Bᵉ) ≃ᵉ invertible-mapᵉ Aᵉ Bᵉ
  equiv-free-loop-equivalence-invertible-mapᵉ =
    equiv-invertible-equivalence-invertible-mapᵉ ∘eᵉ
    equiv-free-loop-equivalence-invertible-equivalenceᵉ
```

### The action of invertible maps on identifications is invertible

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  (Hᵉ : is-invertibleᵉ fᵉ) {xᵉ yᵉ : Aᵉ}
  where

  is-invertible-ap-is-invertibleᵉ : is-invertibleᵉ (apᵉ fᵉ {xᵉ} {yᵉ})
  is-invertible-ap-is-invertibleᵉ =
    is-invertible-ap-is-coherently-invertibleᵉ
      ( is-coherently-invertible-is-invertibleᵉ Hᵉ)
```

## See also

-ᵉ Forᵉ theᵉ coherentᵉ notionᵉ ofᵉ invertibleᵉ mapsᵉ seeᵉ
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ biinvertibleᵉ mapsᵉ seeᵉ
  [`foundation.equivalences`](foundation.equivalences.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ mapsᵉ with contractibleᵉ fibersᵉ seeᵉ
  [`foundation.contractible-maps`](foundation.contractible-maps.md).ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ path-splitᵉ mapsᵉ seeᵉ
  [`foundation.path-split-maps`](foundation.path-split-maps.md).ᵉ