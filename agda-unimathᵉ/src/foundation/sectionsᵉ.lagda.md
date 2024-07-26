# Sections

```agda
module foundation.sectionsᵉ where

open import foundation-core.sectionsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-triangles-of-homotopiesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.retracts-of-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
```

</details>

## Definitions

### Sections of the projection map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  map-section-familyᵉ : ((xᵉ : Aᵉ) → Bᵉ xᵉ) → (Aᵉ → Σᵉ Aᵉ Bᵉ)
  pr1ᵉ (map-section-familyᵉ bᵉ aᵉ) = aᵉ
  pr2ᵉ (map-section-familyᵉ bᵉ aᵉ) = bᵉ aᵉ

  htpy-map-section-familyᵉ :
    (bᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → (pr1ᵉ ∘ᵉ map-section-familyᵉ bᵉ) ~ᵉ idᵉ
  htpy-map-section-familyᵉ bᵉ aᵉ = reflᵉ

  section-dependent-functionᵉ : ((xᵉ : Aᵉ) → Bᵉ xᵉ) → sectionᵉ (pr1ᵉ {Bᵉ = Bᵉ})
  pr1ᵉ (section-dependent-functionᵉ bᵉ) = map-section-familyᵉ bᵉ
  pr2ᵉ (section-dependent-functionᵉ bᵉ) = htpy-map-section-familyᵉ bᵉ
```

## Properties

### Extensionality of sections

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  coherence-htpy-sectionᵉ :
    (sᵉ tᵉ : sectionᵉ fᵉ) → (map-sectionᵉ fᵉ sᵉ ~ᵉ map-sectionᵉ fᵉ tᵉ) → UUᵉ l2ᵉ
  coherence-htpy-sectionᵉ sᵉ tᵉ Hᵉ =
    coherence-triangle-homotopiesᵉ
      ( is-section-map-sectionᵉ fᵉ sᵉ)
      ( is-section-map-sectionᵉ fᵉ tᵉ)
      ( fᵉ ·lᵉ Hᵉ)

  htpy-sectionᵉ : (sᵉ tᵉ : sectionᵉ fᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-sectionᵉ sᵉ tᵉ =
    Σᵉ (map-sectionᵉ fᵉ sᵉ ~ᵉ map-sectionᵉ fᵉ tᵉ) (coherence-htpy-sectionᵉ sᵉ tᵉ)

  extensionality-sectionᵉ : (sᵉ tᵉ : sectionᵉ fᵉ) → (sᵉ ＝ᵉ tᵉ) ≃ᵉ htpy-sectionᵉ sᵉ tᵉ
  extensionality-sectionᵉ (sᵉ ,ᵉ Hᵉ) =
    extensionality-Σᵉ
      ( λ {s'ᵉ} H'ᵉ Kᵉ → Hᵉ ~ᵉ ((fᵉ ·lᵉ Kᵉ) ∙hᵉ H'ᵉ))
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( λ s'ᵉ → equiv-funextᵉ)
      ( λ H'ᵉ → equiv-funextᵉ)

  eq-htpy-sectionᵉ :
    (sᵉ tᵉ : sectionᵉ fᵉ)
    (Hᵉ : map-sectionᵉ fᵉ sᵉ ~ᵉ map-sectionᵉ fᵉ tᵉ)
    (Kᵉ : coherence-htpy-sectionᵉ sᵉ tᵉ Hᵉ) →
    sᵉ ＝ᵉ tᵉ
  eq-htpy-sectionᵉ sᵉ tᵉ Hᵉ Kᵉ =
    map-inv-equivᵉ (extensionality-sectionᵉ sᵉ tᵉ) (Hᵉ ,ᵉ Kᵉ)
```

### If the right factor of a composite has a section, then the type of sections of the left factor is a retract of the type of sections of the composite

```agda
is-retraction-section-left-map-triangleᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ)
  (Hᵉ : fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ)) (sᵉ : sectionᵉ hᵉ) →
  section-right-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ ∘ᵉ section-left-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ sᵉ ~ᵉ idᵉ
is-retraction-section-left-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ (kᵉ ,ᵉ Kᵉ) (lᵉ ,ᵉ Lᵉ) =
  eq-htpy-sectionᵉ
    ( ( section-right-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ ∘ᵉ
        section-left-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ (kᵉ ,ᵉ Kᵉ))
      ( lᵉ ,ᵉ Lᵉ))
    ( lᵉ ,ᵉ Lᵉ)
    ( Kᵉ ·rᵉ lᵉ)
    ( ( inv-htpy-assoc-htpyᵉ
        ( inv-htpyᵉ (Hᵉ ·rᵉ (kᵉ ∘ᵉ lᵉ)))
        ( Hᵉ ·rᵉ (kᵉ ∘ᵉ lᵉ))
        ( (gᵉ ·lᵉ (Kᵉ ·rᵉ lᵉ)) ∙hᵉ Lᵉ)) ∙hᵉ
      ( ap-concat-htpy'ᵉ ((gᵉ ·lᵉ (Kᵉ ·rᵉ lᵉ)) ∙hᵉ Lᵉ) (left-inv-htpyᵉ (Hᵉ ·rᵉ (kᵉ ∘ᵉ lᵉ)))))

section-left-factor-retract-of-section-compositionᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ)) →
  sectionᵉ hᵉ → (sectionᵉ gᵉ) retract-ofᵉ (sectionᵉ fᵉ)
pr1ᵉ (section-left-factor-retract-of-section-compositionᵉ fᵉ gᵉ hᵉ Hᵉ sᵉ) =
  section-left-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ sᵉ
pr1ᵉ (pr2ᵉ (section-left-factor-retract-of-section-compositionᵉ fᵉ gᵉ hᵉ Hᵉ sᵉ)) =
  section-right-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ

pr2ᵉ (pr2ᵉ (section-left-factor-retract-of-section-compositionᵉ fᵉ gᵉ hᵉ Hᵉ sᵉ)) =
  is-retraction-section-left-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ sᵉ
```

### The equivalence of sections of the projection map and sections of the type family

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  equiv-Π-section-pr1ᵉ : sectionᵉ (pr1ᵉ {Bᵉ = Bᵉ}) ≃ᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)
  equiv-Π-section-pr1ᵉ =
    ( left-unit-law-Σ-is-contrᵉ
      ( is-contr-equivᵉ
        ( Π-total-famᵉ (λ xᵉ yᵉ → yᵉ ＝ᵉ xᵉ))
        ( inv-distributive-Π-Σᵉ)
        ( is-contr-Πᵉ is-torsorial-Id'ᵉ))
      ( idᵉ ,ᵉ refl-htpyᵉ)) ∘eᵉ
    ( equiv-right-swap-Σᵉ) ∘eᵉ
    ( equiv-Σ-equiv-baseᵉ ( λ sᵉ → pr1ᵉ sᵉ ~ᵉ idᵉ) ( distributive-Π-Σᵉ))
```

### Any section of a type family is an equivalence if and only if each type in the family is contractible

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (bᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ)
  where

  is-equiv-map-section-familyᵉ :
    ((xᵉ : Aᵉ) → is-contrᵉ (Bᵉ xᵉ)) → is-equivᵉ (map-section-familyᵉ bᵉ)
  is-equiv-map-section-familyᵉ Cᵉ =
    is-equiv-top-map-triangleᵉ
      ( idᵉ)
      ( pr1ᵉ)
      ( map-section-familyᵉ bᵉ)
      ( htpy-map-section-familyᵉ bᵉ)
      ( is-equiv-pr1-is-contrᵉ Cᵉ)
      ( is-equiv-idᵉ)

  equiv-sectionᵉ :
    ((xᵉ : Aᵉ) → is-contrᵉ (Bᵉ xᵉ)) → Aᵉ ≃ᵉ Σᵉ Aᵉ Bᵉ
  pr1ᵉ (equiv-sectionᵉ Cᵉ) = map-section-familyᵉ bᵉ
  pr2ᵉ (equiv-sectionᵉ Cᵉ) = is-equiv-map-section-familyᵉ Cᵉ

  is-contr-fam-is-equiv-map-section-familyᵉ :
    is-equivᵉ (map-section-familyᵉ bᵉ) → ((xᵉ : Aᵉ) → is-contrᵉ (Bᵉ xᵉ))
  is-contr-fam-is-equiv-map-section-familyᵉ Hᵉ =
    is-contr-is-equiv-pr1ᵉ
      ( is-equiv-right-map-triangleᵉ idᵉ pr1ᵉ
        ( map-section-familyᵉ bᵉ)
        ( htpy-map-section-familyᵉ bᵉ)
        ( is-equiv-idᵉ)
        ( Hᵉ))
```

### Any section of a type family is an injective map

```agda
is-injective-map-section-familyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (bᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) →
  is-injectiveᵉ (map-section-familyᵉ bᵉ)
is-injective-map-section-familyᵉ bᵉ = apᵉ pr1ᵉ
```