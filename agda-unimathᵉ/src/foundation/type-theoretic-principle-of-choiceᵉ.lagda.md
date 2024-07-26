# The type theoretic principle of choice

```agda
module foundation.type-theoretic-principle-of-choiceᵉ where

open import foundation-core.type-theoretic-principle-of-choiceᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.implicit-function-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Aᵉ dependentᵉ functionᵉ takingᵉ valuesᵉ in aᵉ
[dependentᵉ pairᵉ type](foundation.dependent-pair-types.mdᵉ) isᵉ
[equivalently](foundation-core.equivalences.mdᵉ) describedᵉ asᵉ aᵉ pairᵉ ofᵉ dependentᵉ
functions.ᵉ Thisᵉ equivalence,ᵉ whichᵉ givesᵉ theᵉ distributivityᵉ ofᵉ Πᵉ overᵉ Σ,ᵉ isᵉ alsoᵉ
knownᵉ asᵉ theᵉ **typeᵉ theoreticᵉ principleᵉ ofᵉ choice**.ᵉ Indeed,ᵉ itᵉ isᵉ theᵉ
Curry-Howardᵉ interpretationᵉ ofᵉ (oneᵉ formulationᵉ ofᵉ) theᵉ
[axiomᵉ ofᵉ choice](foundation.axiom-of-choice.md).ᵉ

Inᵉ thisᵉ fileᵉ weᵉ record someᵉ furtherᵉ factsᵉ aboutᵉ theᵉ
[structures](foundation.structure.mdᵉ) introducedᵉ in
[`foundation-core.type-theoretic-principle-of-choice`](foundation-core.type-theoretic-principle-of-choice.md).ᵉ

Weᵉ relateᵉ precompositionᵉ ofᵉ mapsᵉ intoᵉ aᵉ dependentᵉ pairᵉ typeᵉ byᵉ aᵉ functionᵉ with
precompositionᵉ in dependentᵉ pairᵉ typesᵉ ofᵉ functionsᵉ in theᵉ fileᵉ
[`orthogonal-factorization-systems.precomposition-lifts-families-of-elements`](orthogonal-factorization-systems.precomposition-lifts-families-of-elements.md).ᵉ

## Lemma

### Characterizing the identity type of `universally-structured-Π`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ)
  where

  htpy-universally-structured-Πᵉ :
    (tᵉ t'ᵉ : universally-structured-Πᵉ Cᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  htpy-universally-structured-Πᵉ tᵉ t'ᵉ =
    universally-structured-Πᵉ
      ( λ (xᵉ : Aᵉ) (pᵉ : (pr1ᵉ tᵉ) xᵉ ＝ᵉ (pr1ᵉ t'ᵉ) xᵉ) →
        trᵉ (Cᵉ xᵉ) pᵉ ((pr2ᵉ tᵉ) xᵉ) ＝ᵉ (pr2ᵉ t'ᵉ) xᵉ)

  extensionality-universally-structured-Πᵉ :
    (tᵉ t'ᵉ : universally-structured-Πᵉ Cᵉ) →
    (tᵉ ＝ᵉ t'ᵉ) ≃ᵉ htpy-universally-structured-Πᵉ tᵉ t'ᵉ
  extensionality-universally-structured-Πᵉ (fᵉ ,ᵉ gᵉ) =
    extensionality-Σᵉ
      ( λ {f'ᵉ} g'ᵉ (Hᵉ : fᵉ ~ᵉ f'ᵉ) → (xᵉ : Aᵉ) → trᵉ (Cᵉ xᵉ) (Hᵉ xᵉ) (gᵉ xᵉ) ＝ᵉ g'ᵉ xᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( λ f'ᵉ → equiv-funextᵉ)
      ( λ g'ᵉ → equiv-funextᵉ)

  eq-htpy-universally-structured-Πᵉ :
    {tᵉ t'ᵉ : universally-structured-Πᵉ Cᵉ} →
    htpy-universally-structured-Πᵉ tᵉ t'ᵉ → tᵉ ＝ᵉ t'ᵉ
  eq-htpy-universally-structured-Πᵉ {tᵉ} {t'ᵉ} =
    map-inv-equivᵉ (extensionality-universally-structured-Πᵉ tᵉ t'ᵉ)
```

### Characterizing the identity type of `universally-structured-implicit-Π`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ)
  where

  htpy-universally-structured-implicit-Πᵉ :
    (tᵉ t'ᵉ : universally-structured-implicit-Πᵉ Cᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  htpy-universally-structured-implicit-Πᵉ tᵉ t'ᵉ =
    universally-structured-Πᵉ
      ( λ (xᵉ : Aᵉ) (pᵉ : (pr1ᵉ tᵉ) {xᵉ} ＝ᵉ (pr1ᵉ t'ᵉ) {xᵉ}) →
        trᵉ (Cᵉ xᵉ) pᵉ ((pr2ᵉ tᵉ) {xᵉ}) ＝ᵉ (pr2ᵉ t'ᵉ) {xᵉ})

  extensionality-universally-structured-implicit-Πᵉ :
    (tᵉ t'ᵉ : universally-structured-implicit-Πᵉ Cᵉ) →
    (tᵉ ＝ᵉ t'ᵉ) ≃ᵉ htpy-universally-structured-implicit-Πᵉ tᵉ t'ᵉ
  extensionality-universally-structured-implicit-Πᵉ (fᵉ ,ᵉ gᵉ) =
    extensionality-Σᵉ
      ( λ {f'ᵉ} g'ᵉ Hᵉ → (xᵉ : Aᵉ) → trᵉ (Cᵉ xᵉ) (Hᵉ xᵉ) (gᵉ {xᵉ}) ＝ᵉ g'ᵉ {xᵉ})
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( λ f'ᵉ → equiv-funext-implicitᵉ)
      ( λ g'ᵉ → equiv-funext-implicitᵉ)

  eq-htpy-universally-structured-implicit-Πᵉ :
    {tᵉ t'ᵉ : universally-structured-implicit-Πᵉ Cᵉ} →
    htpy-universally-structured-implicit-Πᵉ tᵉ t'ᵉ → tᵉ ＝ᵉ t'ᵉ
  eq-htpy-universally-structured-implicit-Πᵉ {tᵉ} {t'ᵉ} =
    map-inv-equivᵉ (extensionality-universally-structured-implicit-Πᵉ tᵉ t'ᵉ)
```

## Corollaries

### Characterizing the identity type of `Π-total-fam`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ)
  (fᵉ gᵉ : (aᵉ : Aᵉ) → Σᵉ (Bᵉ aᵉ) (Cᵉ aᵉ))
  where

  Eq-Π-total-famᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  Eq-Π-total-famᵉ =
    Π-total-famᵉ (λ xᵉ (pᵉ : pr1ᵉ (fᵉ xᵉ) ＝ᵉ pr1ᵉ (gᵉ xᵉ)) →
      trᵉ (Cᵉ xᵉ) pᵉ (pr2ᵉ (fᵉ xᵉ)) ＝ᵉ pr2ᵉ (gᵉ xᵉ))

  extensionality-Π-total-famᵉ : (fᵉ ＝ᵉ gᵉ) ≃ᵉ Eq-Π-total-famᵉ
  extensionality-Π-total-famᵉ =
    ( inv-distributive-Π-Σᵉ) ∘eᵉ
    ( extensionality-universally-structured-Πᵉ Cᵉ
      ( map-distributive-Π-Σᵉ fᵉ)
      ( map-distributive-Π-Σᵉ gᵉ)) ∘eᵉ
    ( equiv-apᵉ distributive-Π-Σᵉ fᵉ gᵉ)

  eq-Eq-Π-total-famᵉ : Eq-Π-total-famᵉ → fᵉ ＝ᵉ gᵉ
  eq-Eq-Π-total-famᵉ = map-inv-equivᵉ extensionality-Π-total-famᵉ
```

### Characterizing the identity type of `implicit-Π-total-fam`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ)
  (fᵉ gᵉ : {aᵉ : Aᵉ} → Σᵉ (Bᵉ aᵉ) (Cᵉ aᵉ))
  where

  extensionality-implicit-Π-total-famᵉ :
    (Idᵉ {Aᵉ = {aᵉ : Aᵉ} → Σᵉ (Bᵉ aᵉ) (Cᵉ aᵉ)} fᵉ gᵉ) ≃ᵉ
    Eq-Π-total-famᵉ Cᵉ (λ xᵉ → fᵉ {xᵉ}) (λ xᵉ → gᵉ {xᵉ})
  extensionality-implicit-Π-total-famᵉ =
    ( extensionality-Π-total-famᵉ Cᵉ (λ xᵉ → fᵉ {xᵉ}) (λ xᵉ → gᵉ {xᵉ})) ∘eᵉ
    ( equiv-apᵉ equiv-explicit-implicit-Πᵉ fᵉ gᵉ)

  eq-Eq-implicit-Π-total-famᵉ :
    Eq-Π-total-famᵉ Cᵉ (λ xᵉ → fᵉ {xᵉ}) (λ xᵉ → gᵉ {xᵉ}) →
    (Idᵉ {Aᵉ = {aᵉ : Aᵉ} → Σᵉ (Bᵉ aᵉ) (Cᵉ aᵉ)} fᵉ gᵉ)
  eq-Eq-implicit-Π-total-famᵉ = map-inv-equivᵉ extensionality-implicit-Π-total-famᵉ
```