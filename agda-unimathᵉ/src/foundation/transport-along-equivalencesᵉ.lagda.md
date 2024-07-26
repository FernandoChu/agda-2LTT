# Transport along equivalences

```agda
module foundation.transport-along-equivalencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-equivalences-functionsᵉ
open import foundation.action-on-equivalences-type-familiesᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalence-inductionᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
```

</details>

## Idea

Givenᵉ aᵉ mapᵉ betweenᵉ universesᵉ `fᵉ : 𝒰ᵉ → 𝒱`,ᵉ applyingᵉ
[transportᵉ alongᵉ identifications](foundation-core.transport-along-identifications.mdᵉ)
to [identifications](foundation-core.identity-types.mdᵉ) arisingᵉ fromᵉ theᵉ
[univalenceᵉ axiom](foundation.univalence.mdᵉ) givesᵉ usᵉ
{{#conceptᵉ "transportᵉ alongᵉ equivalences"ᵉ Agda=tr-equivᵉ}}:

```text
  tr-equivᵉ fᵉ : Xᵉ ≃ᵉ Yᵉ → fᵉ Xᵉ ≃ᵉ fᵉ Y.ᵉ
```

Alternatively,ᵉ weᵉ couldᵉ applyᵉ theᵉ
[actionᵉ onᵉ identifications](foundation.action-on-identifications-functions.mdᵉ)
to getᵉ anotherᵉ
[actionᵉ onᵉ equivalences](foundation.action-on-equivalences-functions.md).ᵉ
However,ᵉ byᵉ univalenceᵉ suchᵉ aᵉ mapᵉ mustᵉ alsoᵉ beᵉ unique,ᵉ henceᵉ theseᵉ twoᵉ
constructionsᵉ coincide.ᵉ

## Definitions

### Transporting along equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} (fᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ) {Xᵉ Yᵉ : UUᵉ l1ᵉ}
  where

  map-tr-equivᵉ : Xᵉ ≃ᵉ Yᵉ → fᵉ Xᵉ → fᵉ Yᵉ
  map-tr-equivᵉ eᵉ = trᵉ fᵉ (eq-equivᵉ eᵉ)

  abstract
    is-equiv-map-tr-equivᵉ : (eᵉ : Xᵉ ≃ᵉ Yᵉ) → is-equivᵉ (map-tr-equivᵉ eᵉ)
    is-equiv-map-tr-equivᵉ eᵉ = is-equiv-trᵉ fᵉ (eq-equivᵉ eᵉ)

  tr-equivᵉ : Xᵉ ≃ᵉ Yᵉ → fᵉ Xᵉ ≃ᵉ fᵉ Yᵉ
  pr1ᵉ (tr-equivᵉ eᵉ) = map-tr-equivᵉ eᵉ
  pr2ᵉ (tr-equivᵉ eᵉ) = is-equiv-map-tr-equivᵉ eᵉ

  eq-tr-equivᵉ : Xᵉ ≃ᵉ Yᵉ → fᵉ Xᵉ ＝ᵉ fᵉ Yᵉ
  eq-tr-equivᵉ = eq-equivᵉ ∘ᵉ tr-equivᵉ
```

### Transporting along inverse equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} (fᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ) {Xᵉ Yᵉ : UUᵉ l1ᵉ}
  where

  map-tr-inv-equivᵉ : Xᵉ ≃ᵉ Yᵉ → fᵉ Yᵉ → fᵉ Xᵉ
  map-tr-inv-equivᵉ eᵉ = trᵉ fᵉ (eq-equivᵉ (inv-equivᵉ eᵉ))

  abstract
    is-equiv-map-tr-inv-equivᵉ : (eᵉ : Xᵉ ≃ᵉ Yᵉ) → is-equivᵉ (map-tr-inv-equivᵉ eᵉ)
    is-equiv-map-tr-inv-equivᵉ eᵉ = is-equiv-trᵉ fᵉ (eq-equivᵉ (inv-equivᵉ eᵉ))

  tr-inv-equivᵉ : Xᵉ ≃ᵉ Yᵉ → fᵉ Yᵉ ≃ᵉ fᵉ Xᵉ
  pr1ᵉ (tr-inv-equivᵉ eᵉ) = map-tr-inv-equivᵉ eᵉ
  pr2ᵉ (tr-inv-equivᵉ eᵉ) = is-equiv-map-tr-inv-equivᵉ eᵉ

  eq-tr-inv-equivᵉ : Xᵉ ≃ᵉ Yᵉ → fᵉ Yᵉ ＝ᵉ fᵉ Xᵉ
  eq-tr-inv-equivᵉ = eq-equivᵉ ∘ᵉ tr-inv-equivᵉ
```

## Properties

### Transporting along `id-equiv` is the identity equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} (fᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ) {Xᵉ : UUᵉ l1ᵉ}
  where

  compute-map-tr-equiv-id-equivᵉ : map-tr-equivᵉ fᵉ id-equivᵉ ＝ᵉ idᵉ
  compute-map-tr-equiv-id-equivᵉ = apᵉ (trᵉ fᵉ) (compute-eq-equiv-id-equivᵉ Xᵉ)

  compute-tr-equiv-id-equivᵉ : tr-equivᵉ fᵉ id-equivᵉ ＝ᵉ id-equivᵉ
  compute-tr-equiv-id-equivᵉ =
    is-injective-map-equivᵉ (apᵉ (trᵉ fᵉ) (compute-eq-equiv-id-equivᵉ Xᵉ))
```

### Transport along equivalences preserves composition of equivalences

Forᵉ anyᵉ operationᵉ `fᵉ : 𝒰₁ᵉ → 𝒰₂`ᵉ andᵉ anyᵉ twoᵉ composableᵉ equivalencesᵉ `eᵉ : Xᵉ ≃ᵉ Y`ᵉ
andᵉ `e'ᵉ : Yᵉ ≃ᵉ Z`ᵉ in `𝒰₁`ᵉ weᵉ obtainᵉ aᵉ commutingᵉ triangleᵉ

```text
                     tr-equivᵉ fᵉ eᵉ
                 fᵉ Xᵉ ---------->ᵉ fᵉ Yᵉ
                     \ᵉ         /ᵉ
  tr-equivᵉ fᵉ (e'ᵉ ∘ᵉ eᵉ) \ᵉ       /ᵉ tr-equivᵉ fᵉ e'ᵉ
                       \ᵉ     /ᵉ
                        ∨ᵉ   ∨ᵉ
                         fᵉ Zᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} (fᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ)
  {Xᵉ Yᵉ Zᵉ : UUᵉ l1ᵉ} (eᵉ : Xᵉ ≃ᵉ Yᵉ) (e'ᵉ : Yᵉ ≃ᵉ Zᵉ)
  where

  distributive-map-tr-equiv-equiv-compᵉ :
    coherence-triangle-mapsᵉ
      ( map-tr-equivᵉ fᵉ (e'ᵉ ∘eᵉ eᵉ))
      ( map-tr-equivᵉ fᵉ e'ᵉ)
      ( map-tr-equivᵉ fᵉ eᵉ)
  distributive-map-tr-equiv-equiv-compᵉ xᵉ =
    ( invᵉ (apᵉ (λ pᵉ → trᵉ fᵉ pᵉ xᵉ) (compute-eq-equiv-comp-equivᵉ eᵉ e'ᵉ))) ∙ᵉ
    ( tr-concatᵉ (eq-equivᵉ eᵉ) (eq-equivᵉ e'ᵉ) xᵉ)

  distributive-tr-equiv-equiv-compᵉ :
    tr-equivᵉ fᵉ (e'ᵉ ∘eᵉ eᵉ) ＝ᵉ tr-equivᵉ fᵉ e'ᵉ ∘eᵉ tr-equivᵉ fᵉ eᵉ
  distributive-tr-equiv-equiv-compᵉ =
    eq-htpy-equivᵉ distributive-map-tr-equiv-equiv-compᵉ
```

### Transporting along an inverse equivalence is inverse to transporting along the original equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} (fᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ)
  {Xᵉ Yᵉ : UUᵉ l1ᵉ} (eᵉ : Xᵉ ≃ᵉ Yᵉ)
  where

  is-section-map-tr-inv-equivᵉ :
    is-sectionᵉ (map-tr-equivᵉ fᵉ eᵉ) (map-tr-equivᵉ fᵉ (inv-equivᵉ eᵉ))
  is-section-map-tr-inv-equivᵉ xᵉ =
    ( invᵉ
      ( apᵉ
        ( map-tr-equivᵉ fᵉ eᵉ ∘ᵉ (λ pᵉ → trᵉ fᵉ pᵉ xᵉ))
        ( commutativity-inv-eq-equivᵉ eᵉ))) ∙ᵉ
    ( is-section-inv-trᵉ fᵉ (eq-equivᵉ eᵉ) xᵉ)

  is-retraction-map-tr-inv-equivᵉ :
    is-retractionᵉ (map-tr-equivᵉ fᵉ eᵉ) (map-tr-equivᵉ fᵉ (inv-equivᵉ eᵉ))
  is-retraction-map-tr-inv-equivᵉ xᵉ =
    ( invᵉ
      ( apᵉ
        ( λ pᵉ → trᵉ fᵉ pᵉ (map-tr-equivᵉ fᵉ eᵉ xᵉ))
        ( commutativity-inv-eq-equivᵉ eᵉ))) ∙ᵉ
    ( is-retraction-inv-trᵉ fᵉ (eq-equivᵉ eᵉ) xᵉ)
```

### Transposing transport along the inverse of an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} (fᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ)
  {Xᵉ Yᵉ : UUᵉ l1ᵉ} (eᵉ : Xᵉ ≃ᵉ Yᵉ) {uᵉ : fᵉ Xᵉ} {vᵉ : fᵉ Yᵉ}
  where

  eq-transpose-map-tr-equivᵉ :
    vᵉ ＝ᵉ map-tr-equivᵉ fᵉ eᵉ uᵉ → map-tr-equivᵉ fᵉ (inv-equivᵉ eᵉ) vᵉ ＝ᵉ uᵉ
  eq-transpose-map-tr-equivᵉ pᵉ =
    apᵉ (map-tr-equivᵉ fᵉ (inv-equivᵉ eᵉ)) pᵉ ∙ᵉ is-retraction-map-tr-inv-equivᵉ fᵉ eᵉ uᵉ

  eq-transpose-map-tr-equiv'ᵉ :
    map-tr-equivᵉ fᵉ eᵉ uᵉ ＝ᵉ vᵉ → uᵉ ＝ᵉ map-tr-equivᵉ fᵉ (inv-equivᵉ eᵉ) vᵉ
  eq-transpose-map-tr-equiv'ᵉ pᵉ =
    ( invᵉ (is-retraction-map-tr-inv-equivᵉ fᵉ eᵉ uᵉ)) ∙ᵉ
    ( apᵉ (map-tr-equivᵉ fᵉ (inv-equivᵉ eᵉ)) pᵉ)
```

### Substitution law for transport along equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (gᵉ : UUᵉ l2ᵉ → UUᵉ l3ᵉ) (fᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ) {Xᵉ Yᵉ : UUᵉ l1ᵉ}
  (eᵉ : Xᵉ ≃ᵉ Yᵉ)
  where

  substitution-map-tr-equivᵉ :
    map-tr-equivᵉ gᵉ (action-equiv-familyᵉ fᵉ eᵉ) ~ᵉ map-tr-equivᵉ (gᵉ ∘ᵉ fᵉ) eᵉ
  substitution-map-tr-equivᵉ X'ᵉ =
    ( apᵉ
      ( λ pᵉ → trᵉ gᵉ pᵉ X'ᵉ)
      ( is-retraction-eq-equivᵉ (action-equiv-functionᵉ fᵉ eᵉ))) ∙ᵉ
    ( substitution-law-trᵉ gᵉ fᵉ (eq-equivᵉ eᵉ))

  substitution-law-tr-equivᵉ :
    tr-equivᵉ gᵉ (action-equiv-familyᵉ fᵉ eᵉ) ＝ᵉ tr-equivᵉ (gᵉ ∘ᵉ fᵉ) eᵉ
  substitution-law-tr-equivᵉ = eq-htpy-equivᵉ substitution-map-tr-equivᵉ
```

### Transporting along the action on equivalences of a function

```agda
compute-map-tr-equiv-action-equiv-familyᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Bᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ} {Dᵉ : UUᵉ l3ᵉ → UUᵉ l4ᵉ}
  (fᵉ : UUᵉ l1ᵉ → UUᵉ l3ᵉ) (gᵉ : (Xᵉ : UUᵉ l1ᵉ) → Bᵉ Xᵉ → Dᵉ (fᵉ Xᵉ))
  {Xᵉ Yᵉ : UUᵉ l1ᵉ} (eᵉ : Xᵉ ≃ᵉ Yᵉ) (X'ᵉ : Bᵉ Xᵉ) →
  map-tr-equivᵉ Dᵉ (action-equiv-familyᵉ fᵉ eᵉ) (gᵉ Xᵉ X'ᵉ) ＝ᵉ gᵉ Yᵉ (map-tr-equivᵉ Bᵉ eᵉ X'ᵉ)
compute-map-tr-equiv-action-equiv-familyᵉ {Dᵉ = Dᵉ} fᵉ gᵉ {Xᵉ} eᵉ X'ᵉ =
  ( apᵉ
    ( λ pᵉ → trᵉ Dᵉ pᵉ (gᵉ Xᵉ X'ᵉ))
    ( is-retraction-eq-equivᵉ (action-equiv-functionᵉ fᵉ eᵉ))) ∙ᵉ
  ( tr-apᵉ fᵉ gᵉ (eq-equivᵉ eᵉ) X'ᵉ)
```

### Transport along equivalences and the action on equivalences in the universe coincide

```agda
module _
  {l1ᵉ l2ᵉ : Level} (fᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ) {Xᵉ Yᵉ : UUᵉ l1ᵉ} (eᵉ : Xᵉ ≃ᵉ Yᵉ)
  where

  eq-tr-equiv-action-equiv-familyᵉ :
    tr-equivᵉ fᵉ eᵉ ＝ᵉ action-equiv-familyᵉ fᵉ eᵉ
  eq-tr-equiv-action-equiv-familyᵉ =
    ind-equivᵉ
      ( λ Yᵉ dᵉ → tr-equivᵉ fᵉ dᵉ ＝ᵉ action-equiv-familyᵉ fᵉ dᵉ)
      ( compute-tr-equiv-id-equivᵉ fᵉ ∙ᵉ
        invᵉ (compute-action-equiv-family-id-equivᵉ fᵉ))
      ( eᵉ)

  eq-map-tr-equiv-map-action-equiv-familyᵉ :
    map-tr-equivᵉ fᵉ eᵉ ＝ᵉ map-action-equiv-familyᵉ fᵉ eᵉ
  eq-map-tr-equiv-map-action-equiv-familyᵉ =
    apᵉ map-equivᵉ eq-tr-equiv-action-equiv-familyᵉ
```