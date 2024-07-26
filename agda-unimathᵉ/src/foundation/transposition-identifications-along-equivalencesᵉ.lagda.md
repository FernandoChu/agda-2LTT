# Transposing identifications along equivalences

```agda
module foundation.transposition-identifications-along-equivalencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-triangles-of-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
```

</details>

## Idea

Considerᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) `eᵉ : Aᵉ ≃ᵉ B`ᵉ andᵉ twoᵉ
elementsᵉ `xᵉ : A`ᵉ andᵉ `yᵉ : B`.ᵉ Theᵉ
{{#conceptᵉ "transposition"ᵉ Disambiguation="identificationsᵉ alongᵉ equivalences"ᵉ Agda=eq-transpose-equivᵉ}}
isᵉ anᵉ equivalenceᵉ

```text
  (eᵉ xᵉ ＝ᵉ yᵉ) ≃ᵉ (xᵉ ＝ᵉ e⁻¹ᵉ yᵉ)
```

ofᵉ [identityᵉ types](foundation-core.identity-types.md).ᵉ Thereᵉ areᵉ twoᵉ waysᵉ ofᵉ
constructingᵉ thisᵉ equivalence.ᵉ Oneᵉ wayᵉ usesᵉ theᵉ factᵉ thatᵉ `e⁻¹`ᵉ isᵉ aᵉ
[section](foundation-core.sections.mdᵉ) ofᵉ `e`,ᵉ fromᵉ whichᵉ itᵉ followsᵉ thatᵉ

```text
 (eᵉ xᵉ ＝ᵉ yᵉ) ≃ᵉ (eᵉ xᵉ ＝ᵉ eᵉ e⁻¹ᵉ yᵉ) ≃ᵉ (xᵉ ＝ᵉ e⁻¹ᵉ y).ᵉ
```

Inᵉ otherᵉ words,ᵉ theᵉ transposeᵉ ofᵉ anᵉ identificationᵉ `pᵉ : eᵉ xᵉ ＝ᵉ y`ᵉ alongᵉ `e`ᵉ isᵉ
theᵉ uniqueᵉ identificationᵉ `qᵉ : xᵉ ＝ᵉ e⁻¹ᵉ y`ᵉ equippedᵉ with anᵉ identificationᵉ
witnessingᵉ thatᵉ theᵉ triangleᵉ

```text
      apᵉ eᵉ qᵉ
  eᵉ xᵉ ------>ᵉ eᵉ (e⁻¹ᵉ yᵉ)
     \ᵉ       /ᵉ
    pᵉ \ᵉ     /ᵉ is-section-map-inv-equivᵉ eᵉ yᵉ
       \ᵉ   /ᵉ
        ∨ᵉ ∨ᵉ
         yᵉ
```

commutes.ᵉ Theᵉ otherᵉ wayᵉ usesᵉ theᵉ factᵉ thatᵉ `e⁻¹`ᵉ isᵉ aᵉ
[retraction](foundation-core.retractions.mdᵉ) ofᵉ `e`,ᵉ resultingᵉ in theᵉ
equivalenceᵉ

```text
 (eᵉ xᵉ ＝ᵉ yᵉ) ≃ᵉ (e⁻¹ᵉ eᵉ xᵉ ＝ᵉ e⁻¹ᵉ yᵉ) ≃ᵉ (xᵉ ＝ᵉ e⁻¹ᵉ yᵉ) .ᵉ
```

Theseᵉ twoᵉ equivalencesᵉ areᵉ [homotopic](foundation-core.homotopies.md),ᵉ asᵉ isᵉ
shownᵉ below.ᵉ

## Definitions

### Transposing equalities along equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  eq-transpose-equivᵉ :
    (xᵉ : Aᵉ) (yᵉ : Bᵉ) → (map-equivᵉ eᵉ xᵉ ＝ᵉ yᵉ) ≃ᵉ (xᵉ ＝ᵉ map-inv-equivᵉ eᵉ yᵉ)
  eq-transpose-equivᵉ xᵉ yᵉ =
    ( inv-equivᵉ (equiv-apᵉ eᵉ xᵉ (map-inv-equivᵉ eᵉ yᵉ))) ∘eᵉ
    ( equiv-concat'ᵉ
      ( map-equivᵉ eᵉ xᵉ)
      ( invᵉ (is-section-map-inv-equivᵉ eᵉ yᵉ)))

  map-eq-transpose-equivᵉ :
    {xᵉ : Aᵉ} {yᵉ : Bᵉ} → map-equivᵉ eᵉ xᵉ ＝ᵉ yᵉ → xᵉ ＝ᵉ map-inv-equivᵉ eᵉ yᵉ
  map-eq-transpose-equivᵉ {xᵉ} {yᵉ} = map-equivᵉ (eq-transpose-equivᵉ xᵉ yᵉ)

  map-inv-eq-transpose-equivᵉ :
    {xᵉ : Aᵉ} {yᵉ : Bᵉ} → xᵉ ＝ᵉ map-inv-equivᵉ eᵉ yᵉ → map-equivᵉ eᵉ xᵉ ＝ᵉ yᵉ
  map-inv-eq-transpose-equivᵉ {xᵉ} {yᵉ} = map-inv-equivᵉ (eq-transpose-equivᵉ xᵉ yᵉ)

  eq-transpose-equiv'ᵉ :
    (xᵉ : Aᵉ) (yᵉ : Bᵉ) → (map-equivᵉ eᵉ xᵉ ＝ᵉ yᵉ) ≃ᵉ (xᵉ ＝ᵉ map-inv-equivᵉ eᵉ yᵉ)
  eq-transpose-equiv'ᵉ xᵉ yᵉ =
    ( equiv-concatᵉ
      ( invᵉ (is-retraction-map-inv-equivᵉ eᵉ xᵉ))
      ( map-inv-equivᵉ eᵉ yᵉ)) ∘eᵉ
    ( equiv-apᵉ (inv-equivᵉ eᵉ) (map-equivᵉ eᵉ xᵉ) yᵉ)

  map-eq-transpose-equiv'ᵉ :
    {xᵉ : Aᵉ} {yᵉ : Bᵉ} → map-equivᵉ eᵉ xᵉ ＝ᵉ yᵉ → xᵉ ＝ᵉ map-inv-equivᵉ eᵉ yᵉ
  map-eq-transpose-equiv'ᵉ {xᵉ} {yᵉ} = map-equivᵉ (eq-transpose-equiv'ᵉ xᵉ yᵉ)
```

### Transposing identifications of reversed identity types along equivalences

Itᵉ isᵉ sometimesᵉ usefulᵉ to considerᵉ identificationsᵉ `yᵉ ＝ᵉ eᵉ x`ᵉ insteadᵉ ofᵉ
`eᵉ xᵉ ＝ᵉ y`,ᵉ soᵉ weᵉ includeᵉ anᵉ invertedᵉ equivalenceᵉ forᵉ thatᵉ asᵉ well.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  eq-transpose-equiv-invᵉ :
    (xᵉ : Aᵉ) (yᵉ : Bᵉ) → (yᵉ ＝ᵉ map-equivᵉ eᵉ xᵉ) ≃ᵉ (map-inv-equivᵉ eᵉ yᵉ ＝ᵉ xᵉ)
  eq-transpose-equiv-invᵉ xᵉ yᵉ =
    ( inv-equivᵉ (equiv-apᵉ eᵉ _ _)) ∘eᵉ
    ( equiv-concatᵉ (is-section-map-inv-equivᵉ eᵉ yᵉ) _)

  map-eq-transpose-equiv-invᵉ :
    {aᵉ : Aᵉ} {bᵉ : Bᵉ} → bᵉ ＝ᵉ map-equivᵉ eᵉ aᵉ → map-inv-equivᵉ eᵉ bᵉ ＝ᵉ aᵉ
  map-eq-transpose-equiv-invᵉ {aᵉ} {bᵉ} = map-equivᵉ (eq-transpose-equiv-invᵉ aᵉ bᵉ)

  map-inv-eq-transpose-equiv-invᵉ :
    {aᵉ : Aᵉ} {bᵉ : Bᵉ} → map-inv-equivᵉ eᵉ bᵉ ＝ᵉ aᵉ → bᵉ ＝ᵉ map-equivᵉ eᵉ aᵉ
  map-inv-eq-transpose-equiv-invᵉ {aᵉ} {bᵉ} =
    map-inv-equivᵉ (eq-transpose-equiv-invᵉ aᵉ bᵉ)
```

## Properties

### Computing transposition of reflexivity along equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  compute-refl-eq-transpose-equivᵉ :
    {xᵉ : Aᵉ} →
    map-eq-transpose-equivᵉ eᵉ reflᵉ ＝ᵉ invᵉ (is-retraction-map-inv-equivᵉ eᵉ xᵉ)
  compute-refl-eq-transpose-equivᵉ =
    map-eq-transpose-equiv-invᵉ
      ( equiv-apᵉ eᵉ _ (map-inv-equivᵉ eᵉ _))
      ( apᵉ invᵉ (coherence-map-inv-equivᵉ eᵉ _) ∙ᵉ
        invᵉ (ap-invᵉ (map-equivᵉ eᵉ) _))

  compute-refl-eq-transpose-equiv-invᵉ :
    {xᵉ : Aᵉ} →
    map-eq-transpose-equiv-invᵉ eᵉ reflᵉ ＝ᵉ is-retraction-map-inv-equivᵉ eᵉ xᵉ
  compute-refl-eq-transpose-equiv-invᵉ {xᵉ} =
    map-eq-transpose-equiv-invᵉ
      ( equiv-apᵉ eᵉ _ _)
      ( ( right-unitᵉ) ∙ᵉ
        ( coherence-map-inv-equivᵉ eᵉ _))
```

### The two definitions of transposing identifications along equivalences are homotopic

Weᵉ beginᵉ byᵉ showingᵉ thatᵉ theᵉ twoᵉ equivalencesᵉ statedᵉ aboveᵉ areᵉ homotopic.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  compute-map-eq-transpose-equivᵉ :
    {xᵉ : Aᵉ} {yᵉ : Bᵉ} →
    map-eq-transpose-equivᵉ eᵉ {xᵉ} {yᵉ} ~ᵉ map-eq-transpose-equiv'ᵉ eᵉ
  compute-map-eq-transpose-equivᵉ {xᵉ} reflᵉ =
    ( map-eq-transpose-equiv-invᵉ
      ( equiv-apᵉ eᵉ xᵉ _)
      ( ( apᵉ invᵉ (coherence-map-inv-equivᵉ eᵉ xᵉ)) ∙ᵉ
        ( invᵉ (ap-invᵉ (map-equivᵉ eᵉ) (is-retraction-map-inv-equivᵉ eᵉ xᵉ))))) ∙ᵉ
    ( invᵉ right-unitᵉ)
```

### The defining commuting triangles of transposed identifications

Transposedᵉ identificationsᵉ fitᵉ in
[commutingᵉ triangles](foundation.commuting-triangles-of-identifications.mdᵉ) with
theᵉ originalᵉ identifications.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  triangle-eq-transpose-equivᵉ :
    {xᵉ : Aᵉ} {yᵉ : Bᵉ} (pᵉ : map-equivᵉ eᵉ xᵉ ＝ᵉ yᵉ) →
    coherence-triangle-identifications'ᵉ
      ( pᵉ)
      ( is-section-map-inv-equivᵉ eᵉ yᵉ)
      ( apᵉ (map-equivᵉ eᵉ) (map-eq-transpose-equivᵉ eᵉ pᵉ))
  triangle-eq-transpose-equivᵉ {xᵉ} {yᵉ} pᵉ =
    ( right-whisker-concatᵉ
      ( is-section-map-inv-equivᵉ
        ( equiv-apᵉ eᵉ xᵉ (map-inv-equivᵉ eᵉ yᵉ))
        ( pᵉ ∙ᵉ invᵉ (is-section-map-inv-equivᵉ eᵉ yᵉ)))
      ( is-section-map-inv-equivᵉ eᵉ yᵉ)) ∙ᵉ
    ( is-section-inv-concat'ᵉ (is-section-map-inv-equivᵉ eᵉ yᵉ) pᵉ)

  triangle-eq-transpose-equiv-invᵉ :
    {xᵉ : Aᵉ} {yᵉ : Bᵉ} (pᵉ : yᵉ ＝ᵉ map-equivᵉ eᵉ xᵉ) →
    coherence-triangle-identifications'ᵉ
      ( apᵉ (map-equivᵉ eᵉ) (map-eq-transpose-equiv-invᵉ eᵉ pᵉ))
      ( pᵉ)
      ( is-section-map-inv-equivᵉ eᵉ yᵉ)
  triangle-eq-transpose-equiv-invᵉ {xᵉ} {yᵉ} pᵉ =
    invᵉ
      ( is-section-map-inv-equivᵉ
        ( equiv-apᵉ eᵉ _ _)
        ( is-section-map-inv-equivᵉ eᵉ yᵉ ∙ᵉ pᵉ))

  triangle-eq-transpose-equiv'ᵉ :
    {xᵉ : Aᵉ} {yᵉ : Bᵉ} (pᵉ : map-equivᵉ eᵉ xᵉ ＝ᵉ yᵉ) →
    coherence-triangle-identifications'ᵉ
      ( apᵉ (map-inv-equivᵉ eᵉ) pᵉ)
      ( map-eq-transpose-equivᵉ eᵉ pᵉ)
      ( is-retraction-map-inv-equivᵉ eᵉ xᵉ)
  triangle-eq-transpose-equiv'ᵉ {xᵉ} reflᵉ =
    ( left-whisker-concatᵉ
      ( is-retraction-map-inv-equivᵉ eᵉ xᵉ)
      ( compute-map-eq-transpose-equivᵉ eᵉ reflᵉ)) ∙ᵉ
    ( is-section-inv-concatᵉ (is-retraction-map-inv-equivᵉ eᵉ xᵉ) reflᵉ)

  triangle-eq-transpose-equiv-inv'ᵉ :
    {xᵉ : Aᵉ} {yᵉ : Bᵉ} (pᵉ : yᵉ ＝ᵉ map-equivᵉ eᵉ xᵉ) →
    coherence-triangle-identificationsᵉ
      ( map-eq-transpose-equiv-invᵉ eᵉ pᵉ)
      ( is-retraction-map-inv-equivᵉ eᵉ xᵉ)
      ( apᵉ (map-inv-equivᵉ eᵉ) pᵉ)
  triangle-eq-transpose-equiv-inv'ᵉ {xᵉ} reflᵉ =
    compute-refl-eq-transpose-equiv-invᵉ eᵉ

  right-inverse-eq-transpose-equivᵉ :
    {xᵉ : Aᵉ} {yᵉ : Bᵉ} (pᵉ : yᵉ ＝ᵉ map-equivᵉ eᵉ xᵉ) →
    ( ( map-eq-transpose-equivᵉ eᵉ (invᵉ pᵉ)) ∙ᵉ
      ( apᵉ (map-inv-equivᵉ eᵉ) pᵉ ∙ᵉ is-retraction-map-inv-equivᵉ eᵉ xᵉ)) ＝ᵉ
    ( reflᵉ)
  right-inverse-eq-transpose-equivᵉ {xᵉ} reflᵉ =
    ( right-whisker-concatᵉ (compute-refl-eq-transpose-equivᵉ eᵉ) _) ∙ᵉ
    ( left-invᵉ (is-retraction-map-inv-equivᵉ eᵉ _))
```

### Transposing concatenated identifications along equivalences

Transposingᵉ concatenatedᵉ identificationsᵉ intoᵉ aᵉ triangleᵉ with aᵉ transposeᵉ ofᵉ theᵉ
leftᵉ factor.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  triangle-eq-transpose-equiv-concatᵉ :
    {xᵉ : Aᵉ} {yᵉ zᵉ : Bᵉ} (pᵉ : map-equivᵉ eᵉ xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    ( map-eq-transpose-equivᵉ eᵉ (pᵉ ∙ᵉ qᵉ)) ＝ᵉ
    ( map-eq-transpose-equivᵉ eᵉ pᵉ ∙ᵉ apᵉ (map-inv-equivᵉ eᵉ) qᵉ)
  triangle-eq-transpose-equiv-concatᵉ reflᵉ reflᵉ = invᵉ right-unitᵉ
```