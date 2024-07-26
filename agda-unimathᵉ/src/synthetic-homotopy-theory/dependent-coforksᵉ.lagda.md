# Dependent coforks

```agda
module synthetic-homotopy-theory.dependent-coforksᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.constant-type-familiesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.double-arrowsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import synthetic-homotopy-theory.coforksᵉ
open import synthetic-homotopy-theory.dependent-cocones-under-spansᵉ
```

</details>

## Idea

Givenᵉ aᵉ [doubleᵉ arrow](foundation.double-arrows.mdᵉ) `f,ᵉ gᵉ : Aᵉ → B`,ᵉ aᵉ
[cofork](synthetic-homotopy-theory.coforks.mdᵉ) `eᵉ : Bᵉ → X`ᵉ with vertexᵉ `X`,ᵉ andᵉ
aᵉ typeᵉ familyᵉ `Pᵉ : Xᵉ → 𝒰`ᵉ overᵉ `X`,ᵉ weᵉ mayᵉ constructᵉ _dependentᵉ_ coforksᵉ onᵉ `P`ᵉ
overᵉ `e`.ᵉ

Aᵉ
{{#conceptᵉ "dependentᵉ cofork"ᵉ Disambiguation="ofᵉ types"ᵉ Agda=dependent-coforkᵉ}}
onᵉ `P`ᵉ overᵉ `e`ᵉ consistsᵉ ofᵉ aᵉ dependentᵉ mapᵉ

```text
kᵉ : (bᵉ : Bᵉ) → Pᵉ (eᵉ bᵉ)
```

andᵉ aᵉ familyᵉ ofᵉ
[dependentᵉ identifications](foundation.dependent-identifications.mdᵉ) indexedᵉ byᵉ
`A`ᵉ

```text
(aᵉ : Aᵉ) → dependent-identificationᵉ Pᵉ (Hᵉ aᵉ) (kᵉ (fᵉ aᵉ)) (kᵉ (gᵉ a)).ᵉ
```

Dependentᵉ coforksᵉ areᵉ anᵉ analogueᵉ ofᵉ
[dependentᵉ coconesᵉ underᵉ spans](synthetic-homotopy-theory.dependent-cocones-under-spans.mdᵉ)
forᵉ doubleᵉ arrows.ᵉ

## Definitions

### Dependent coforks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  (eᵉ : coforkᵉ aᵉ Xᵉ) (Pᵉ : Xᵉ → UUᵉ l4ᵉ)
  where

  dependent-coforkᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  dependent-coforkᵉ =
    Σᵉ ( (bᵉ : codomain-double-arrowᵉ aᵉ) → Pᵉ (map-coforkᵉ aᵉ eᵉ bᵉ))
      ( λ kᵉ →
        (xᵉ : domain-double-arrowᵉ aᵉ) →
        dependent-identificationᵉ Pᵉ
          ( coh-coforkᵉ aᵉ eᵉ xᵉ)
          ( kᵉ (left-map-double-arrowᵉ aᵉ xᵉ))
          ( kᵉ (right-map-double-arrowᵉ aᵉ xᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  {eᵉ : coforkᵉ aᵉ Xᵉ} (Pᵉ : Xᵉ → UUᵉ l4ᵉ)
  (kᵉ : dependent-coforkᵉ aᵉ eᵉ Pᵉ)
  where

  map-dependent-coforkᵉ : (bᵉ : codomain-double-arrowᵉ aᵉ) → Pᵉ (map-coforkᵉ aᵉ eᵉ bᵉ)
  map-dependent-coforkᵉ = pr1ᵉ kᵉ

  coherence-dependent-coforkᵉ :
    (xᵉ : domain-double-arrowᵉ aᵉ) →
    dependent-identificationᵉ Pᵉ
      ( coh-coforkᵉ aᵉ eᵉ xᵉ)
      ( map-dependent-coforkᵉ (left-map-double-arrowᵉ aᵉ xᵉ))
      ( map-dependent-coforkᵉ (right-map-double-arrowᵉ aᵉ xᵉ))
  coherence-dependent-coforkᵉ = pr2ᵉ kᵉ
```

### Homotopies of dependent coforks

Aᵉ homotopyᵉ betweenᵉ dependentᵉ coforksᵉ isᵉ aᵉ homotopyᵉ betweenᵉ theᵉ underlyingᵉ maps,ᵉ
togetherᵉ with aᵉ coherenceᵉ condition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  {eᵉ : coforkᵉ aᵉ Xᵉ} (Pᵉ : Xᵉ → UUᵉ l4ᵉ)
  where

  coherence-htpy-dependent-coforkᵉ :
    (kᵉ k'ᵉ : dependent-coforkᵉ aᵉ eᵉ Pᵉ) →
    (Kᵉ : map-dependent-coforkᵉ aᵉ Pᵉ kᵉ ~ᵉ map-dependent-coforkᵉ aᵉ Pᵉ k'ᵉ) →
    UUᵉ (l1ᵉ ⊔ l4ᵉ)
  coherence-htpy-dependent-coforkᵉ kᵉ k'ᵉ Kᵉ =
    ( (coherence-dependent-coforkᵉ aᵉ Pᵉ kᵉ) ∙hᵉ (Kᵉ ·rᵉ right-map-double-arrowᵉ aᵉ)) ~ᵉ
    ( ( (λ {xᵉ} → trᵉ Pᵉ (coh-coforkᵉ aᵉ eᵉ xᵉ)) ·lᵉ (Kᵉ ·rᵉ left-map-double-arrowᵉ aᵉ)) ∙hᵉ
      ( coherence-dependent-coforkᵉ aᵉ Pᵉ k'ᵉ))

  htpy-dependent-coforkᵉ :
    (kᵉ k'ᵉ : dependent-coforkᵉ aᵉ eᵉ Pᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  htpy-dependent-coforkᵉ kᵉ k'ᵉ =
    Σᵉ ( map-dependent-coforkᵉ aᵉ Pᵉ kᵉ ~ᵉ map-dependent-coforkᵉ aᵉ Pᵉ k'ᵉ)
      ( coherence-htpy-dependent-coforkᵉ kᵉ k'ᵉ)
```

### Obtaining dependent coforks as postcomposition of coforks with dependent maps

Oneᵉ wayᵉ to obtainsᵉ dependentᵉ coforksᵉ isᵉ to postcomposeᵉ theᵉ underlyingᵉ coforkᵉ byᵉ
aᵉ dependentᵉ map,ᵉ accordingᵉ to theᵉ diagramᵉ

```text
     gᵉ
   ----->ᵉ     eᵉ              hᵉ
 Aᵉ ----->ᵉ Bᵉ ----->ᵉ (xᵉ : Xᵉ) ----->ᵉ (Pᵉ xᵉ)
     fᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  (eᵉ : coforkᵉ aᵉ Xᵉ)
  where

  dependent-cofork-mapᵉ :
    {lᵉ : Level} {Pᵉ : Xᵉ → UUᵉ lᵉ} → ((xᵉ : Xᵉ) → Pᵉ xᵉ) → dependent-coforkᵉ aᵉ eᵉ Pᵉ
  pr1ᵉ (dependent-cofork-mapᵉ hᵉ) = hᵉ ∘ᵉ map-coforkᵉ aᵉ eᵉ
  pr2ᵉ (dependent-cofork-mapᵉ hᵉ) = apdᵉ hᵉ ∘ᵉ coh-coforkᵉ aᵉ eᵉ
```

## Properties

### Characterization of identity types of coforks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  {eᵉ : coforkᵉ aᵉ Xᵉ} (Pᵉ : Xᵉ → UUᵉ l4ᵉ)
  where

  refl-htpy-dependent-coforkᵉ :
    (kᵉ : dependent-coforkᵉ aᵉ eᵉ Pᵉ) →
    htpy-dependent-coforkᵉ aᵉ Pᵉ kᵉ kᵉ
  pr1ᵉ (refl-htpy-dependent-coforkᵉ kᵉ) = refl-htpyᵉ
  pr2ᵉ (refl-htpy-dependent-coforkᵉ kᵉ) = right-unit-htpyᵉ

  htpy-dependent-cofork-eqᵉ :
    (kᵉ k'ᵉ : dependent-coforkᵉ aᵉ eᵉ Pᵉ) →
    (kᵉ ＝ᵉ k'ᵉ) → htpy-dependent-coforkᵉ aᵉ Pᵉ kᵉ k'ᵉ
  htpy-dependent-cofork-eqᵉ kᵉ .kᵉ reflᵉ = refl-htpy-dependent-coforkᵉ kᵉ

  abstract
    is-torsorial-htpy-dependent-coforkᵉ :
      (kᵉ : dependent-coforkᵉ aᵉ eᵉ Pᵉ) →
      is-torsorialᵉ (htpy-dependent-coforkᵉ aᵉ Pᵉ kᵉ)
    is-torsorial-htpy-dependent-coforkᵉ kᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpyᵉ (map-dependent-coforkᵉ aᵉ Pᵉ kᵉ))
        ( map-dependent-coforkᵉ aᵉ Pᵉ kᵉ ,ᵉ refl-htpyᵉ)
        ( is-torsorial-htpyᵉ
          ( coherence-dependent-coforkᵉ aᵉ Pᵉ kᵉ ∙hᵉ refl-htpyᵉ))

    is-equiv-htpy-dependent-cofork-eqᵉ :
      (kᵉ k'ᵉ : dependent-coforkᵉ aᵉ eᵉ Pᵉ) →
      is-equivᵉ (htpy-dependent-cofork-eqᵉ kᵉ k'ᵉ)
    is-equiv-htpy-dependent-cofork-eqᵉ kᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-htpy-dependent-coforkᵉ kᵉ)
        ( htpy-dependent-cofork-eqᵉ kᵉ)

  eq-htpy-dependent-coforkᵉ :
    (kᵉ k'ᵉ : dependent-coforkᵉ aᵉ eᵉ Pᵉ) →
    htpy-dependent-coforkᵉ aᵉ Pᵉ kᵉ k'ᵉ → kᵉ ＝ᵉ k'ᵉ
  eq-htpy-dependent-coforkᵉ kᵉ k'ᵉ =
    map-inv-is-equivᵉ (is-equiv-htpy-dependent-cofork-eqᵉ kᵉ k'ᵉ)
```

### Dependent coforks on constant type families are equivalent to nondependent coforks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  (eᵉ : coforkᵉ aᵉ Xᵉ) (Yᵉ : UUᵉ l4ᵉ)
  where

  compute-dependent-cofork-constant-familyᵉ :
    dependent-coforkᵉ aᵉ eᵉ (λ _ → Yᵉ) ≃ᵉ coforkᵉ aᵉ Yᵉ
  compute-dependent-cofork-constant-familyᵉ =
    equiv-totᵉ
      ( λ hᵉ →
        equiv-Π-equiv-familyᵉ
          ( λ xᵉ →
            equiv-concatᵉ
              ( invᵉ
                ( tr-constant-type-familyᵉ
                  ( coh-coforkᵉ aᵉ eᵉ xᵉ)
                  ( hᵉ (left-map-double-arrowᵉ aᵉ xᵉ))))
              ( hᵉ (right-map-double-arrowᵉ aᵉ xᵉ))))

  map-compute-dependent-cofork-constant-familyᵉ :
    dependent-coforkᵉ aᵉ eᵉ (λ _ → Yᵉ) → coforkᵉ aᵉ Yᵉ
  map-compute-dependent-cofork-constant-familyᵉ =
    map-equivᵉ compute-dependent-cofork-constant-familyᵉ

  triangle-compute-dependent-cofork-constant-familyᵉ :
    coherence-triangle-mapsᵉ
      ( cofork-mapᵉ aᵉ eᵉ)
      ( map-compute-dependent-cofork-constant-familyᵉ)
      ( dependent-cofork-mapᵉ aᵉ eᵉ)
  triangle-compute-dependent-cofork-constant-familyᵉ hᵉ =
    eq-htpy-coforkᵉ aᵉ
      ( cofork-mapᵉ aᵉ eᵉ hᵉ)
      ( map-compute-dependent-cofork-constant-familyᵉ
        ( dependent-cofork-mapᵉ aᵉ eᵉ hᵉ))
      ( ( refl-htpyᵉ) ,ᵉ
        ( right-unit-htpyᵉ ∙hᵉ
          ( λ xᵉ →
            left-transpose-eq-concatᵉ _ _ _
              ( invᵉ (apd-constant-type-familyᵉ hᵉ (coh-coforkᵉ aᵉ eᵉ xᵉ))))))
```

### Dependent coforks are special cases of dependent cocones under spans

Theᵉ typeᵉ ofᵉ dependentᵉ coforksᵉ onᵉ `P`ᵉ overᵉ `e`ᵉ isᵉ equivalentᵉ to theᵉ typeᵉ ofᵉ
[dependentᵉ cocones](synthetic-homotopy-theory.dependent-cocones-under-spans.mdᵉ)
onᵉ `P`ᵉ overᵉ aᵉ coconeᵉ correspondingᵉ to `e`ᵉ viaᵉ `cocone-codiagonal-cofork`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  (eᵉ : coforkᵉ aᵉ Xᵉ)
  where

  module _
    {l4ᵉ : Level} (Pᵉ : Xᵉ → UUᵉ l4ᵉ)
    where

    dependent-cofork-dependent-cocone-codiagonalᵉ :
      dependent-coconeᵉ
        ( vertical-map-span-cocone-coforkᵉ aᵉ)
        ( horizontal-map-span-cocone-coforkᵉ aᵉ)
        ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
        ( Pᵉ) →
      dependent-coforkᵉ aᵉ eᵉ Pᵉ
    pr1ᵉ (dependent-cofork-dependent-cocone-codiagonalᵉ kᵉ) =
      vertical-map-dependent-coconeᵉ
        ( vertical-map-span-cocone-coforkᵉ aᵉ)
        ( horizontal-map-span-cocone-coforkᵉ aᵉ)
        ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
        ( Pᵉ)
        ( kᵉ)
    pr2ᵉ (dependent-cofork-dependent-cocone-codiagonalᵉ kᵉ) xᵉ =
      invᵉ
        ( apᵉ
          ( trᵉ Pᵉ (coh-coforkᵉ aᵉ eᵉ xᵉ))
          ( coherence-square-dependent-coconeᵉ
            ( vertical-map-span-cocone-coforkᵉ aᵉ)
            ( horizontal-map-span-cocone-coforkᵉ aᵉ)
            ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
            ( Pᵉ)
            ( kᵉ)
            ( inlᵉ xᵉ))) ∙ᵉ
      coherence-square-dependent-coconeᵉ
        ( vertical-map-span-cocone-coforkᵉ aᵉ)
        ( horizontal-map-span-cocone-coforkᵉ aᵉ)
        ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
        ( Pᵉ)
        ( kᵉ)
        ( inrᵉ xᵉ)

    dependent-cocone-codiagonal-dependent-coforkᵉ :
      dependent-coforkᵉ aᵉ eᵉ Pᵉ →
      dependent-coconeᵉ
        ( vertical-map-span-cocone-coforkᵉ aᵉ)
        ( horizontal-map-span-cocone-coforkᵉ aᵉ)
        ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
        ( Pᵉ)
    pr1ᵉ (dependent-cocone-codiagonal-dependent-coforkᵉ kᵉ) =
      map-dependent-coforkᵉ aᵉ Pᵉ kᵉ ∘ᵉ left-map-double-arrowᵉ aᵉ
    pr1ᵉ (pr2ᵉ (dependent-cocone-codiagonal-dependent-coforkᵉ kᵉ)) =
      map-dependent-coforkᵉ aᵉ Pᵉ kᵉ
    pr2ᵉ (pr2ᵉ (dependent-cocone-codiagonal-dependent-coforkᵉ kᵉ)) (inlᵉ aᵉ) =
      reflᵉ
    pr2ᵉ (pr2ᵉ (dependent-cocone-codiagonal-dependent-coforkᵉ kᵉ)) (inrᵉ xᵉ) =
      coherence-dependent-coforkᵉ aᵉ Pᵉ kᵉ xᵉ

    abstract
      is-section-dependent-cocone-codiagonal-dependent-coforkᵉ :
        ( ( dependent-cofork-dependent-cocone-codiagonalᵉ) ∘ᵉ
          ( dependent-cocone-codiagonal-dependent-coforkᵉ)) ~ᵉ
        ( idᵉ)
      is-section-dependent-cocone-codiagonal-dependent-coforkᵉ kᵉ =
        eq-htpy-dependent-coforkᵉ aᵉ Pᵉ
          ( dependent-cofork-dependent-cocone-codiagonalᵉ
            ( dependent-cocone-codiagonal-dependent-coforkᵉ kᵉ))
          ( kᵉ)
          ( refl-htpyᵉ ,ᵉ right-unit-htpyᵉ)

      is-retraction-dependent-cocone-codiagonal-dependent-coforkᵉ :
        ( ( dependent-cocone-codiagonal-dependent-coforkᵉ) ∘ᵉ
          ( dependent-cofork-dependent-cocone-codiagonalᵉ)) ~ᵉ
        ( idᵉ)
      is-retraction-dependent-cocone-codiagonal-dependent-coforkᵉ dᵉ =
        eq-htpy-dependent-coconeᵉ
          ( vertical-map-span-cocone-coforkᵉ aᵉ)
          ( horizontal-map-span-cocone-coforkᵉ aᵉ)
          ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
          ( Pᵉ)
          ( dependent-cocone-codiagonal-dependent-coforkᵉ
            ( dependent-cofork-dependent-cocone-codiagonalᵉ dᵉ))
          ( dᵉ)
          ( inv-htpyᵉ
            ( ( coherence-square-dependent-coconeᵉ
                ( vertical-map-span-cocone-coforkᵉ aᵉ)
                ( horizontal-map-span-cocone-coforkᵉ aᵉ)
                ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
                ( Pᵉ)
                ( dᵉ)) ∘ᵉ
              ( inlᵉ)) ,ᵉ
            ( refl-htpyᵉ) ,ᵉ
            ( right-unit-htpyᵉ ∙hᵉ
              ( λ where
                (inlᵉ xᵉ) →
                  invᵉ
                    ( ( right-whisker-concatᵉ
                        ( ap-idᵉ
                          ( invᵉ
                            ( coherence-square-dependent-coconeᵉ
                              ( vertical-map-span-cocone-coforkᵉ aᵉ)
                              ( horizontal-map-span-cocone-coforkᵉ aᵉ)
                              ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
                              ( Pᵉ)
                              ( dᵉ)
                              ( inlᵉ xᵉ))))
                        ( coherence-square-dependent-coconeᵉ
                          ( vertical-map-span-cocone-coforkᵉ aᵉ)
                          ( horizontal-map-span-cocone-coforkᵉ aᵉ)
                          ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
                          ( Pᵉ)
                          ( dᵉ)
                          ( inlᵉ xᵉ))) ∙ᵉ
                      ( left-invᵉ
                        ( coherence-square-dependent-coconeᵉ
                          ( vertical-map-span-cocone-coforkᵉ aᵉ)
                          ( horizontal-map-span-cocone-coforkᵉ aᵉ)
                          ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
                          ( Pᵉ)
                          ( dᵉ)
                          ( inlᵉ xᵉ))))
                (inrᵉ xᵉ) →
                  right-whisker-concatᵉ
                    ( invᵉ
                      ( ap-invᵉ
                        ( trᵉ Pᵉ (coh-coforkᵉ aᵉ eᵉ xᵉ))
                        ( coherence-square-dependent-coconeᵉ
                          ( vertical-map-span-cocone-coforkᵉ aᵉ)
                          ( horizontal-map-span-cocone-coforkᵉ aᵉ)
                          ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
                          ( Pᵉ)
                          ( dᵉ)
                          ( inlᵉ xᵉ))))
                    ( coherence-square-dependent-coconeᵉ
                      ( vertical-map-span-cocone-coforkᵉ aᵉ)
                      ( horizontal-map-span-cocone-coforkᵉ aᵉ)
                      ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
                      ( Pᵉ)
                      ( dᵉ)
                      ( inrᵉ xᵉ)))))

    is-equiv-dependent-cofork-dependent-cocone-codiagonalᵉ :
      is-equivᵉ dependent-cofork-dependent-cocone-codiagonalᵉ
    is-equiv-dependent-cofork-dependent-cocone-codiagonalᵉ =
      is-equiv-is-invertibleᵉ
        ( dependent-cocone-codiagonal-dependent-coforkᵉ)
        ( is-section-dependent-cocone-codiagonal-dependent-coforkᵉ)
        ( is-retraction-dependent-cocone-codiagonal-dependent-coforkᵉ)

    equiv-dependent-cofork-dependent-cocone-codiagonalᵉ :
      dependent-coconeᵉ
        ( vertical-map-span-cocone-coforkᵉ aᵉ)
        ( horizontal-map-span-cocone-coforkᵉ aᵉ)
        ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
        ( Pᵉ) ≃ᵉ
      dependent-coforkᵉ aᵉ eᵉ Pᵉ
    pr1ᵉ equiv-dependent-cofork-dependent-cocone-codiagonalᵉ =
      dependent-cofork-dependent-cocone-codiagonalᵉ
    pr2ᵉ equiv-dependent-cofork-dependent-cocone-codiagonalᵉ =
      is-equiv-dependent-cofork-dependent-cocone-codiagonalᵉ

  triangle-dependent-cofork-dependent-cocone-codiagonalᵉ :
    {l4ᵉ : Level} (Pᵉ : Xᵉ → UUᵉ l4ᵉ) →
    coherence-triangle-mapsᵉ
      ( dependent-cofork-mapᵉ aᵉ eᵉ)
      ( dependent-cofork-dependent-cocone-codiagonalᵉ Pᵉ)
      ( dependent-cocone-mapᵉ
        ( vertical-map-span-cocone-coforkᵉ aᵉ)
        ( horizontal-map-span-cocone-coforkᵉ aᵉ)
        ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
        ( Pᵉ))
  triangle-dependent-cofork-dependent-cocone-codiagonalᵉ Pᵉ hᵉ =
    eq-htpy-dependent-coforkᵉ aᵉ Pᵉ
      ( dependent-cofork-mapᵉ aᵉ eᵉ hᵉ)
      ( dependent-cofork-dependent-cocone-codiagonalᵉ Pᵉ
        ( dependent-cocone-mapᵉ
          ( vertical-map-span-cocone-coforkᵉ aᵉ)
          ( horizontal-map-span-cocone-coforkᵉ aᵉ)
          ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
          ( Pᵉ)
          ( hᵉ)))
      ( refl-htpyᵉ ,ᵉ
        right-unit-htpyᵉ)
```