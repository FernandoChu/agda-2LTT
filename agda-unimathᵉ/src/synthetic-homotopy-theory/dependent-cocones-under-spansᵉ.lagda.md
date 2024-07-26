# Dependent cocones under spans

```agda
module synthetic-homotopy-theory.dependent-cocones-under-spansᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.constant-type-familiesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-homotopiesᵉ
open import foundation.dependent-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.span-diagramsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-higher-identificationsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.injective-mapsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
```

</details>

## Idea

Considerᵉ aᵉ spanᵉ `𝒮ᵉ :=ᵉ (Aᵉ <--ᵉ Sᵉ -->ᵉ B)`ᵉ andᵉ aᵉ
[coconeᵉ structure](synthetic-homotopy-theory.cocones-under-spans.mdᵉ) `c`ᵉ ofᵉ `𝒮`ᵉ
intoᵉ aᵉ typeᵉ `X`.ᵉ Furthermore,ᵉ considerᵉ aᵉ typeᵉ familyᵉ `P`ᵉ overᵉ `X`.ᵉ Inᵉ thisᵉ caseᵉ
weᵉ mayᵉ considerᵉ _dependentᵉ_ coconeᵉ structuresᵉ onᵉ `P`ᵉ overᵉ `c`.ᵉ

Aᵉ **dependentᵉ cocone**ᵉ `d`ᵉ overᵉ `(iᵉ ,ᵉ jᵉ ,ᵉ H)`ᵉ onᵉ `P`ᵉ consistsᵉ ofᵉ twoᵉ dependentᵉ
functionsᵉ

```text
  i'ᵉ : (aᵉ : Aᵉ) → Pᵉ (iᵉ aᵉ)
  j'ᵉ : (bᵉ : Bᵉ) → Pᵉ (jᵉ bᵉ)
```

andᵉ aᵉ familyᵉ ofᵉ
[dependentᵉ identifications](foundation.dependent-identifications.mdᵉ)

```text
  (sᵉ : Sᵉ) → dependent-identificationᵉ Pᵉ (Hᵉ sᵉ) (i'ᵉ (fᵉ sᵉ)) (j'ᵉ (gᵉ s)).ᵉ
```

## Definitions

### Dependent cocones

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) (Pᵉ : Xᵉ → UUᵉ l5ᵉ)
  where

  dependent-coconeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l5ᵉ)
  dependent-coconeᵉ =
    Σᵉ ( (aᵉ : Aᵉ) → Pᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ aᵉ))
      ( λ hAᵉ →
        Σᵉ ( (bᵉ : Bᵉ) → Pᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ bᵉ))
          ( λ hBᵉ →
            (sᵉ : Sᵉ) →
            dependent-identificationᵉ Pᵉ
              ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ)
              ( hAᵉ (fᵉ sᵉ))
              ( hBᵉ (gᵉ sᵉ))))

  module _
    (dᵉ : dependent-coconeᵉ)
    where

    horizontal-map-dependent-coconeᵉ :
      (aᵉ : Aᵉ) → Pᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ aᵉ)
    horizontal-map-dependent-coconeᵉ = pr1ᵉ dᵉ

    vertical-map-dependent-coconeᵉ :
      (bᵉ : Bᵉ) → Pᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ bᵉ)
    vertical-map-dependent-coconeᵉ = pr1ᵉ (pr2ᵉ dᵉ)

    coherence-square-dependent-coconeᵉ :
      (sᵉ : Sᵉ) →
      dependent-identificationᵉ Pᵉ
        ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ)
        ( horizontal-map-dependent-coconeᵉ (fᵉ sᵉ))
        ( vertical-map-dependent-coconeᵉ (gᵉ sᵉ))
    coherence-square-dependent-coconeᵉ = pr2ᵉ (pr2ᵉ dᵉ)

dependent-cocone-span-diagramᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  ( cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ) (Pᵉ : Xᵉ → UUᵉ l5ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l5ᵉ)
dependent-cocone-span-diagramᵉ {𝒮ᵉ = 𝒮ᵉ} =
  dependent-coconeᵉ (left-map-span-diagramᵉ 𝒮ᵉ) (right-map-span-diagramᵉ 𝒮ᵉ)
```

### Cocones equipped with dependent cocones

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (Pᵉ : Xᵉ → UUᵉ l5ᵉ)
  where

  cocone-with-dependent-coconeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
  cocone-with-dependent-coconeᵉ =
    Σᵉ (coconeᵉ fᵉ gᵉ Xᵉ) (λ cᵉ → dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (Pᵉ : Xᵉ → UUᵉ l5ᵉ)
  (cᵉ : cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ)
  where

  cocone-cocone-with-dependent-coconeᵉ : coconeᵉ fᵉ gᵉ Xᵉ
  cocone-cocone-with-dependent-coconeᵉ = pr1ᵉ cᵉ

  horizontal-map-cocone-with-dependent-coconeᵉ : Aᵉ → Xᵉ
  horizontal-map-cocone-with-dependent-coconeᵉ =
    horizontal-map-coconeᵉ fᵉ gᵉ cocone-cocone-with-dependent-coconeᵉ

  vertical-map-cocone-with-dependent-coconeᵉ : Bᵉ → Xᵉ
  vertical-map-cocone-with-dependent-coconeᵉ =
    vertical-map-coconeᵉ fᵉ gᵉ cocone-cocone-with-dependent-coconeᵉ

  coherence-square-cocone-with-dependent-coconeᵉ :
    coherence-square-mapsᵉ gᵉ fᵉ
      ( vertical-map-cocone-with-dependent-coconeᵉ)
      ( horizontal-map-cocone-with-dependent-coconeᵉ)
  coherence-square-cocone-with-dependent-coconeᵉ =
    coherence-square-coconeᵉ fᵉ gᵉ cocone-cocone-with-dependent-coconeᵉ

  dependent-cocone-cocone-with-dependent-coconeᵉ :
    dependent-coconeᵉ fᵉ gᵉ cocone-cocone-with-dependent-coconeᵉ Pᵉ
  dependent-cocone-cocone-with-dependent-coconeᵉ = pr2ᵉ cᵉ

  horizontal-map-dependent-cocone-with-dependent-coconeᵉ :
    (aᵉ : Aᵉ) → Pᵉ (horizontal-map-cocone-with-dependent-coconeᵉ aᵉ)
  horizontal-map-dependent-cocone-with-dependent-coconeᵉ =
    horizontal-map-dependent-coconeᵉ fᵉ gᵉ
      ( cocone-cocone-with-dependent-coconeᵉ)
      ( Pᵉ)
      ( dependent-cocone-cocone-with-dependent-coconeᵉ)

  vertical-map-dependent-cocone-with-dependent-coconeᵉ :
    (bᵉ : Bᵉ) → Pᵉ (vertical-map-cocone-with-dependent-coconeᵉ bᵉ)
  vertical-map-dependent-cocone-with-dependent-coconeᵉ =
    vertical-map-dependent-coconeᵉ fᵉ gᵉ
      ( cocone-cocone-with-dependent-coconeᵉ)
      ( Pᵉ)
      ( dependent-cocone-cocone-with-dependent-coconeᵉ)

  coherence-square-dependent-cocone-with-dependent-coconeᵉ :
    (sᵉ : Sᵉ) →
    dependent-identificationᵉ Pᵉ
      ( coherence-square-cocone-with-dependent-coconeᵉ sᵉ)
      ( horizontal-map-dependent-cocone-with-dependent-coconeᵉ (fᵉ sᵉ))
      ( vertical-map-dependent-cocone-with-dependent-coconeᵉ (gᵉ sᵉ))
  coherence-square-dependent-cocone-with-dependent-coconeᵉ =
    coherence-square-dependent-coconeᵉ fᵉ gᵉ
      ( cocone-cocone-with-dependent-coconeᵉ)
      ( Pᵉ)
      ( dependent-cocone-cocone-with-dependent-coconeᵉ)
```

### Postcomposing dependent cocones with maps

```agda
dependent-cocone-mapᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) (Pᵉ : Xᵉ → UUᵉ l5ᵉ) →
  ( (xᵉ : Xᵉ) → Pᵉ xᵉ) → dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ
pr1ᵉ (dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ hᵉ) aᵉ =
  hᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ aᵉ)
pr1ᵉ (pr2ᵉ (dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ hᵉ)) bᵉ =
  hᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ bᵉ)
pr2ᵉ (pr2ᵉ (dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ hᵉ)) sᵉ =
  apdᵉ hᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ)

dependent-cocone-map-span-diagramᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  ( cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ) (Pᵉ : Xᵉ → UUᵉ l5ᵉ) →
  ( (xᵉ : Xᵉ) → Pᵉ xᵉ) → dependent-cocone-span-diagramᵉ cᵉ Pᵉ
dependent-cocone-map-span-diagramᵉ {𝒮ᵉ = 𝒮ᵉ} cᵉ =
  dependent-cocone-mapᵉ (left-map-span-diagramᵉ 𝒮ᵉ) (right-map-span-diagramᵉ 𝒮ᵉ) cᵉ
```

## Properties

### Characterization of identifications of dependent cocones over a fixed cocone

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ)
  {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  (Pᵉ : Xᵉ → UUᵉ l5ᵉ) (dᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ)
  where

  coherence-htpy-dependent-coconeᵉ :
    ( d'ᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ) →
    ( horizontal-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ ~ᵉ
      horizontal-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ d'ᵉ) →
    ( vertical-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ ~ᵉ
      vertical-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ d'ᵉ) →
    UUᵉ (l1ᵉ ⊔ l5ᵉ)
  coherence-htpy-dependent-coconeᵉ d'ᵉ Kᵉ Lᵉ =
    (sᵉ : Sᵉ) →
    ( ( coherence-square-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ sᵉ) ∙ᵉ (Lᵉ (gᵉ sᵉ))) ＝ᵉ
    ( ( apᵉ (trᵉ Pᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ)) (Kᵉ (fᵉ sᵉ))) ∙ᵉ
      ( coherence-square-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ d'ᵉ sᵉ))

  htpy-dependent-coconeᵉ :
    (d'ᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l5ᵉ)
  htpy-dependent-coconeᵉ d'ᵉ =
    Σᵉ ( horizontal-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ ~ᵉ
        horizontal-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ d'ᵉ)
      ( λ Kᵉ →
        Σᵉ ( vertical-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ ~ᵉ
            vertical-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ d'ᵉ)
          ( coherence-htpy-dependent-coconeᵉ d'ᵉ Kᵉ))

  refl-htpy-dependent-coconeᵉ :
    htpy-dependent-coconeᵉ dᵉ
  pr1ᵉ refl-htpy-dependent-coconeᵉ = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ refl-htpy-dependent-coconeᵉ) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ refl-htpy-dependent-coconeᵉ) = right-unit-htpyᵉ

  htpy-eq-dependent-coconeᵉ :
    (d'ᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ) → dᵉ ＝ᵉ d'ᵉ → htpy-dependent-coconeᵉ d'ᵉ
  htpy-eq-dependent-coconeᵉ .dᵉ reflᵉ = refl-htpy-dependent-coconeᵉ

  module _
    (d'ᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ)
    (pᵉ : dᵉ ＝ᵉ d'ᵉ)
    where

    horizontal-htpy-eq-dependent-coconeᵉ :
      horizontal-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ ~ᵉ
      horizontal-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ d'ᵉ
    horizontal-htpy-eq-dependent-coconeᵉ =
      pr1ᵉ (htpy-eq-dependent-coconeᵉ d'ᵉ pᵉ)

    vertical-htpy-eq-dependent-coconeᵉ :
      vertical-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ ~ᵉ
      vertical-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ d'ᵉ
    vertical-htpy-eq-dependent-coconeᵉ =
      pr1ᵉ (pr2ᵉ (htpy-eq-dependent-coconeᵉ d'ᵉ pᵉ))

    coherence-square-htpy-eq-dependent-coconeᵉ :
      coherence-htpy-dependent-coconeᵉ d'ᵉ
        ( horizontal-htpy-eq-dependent-coconeᵉ)
        ( vertical-htpy-eq-dependent-coconeᵉ)
    coherence-square-htpy-eq-dependent-coconeᵉ =
      pr2ᵉ (pr2ᵉ (htpy-eq-dependent-coconeᵉ d'ᵉ pᵉ))

  abstract
    is-torsorial-htpy-dependent-coconeᵉ :
      is-torsorialᵉ htpy-dependent-coconeᵉ
    is-torsorial-htpy-dependent-coconeᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpyᵉ (horizontal-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ))
        ( horizontal-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ ,ᵉ refl-htpyᵉ)
        ( is-torsorial-Eq-structureᵉ
          ( is-torsorial-htpyᵉ (vertical-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ))
          ( vertical-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ ,ᵉ refl-htpyᵉ)
          ( is-contr-equivᵉ
            ( Σᵉ ( (sᵉ : Sᵉ) →
                  dependent-identificationᵉ Pᵉ
                    ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ)
                    ( horizontal-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ (fᵉ sᵉ))
                    ( vertical-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ (gᵉ sᵉ)))
                ( λ γᵉ → coherence-square-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ ~ᵉ γᵉ))
            ( equiv-totᵉ (equiv-concat-htpyᵉ inv-htpy-right-unit-htpyᵉ))
            ( is-torsorial-htpyᵉ
              ( coherence-square-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ))))

  abstract
    is-equiv-htpy-eq-dependent-coconeᵉ :
      (d'ᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ) → is-equivᵉ (htpy-eq-dependent-coconeᵉ d'ᵉ)
    is-equiv-htpy-eq-dependent-coconeᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-htpy-dependent-coconeᵉ)
        ( htpy-eq-dependent-coconeᵉ)

    eq-htpy-dependent-coconeᵉ :
      (d'ᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ) → htpy-dependent-coconeᵉ d'ᵉ → dᵉ ＝ᵉ d'ᵉ
    eq-htpy-dependent-coconeᵉ d'ᵉ =
      map-inv-is-equivᵉ (is-equiv-htpy-eq-dependent-coconeᵉ d'ᵉ)

    is-section-eq-htpy-dependent-coconeᵉ :
      (d'ᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ) →
      ( htpy-eq-dependent-coconeᵉ d'ᵉ ∘ᵉ eq-htpy-dependent-coconeᵉ d'ᵉ) ~ᵉ idᵉ
    is-section-eq-htpy-dependent-coconeᵉ d'ᵉ =
      is-section-map-inv-is-equivᵉ (is-equiv-htpy-eq-dependent-coconeᵉ d'ᵉ)

    is-retraction-eq-htpy-dependent-coconeᵉ :
      (d'ᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ) →
      ( eq-htpy-dependent-coconeᵉ d'ᵉ ∘ᵉ htpy-eq-dependent-coconeᵉ d'ᵉ) ~ᵉ idᵉ
    is-retraction-eq-htpy-dependent-coconeᵉ d'ᵉ =
      is-retraction-map-inv-is-equivᵉ (is-equiv-htpy-eq-dependent-coconeᵉ d'ᵉ)
```

### Dependent homotopies of dependent cocones over homotopies of cocones

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ)
  {Xᵉ : UUᵉ l4ᵉ}
  where

  coherence-dependent-htpy-dependent-coconeᵉ :
    ( cᵉ c'ᵉ : coconeᵉ fᵉ gᵉ Xᵉ) (Hᵉ : htpy-coconeᵉ fᵉ gᵉ cᵉ c'ᵉ) (Pᵉ : Xᵉ → UUᵉ l5ᵉ)
    ( dᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ)
    ( d'ᵉ : dependent-coconeᵉ fᵉ gᵉ c'ᵉ Pᵉ) →
    dependent-homotopyᵉ (λ _ → Pᵉ)
      ( horizontal-htpy-coconeᵉ fᵉ gᵉ cᵉ c'ᵉ Hᵉ)
      ( horizontal-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ)
      ( horizontal-map-dependent-coconeᵉ fᵉ gᵉ c'ᵉ Pᵉ d'ᵉ) →
    dependent-homotopyᵉ (λ _ → Pᵉ)
      ( vertical-htpy-coconeᵉ fᵉ gᵉ cᵉ c'ᵉ Hᵉ)
      ( vertical-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ)
      ( vertical-map-dependent-coconeᵉ fᵉ gᵉ c'ᵉ Pᵉ d'ᵉ) →
    UUᵉ (l1ᵉ ⊔ l5ᵉ)
  coherence-dependent-htpy-dependent-coconeᵉ cᵉ c'ᵉ Hᵉ Pᵉ dᵉ d'ᵉ Kᵉ Lᵉ =
    (sᵉ : Sᵉ) →
    dependent-identification²ᵉ Pᵉ
      ( coherence-htpy-coconeᵉ fᵉ gᵉ cᵉ c'ᵉ Hᵉ sᵉ)
      ( concat-dependent-identificationᵉ Pᵉ
        ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ)
        ( vertical-htpy-coconeᵉ fᵉ gᵉ cᵉ c'ᵉ Hᵉ (gᵉ sᵉ))
        ( coherence-square-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ sᵉ)
        ( Lᵉ (gᵉ sᵉ)))
      ( concat-dependent-identificationᵉ Pᵉ
        ( horizontal-htpy-coconeᵉ fᵉ gᵉ cᵉ c'ᵉ Hᵉ (fᵉ sᵉ))
        ( coherence-square-coconeᵉ fᵉ gᵉ c'ᵉ sᵉ)
        ( Kᵉ (fᵉ sᵉ))
        ( coherence-square-dependent-coconeᵉ fᵉ gᵉ c'ᵉ Pᵉ d'ᵉ sᵉ))

  dependent-htpy-dependent-coconeᵉ :
    ( cᵉ c'ᵉ : coconeᵉ fᵉ gᵉ Xᵉ) (Hᵉ : htpy-coconeᵉ fᵉ gᵉ cᵉ c'ᵉ) (Pᵉ : Xᵉ → UUᵉ l5ᵉ)
    ( dᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ) (d'ᵉ : dependent-coconeᵉ fᵉ gᵉ c'ᵉ Pᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l5ᵉ)
  dependent-htpy-dependent-coconeᵉ cᵉ c'ᵉ Hᵉ Pᵉ dᵉ d'ᵉ =
    Σᵉ ( dependent-homotopyᵉ (λ _ → Pᵉ)
        ( horizontal-htpy-coconeᵉ fᵉ gᵉ cᵉ c'ᵉ Hᵉ)
        ( horizontal-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ)
        ( horizontal-map-dependent-coconeᵉ fᵉ gᵉ c'ᵉ Pᵉ d'ᵉ))
      ( λ Kᵉ →
        Σᵉ ( dependent-homotopyᵉ (λ _ → Pᵉ)
            ( vertical-htpy-coconeᵉ fᵉ gᵉ cᵉ c'ᵉ Hᵉ)
            ( vertical-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ)
            ( vertical-map-dependent-coconeᵉ fᵉ gᵉ c'ᵉ Pᵉ d'ᵉ))
          ( coherence-dependent-htpy-dependent-coconeᵉ cᵉ c'ᵉ Hᵉ Pᵉ dᵉ d'ᵉ Kᵉ))

  refl-dependent-htpy-dependent-coconeᵉ :
    ( cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) (Pᵉ : Xᵉ → UUᵉ l5ᵉ) (dᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ) →
    dependent-htpy-dependent-coconeᵉ cᵉ cᵉ (refl-htpy-coconeᵉ fᵉ gᵉ cᵉ) Pᵉ dᵉ dᵉ
  pr1ᵉ (refl-dependent-htpy-dependent-coconeᵉ cᵉ Pᵉ dᵉ) = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ (refl-dependent-htpy-dependent-coconeᵉ cᵉ Pᵉ dᵉ)) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ (refl-dependent-htpy-dependent-coconeᵉ cᵉ Pᵉ dᵉ)) sᵉ =
    right-unit-dependent-identificationᵉ Pᵉ
      ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ)
      ( coherence-square-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ sᵉ)

  dependent-htpy-dependent-eq-dependent-coconeᵉ :
    (cᵉ c'ᵉ : coconeᵉ fᵉ gᵉ Xᵉ) (pᵉ : cᵉ ＝ᵉ c'ᵉ) (Pᵉ : Xᵉ → UUᵉ l5ᵉ)
    (dᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ) (d'ᵉ : dependent-coconeᵉ fᵉ gᵉ c'ᵉ Pᵉ) →
    dependent-identificationᵉ (λ c''ᵉ → dependent-coconeᵉ fᵉ gᵉ c''ᵉ Pᵉ) pᵉ dᵉ d'ᵉ →
    dependent-htpy-dependent-coconeᵉ cᵉ c'ᵉ (htpy-eq-coconeᵉ fᵉ gᵉ cᵉ c'ᵉ pᵉ) Pᵉ dᵉ d'ᵉ
  dependent-htpy-dependent-eq-dependent-coconeᵉ cᵉ .cᵉ reflᵉ Pᵉ dᵉ ._ reflᵉ =
    refl-dependent-htpy-dependent-coconeᵉ cᵉ Pᵉ dᵉ

  abstract
    is-torsorial-dependent-htpy-over-refl-dependent-coconeᵉ :
      (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) (Pᵉ : Xᵉ → UUᵉ l5ᵉ) (dᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ) →
      is-torsorialᵉ
        ( dependent-htpy-dependent-coconeᵉ cᵉ cᵉ (refl-htpy-coconeᵉ fᵉ gᵉ cᵉ) Pᵉ dᵉ)
    is-torsorial-dependent-htpy-over-refl-dependent-coconeᵉ cᵉ Pᵉ dᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpyᵉ _)
        ( horizontal-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ ,ᵉ refl-htpyᵉ)
        ( is-torsorial-Eq-structureᵉ
          ( is-torsorial-htpyᵉ _)
          ( vertical-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ dᵉ ,ᵉ refl-htpyᵉ)
          ( is-torsorial-htpyᵉ _))
```

#### Characterizing equality of cocones equipped with dependent cocones

Weᵉ nowᵉ moveᵉ to characterizeᵉ equalityᵉ ofᵉ coconesᵉ equippedᵉ with dependentᵉ cocones,ᵉ
fromᵉ whichᵉ itᵉ followsᵉ thatᵉ dependentᵉ homotopiesᵉ ofᵉ dependentᵉ coconesᵉ
characterizeᵉ dependentᵉ identificationsᵉ ofᵉ them.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ)
  {Xᵉ : UUᵉ l4ᵉ} (Pᵉ : Xᵉ → UUᵉ l5ᵉ)
  where

  htpy-cocone-with-dependent-coconeᵉ :
    (cᵉ c'ᵉ : cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
  htpy-cocone-with-dependent-coconeᵉ cᵉ c'ᵉ =
    Σᵉ ( htpy-coconeᵉ fᵉ gᵉ
        ( cocone-cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ cᵉ)
        ( cocone-cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ c'ᵉ))
      ( λ Hᵉ →
        dependent-htpy-dependent-coconeᵉ fᵉ gᵉ
          ( cocone-cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ cᵉ)
          ( cocone-cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ c'ᵉ)
          ( Hᵉ)
          ( Pᵉ)
          ( dependent-cocone-cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ cᵉ)
          ( dependent-cocone-cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ c'ᵉ))

  refl-htpy-cocone-with-dependent-coconeᵉ :
    (cᵉ : cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ) →
    htpy-cocone-with-dependent-coconeᵉ cᵉ cᵉ
  pr1ᵉ (refl-htpy-cocone-with-dependent-coconeᵉ cᵉ) =
    refl-htpy-coconeᵉ fᵉ gᵉ (cocone-cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ cᵉ)
  pr2ᵉ (refl-htpy-cocone-with-dependent-coconeᵉ cᵉ) =
    refl-dependent-htpy-dependent-coconeᵉ fᵉ gᵉ
      ( cocone-cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ cᵉ)
      ( Pᵉ)
      ( dependent-cocone-cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ cᵉ)

  htpy-eq-cocone-with-dependent-coconeᵉ :
    (cᵉ c'ᵉ : cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ) →
    cᵉ ＝ᵉ c'ᵉ →
    htpy-cocone-with-dependent-coconeᵉ cᵉ c'ᵉ
  htpy-eq-cocone-with-dependent-coconeᵉ cᵉ .cᵉ reflᵉ =
    refl-htpy-cocone-with-dependent-coconeᵉ cᵉ

  abstract
    is-torsorial-htpy-cocone-with-dependent-coconeᵉ :
      (cᵉ : cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ) →
      is-torsorialᵉ (htpy-cocone-with-dependent-coconeᵉ cᵉ)
    is-torsorial-htpy-cocone-with-dependent-coconeᵉ cᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpy-coconeᵉ fᵉ gᵉ
          ( cocone-cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ cᵉ))
        ( cocone-cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ cᵉ ,ᵉ
          refl-htpy-coconeᵉ fᵉ gᵉ (cocone-cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ cᵉ))
        ( is-torsorial-dependent-htpy-over-refl-dependent-coconeᵉ fᵉ gᵉ
          ( cocone-cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ cᵉ)
          ( Pᵉ)
          ( dependent-cocone-cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ cᵉ))

  abstract
    is-equiv-htpy-eq-cocone-with-dependent-coconeᵉ :
      (cᵉ c'ᵉ : cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ) →
      is-equivᵉ (htpy-eq-cocone-with-dependent-coconeᵉ cᵉ c'ᵉ)
    is-equiv-htpy-eq-cocone-with-dependent-coconeᵉ cᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-htpy-cocone-with-dependent-coconeᵉ cᵉ)
        ( htpy-eq-cocone-with-dependent-coconeᵉ cᵉ)

  eq-htpy-cocone-with-dependent-coconeᵉ :
    (cᵉ c'ᵉ : cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ) →
    htpy-cocone-with-dependent-coconeᵉ cᵉ c'ᵉ → cᵉ ＝ᵉ c'ᵉ
  eq-htpy-cocone-with-dependent-coconeᵉ cᵉ c'ᵉ =
    map-inv-is-equivᵉ (is-equiv-htpy-eq-cocone-with-dependent-coconeᵉ cᵉ c'ᵉ)

  extensionality-cocone-with-dependent-coconeᵉ :
    (cᵉ c'ᵉ : cocone-with-dependent-coconeᵉ fᵉ gᵉ Pᵉ) →
    (cᵉ ＝ᵉ c'ᵉ) ≃ᵉ htpy-cocone-with-dependent-coconeᵉ cᵉ c'ᵉ
  extensionality-cocone-with-dependent-coconeᵉ cᵉ c'ᵉ =
    ( htpy-eq-cocone-with-dependent-coconeᵉ cᵉ c'ᵉ ,ᵉ
      is-equiv-htpy-eq-cocone-with-dependent-coconeᵉ cᵉ c'ᵉ)
```

### Dependent cocones on constant type families are equivalent to nondependent cocones

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) {Yᵉ : UUᵉ l5ᵉ}
  where

  dependent-cocone-constant-type-family-coconeᵉ :
    coconeᵉ fᵉ gᵉ Yᵉ → dependent-coconeᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ)
  pr1ᵉ (dependent-cocone-constant-type-family-coconeᵉ (f'ᵉ ,ᵉ g'ᵉ ,ᵉ Hᵉ)) = f'ᵉ
  pr1ᵉ (pr2ᵉ (dependent-cocone-constant-type-family-coconeᵉ (f'ᵉ ,ᵉ g'ᵉ ,ᵉ Hᵉ))) = g'ᵉ
  pr2ᵉ (pr2ᵉ (dependent-cocone-constant-type-family-coconeᵉ (f'ᵉ ,ᵉ g'ᵉ ,ᵉ Hᵉ))) sᵉ =
    tr-constant-type-familyᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ) (f'ᵉ (fᵉ sᵉ)) ∙ᵉ Hᵉ sᵉ

  cocone-dependent-cocone-constant-type-familyᵉ :
    dependent-coconeᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ) → coconeᵉ fᵉ gᵉ Yᵉ
  pr1ᵉ (cocone-dependent-cocone-constant-type-familyᵉ (f'ᵉ ,ᵉ g'ᵉ ,ᵉ Hᵉ)) = f'ᵉ
  pr1ᵉ (pr2ᵉ (cocone-dependent-cocone-constant-type-familyᵉ (f'ᵉ ,ᵉ g'ᵉ ,ᵉ Hᵉ))) = g'ᵉ
  pr2ᵉ (pr2ᵉ (cocone-dependent-cocone-constant-type-familyᵉ (f'ᵉ ,ᵉ g'ᵉ ,ᵉ Hᵉ))) sᵉ =
    ( invᵉ
      ( tr-constant-type-familyᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ) (f'ᵉ (fᵉ sᵉ)))) ∙ᵉ
    ( Hᵉ sᵉ)

  is-section-cocone-dependent-cocone-constant-type-familyᵉ :
    is-sectionᵉ
      ( dependent-cocone-constant-type-family-coconeᵉ)
      ( cocone-dependent-cocone-constant-type-familyᵉ)
  is-section-cocone-dependent-cocone-constant-type-familyᵉ (f'ᵉ ,ᵉ g'ᵉ ,ᵉ Hᵉ) =
    eq-pair-eq-fiberᵉ
      ( eq-pair-eq-fiberᵉ
        ( eq-htpyᵉ
          ( λ sᵉ →
            is-section-inv-concatᵉ
              ( tr-constant-type-familyᵉ
                ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ)
                ( f'ᵉ (fᵉ sᵉ)))
              ( Hᵉ sᵉ))))

  is-retraction-cocone-dependent-cocone-constant-type-familyᵉ :
    is-retractionᵉ
      ( dependent-cocone-constant-type-family-coconeᵉ)
      ( cocone-dependent-cocone-constant-type-familyᵉ)
  is-retraction-cocone-dependent-cocone-constant-type-familyᵉ (f'ᵉ ,ᵉ g'ᵉ ,ᵉ Hᵉ) =
    eq-pair-eq-fiberᵉ
      ( eq-pair-eq-fiberᵉ
        ( eq-htpyᵉ
          ( λ sᵉ →
            is-retraction-inv-concatᵉ
              ( tr-constant-type-familyᵉ
                ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ)
                ( f'ᵉ (fᵉ sᵉ)))
              ( Hᵉ sᵉ))))

  is-equiv-dependent-cocone-constant-type-family-coconeᵉ :
    is-equivᵉ dependent-cocone-constant-type-family-coconeᵉ
  is-equiv-dependent-cocone-constant-type-family-coconeᵉ =
    is-equiv-is-invertibleᵉ
      ( cocone-dependent-cocone-constant-type-familyᵉ)
      ( is-section-cocone-dependent-cocone-constant-type-familyᵉ)
      ( is-retraction-cocone-dependent-cocone-constant-type-familyᵉ)

  compute-dependent-cocone-constant-type-familyᵉ :
    coconeᵉ fᵉ gᵉ Yᵉ ≃ᵉ dependent-coconeᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ)
  compute-dependent-cocone-constant-type-familyᵉ =
    ( dependent-cocone-constant-type-family-coconeᵉ ,ᵉ
      is-equiv-dependent-cocone-constant-type-family-coconeᵉ)
```

### Computing the dependent cocone map on a constant type family

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) {Yᵉ : UUᵉ l5ᵉ}
  where

  triangle-dependent-cocone-map-constant-type-familyᵉ :
    dependent-cocone-mapᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ) ~ᵉ
    dependent-cocone-constant-type-family-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ cocone-mapᵉ fᵉ gᵉ cᵉ
  triangle-dependent-cocone-map-constant-type-familyᵉ hᵉ =
    eq-htpy-dependent-coconeᵉ fᵉ gᵉ cᵉ
      ( λ _ → Yᵉ)
      ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ) hᵉ)
      ( dependent-cocone-constant-type-family-coconeᵉ fᵉ gᵉ cᵉ (cocone-mapᵉ fᵉ gᵉ cᵉ hᵉ))
      ( ( refl-htpyᵉ) ,ᵉ
        ( refl-htpyᵉ) ,ᵉ
        ( λ sᵉ →
          right-unitᵉ ∙ᵉ
          apd-constant-type-familyᵉ hᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ)))

  triangle-dependent-cocone-map-constant-type-family'ᵉ :
    cocone-mapᵉ fᵉ gᵉ cᵉ ~ᵉ
    cocone-dependent-cocone-constant-type-familyᵉ fᵉ gᵉ cᵉ ∘ᵉ
    dependent-cocone-mapᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ)
  triangle-dependent-cocone-map-constant-type-family'ᵉ hᵉ =
    eq-htpy-coconeᵉ fᵉ gᵉ
      ( cocone-mapᵉ fᵉ gᵉ cᵉ hᵉ)
      ( ( cocone-dependent-cocone-constant-type-familyᵉ fᵉ gᵉ cᵉ
          ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ) hᵉ)))
      ( ( refl-htpyᵉ) ,ᵉ
        ( refl-htpyᵉ) ,ᵉ
        ( λ sᵉ →
          right-unitᵉ ∙ᵉ
          left-transpose-eq-concatᵉ
            ( tr-constant-type-familyᵉ
              ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ)
              ( pr1ᵉ (dependent-cocone-mapᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ) hᵉ) (fᵉ sᵉ)))
            ( apᵉ hᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ))
            ( apdᵉ hᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ))
            ( invᵉ
              ( apd-constant-type-familyᵉ hᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ)))))
```

### The nondependent cocone map at `Y` is an equivalence if and only if the dependent cocone map at the constant type family `(λ _ → Y)` is

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) {Yᵉ : UUᵉ l5ᵉ}
  where

  is-equiv-cocone-map-is-equiv-dependent-cocone-map-constant-type-familyᵉ :
    is-equivᵉ (dependent-cocone-mapᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ)) →
    is-equivᵉ (cocone-mapᵉ fᵉ gᵉ cᵉ)
  is-equiv-cocone-map-is-equiv-dependent-cocone-map-constant-type-familyᵉ =
    is-equiv-top-map-triangleᵉ
      ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ))
      ( dependent-cocone-constant-type-family-coconeᵉ fᵉ gᵉ cᵉ)
      ( cocone-mapᵉ fᵉ gᵉ cᵉ)
      ( triangle-dependent-cocone-map-constant-type-familyᵉ fᵉ gᵉ cᵉ)
      ( is-equiv-dependent-cocone-constant-type-family-coconeᵉ fᵉ gᵉ cᵉ)

  is-equiv-dependent-cocone-map-constant-type-family-is-equiv-cocone-mapᵉ :
    is-equivᵉ (cocone-mapᵉ fᵉ gᵉ cᵉ) →
    is-equivᵉ (dependent-cocone-mapᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ))
  is-equiv-dependent-cocone-map-constant-type-family-is-equiv-cocone-mapᵉ Hᵉ =
    is-equiv-left-map-triangleᵉ
      ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ))
      ( dependent-cocone-constant-type-family-coconeᵉ fᵉ gᵉ cᵉ)
      ( cocone-mapᵉ fᵉ gᵉ cᵉ)
      ( triangle-dependent-cocone-map-constant-type-familyᵉ fᵉ gᵉ cᵉ)
      ( Hᵉ)
      ( is-equiv-dependent-cocone-constant-type-family-coconeᵉ fᵉ gᵉ cᵉ)
```

### Computing with the characterization of identifications of dependent cocones on constant type families over a fixed cocone

Ifᵉ twoᵉ dependentᵉ coconesᵉ onᵉ aᵉ constantᵉ typeᵉ familyᵉ areᵉ homotopic,ᵉ thenᵉ soᵉ areᵉ
theirᵉ nondependentᵉ counterparts.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ)
  {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  (Yᵉ : UUᵉ l5ᵉ)
  where

  coherence-htpy-cocone-dependent-cocone-coherence-htpy-dependent-cocone-constant-type-familyᵉ :
    ( dᵉ d'ᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ)) →
    ( Kᵉ :
      horizontal-map-dependent-coconeᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ) dᵉ ~ᵉ
      horizontal-map-dependent-coconeᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ) d'ᵉ)
    ( Lᵉ :
      vertical-map-dependent-coconeᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ) dᵉ ~ᵉ
      vertical-map-dependent-coconeᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ) d'ᵉ)
    ( Hᵉ : coherence-htpy-dependent-coconeᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ) dᵉ d'ᵉ Kᵉ Lᵉ) →
    statement-coherence-htpy-coconeᵉ fᵉ gᵉ
      ( cocone-dependent-cocone-constant-type-familyᵉ fᵉ gᵉ cᵉ dᵉ)
      ( cocone-dependent-cocone-constant-type-familyᵉ fᵉ gᵉ cᵉ d'ᵉ)
      ( Kᵉ)
      ( Lᵉ)
  coherence-htpy-cocone-dependent-cocone-coherence-htpy-dependent-cocone-constant-type-familyᵉ
    dᵉ d'ᵉ Kᵉ Lᵉ Hᵉ xᵉ =
    ( left-whisker-concat-coherence-square-identificationsᵉ
      ( invᵉ
        ( tr-constant-type-familyᵉ
          ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ xᵉ)
          ( horizontal-map-dependent-coconeᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ) dᵉ (fᵉ xᵉ))))
      ( apᵉ (trᵉ (λ _ → Yᵉ) (coherence-square-coconeᵉ fᵉ gᵉ cᵉ xᵉ)) (Kᵉ (fᵉ xᵉ)))
      ( coherence-square-dependent-coconeᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ) dᵉ xᵉ)
      ( coherence-square-dependent-coconeᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ) d'ᵉ xᵉ)
      ( Lᵉ (gᵉ xᵉ))
      ( Hᵉ xᵉ)) ∙ᵉ
    ( apᵉ
      ( _∙ᵉ coherence-square-dependent-coconeᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ) d'ᵉ xᵉ)
      ( naturality-inv-tr-constant-type-familyᵉ
        ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ xᵉ)
        ( Kᵉ (fᵉ xᵉ)))) ∙ᵉ
    ( assocᵉ
      ( Kᵉ (fᵉ xᵉ))
      ( invᵉ
        ( tr-constant-type-familyᵉ
          ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ xᵉ)
          ( horizontal-map-dependent-coconeᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ) d'ᵉ (fᵉ xᵉ))))
      ( coherence-square-dependent-coconeᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ) d'ᵉ xᵉ))
```

Ifᵉ theᵉ dependentᵉ coconesᵉ onᵉ constantᵉ typeᵉ familiesᵉ constructedᵉ fromᵉ nondependentᵉ
coconesᵉ areᵉ homotopic,ᵉ thenᵉ soᵉ areᵉ theᵉ nondependentᵉ cocones.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ)
  {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ}
  where

  coherence-htpy-cocone-coherence-htpy-dependent-cocone-constant-type-familyᵉ :
    (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
    (dᵉ d'ᵉ : coconeᵉ fᵉ gᵉ Yᵉ) →
    ( Kᵉ : horizontal-map-coconeᵉ fᵉ gᵉ dᵉ ~ᵉ horizontal-map-coconeᵉ fᵉ gᵉ d'ᵉ)
    ( Lᵉ : vertical-map-coconeᵉ fᵉ gᵉ dᵉ ~ᵉ vertical-map-coconeᵉ fᵉ gᵉ d'ᵉ) →
    coherence-htpy-dependent-coconeᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ)
      ( dependent-cocone-constant-type-family-coconeᵉ fᵉ gᵉ cᵉ dᵉ)
      ( dependent-cocone-constant-type-family-coconeᵉ fᵉ gᵉ cᵉ d'ᵉ)
      ( Kᵉ)
      ( Lᵉ) →
    statement-coherence-htpy-coconeᵉ fᵉ gᵉ
      ( dᵉ)
      ( d'ᵉ)
      ( Kᵉ)
      ( Lᵉ)
  coherence-htpy-cocone-coherence-htpy-dependent-cocone-constant-type-familyᵉ
    cᵉ dᵉ d'ᵉ Kᵉ Lᵉ Hᵉ xᵉ =
    is-injective-concatᵉ
      ( tr-constant-type-familyᵉ
        ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ xᵉ)
        ( horizontal-map-coconeᵉ fᵉ gᵉ dᵉ (fᵉ xᵉ)))
      ( ( invᵉ
          ( assocᵉ
            ( tr-constant-type-familyᵉ
              ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ xᵉ)
              ( horizontal-map-coconeᵉ fᵉ gᵉ dᵉ (fᵉ xᵉ)))
            ( coherence-square-coconeᵉ fᵉ gᵉ dᵉ xᵉ)
            ( Lᵉ (gᵉ xᵉ)))) ∙ᵉ
        ( Hᵉ xᵉ) ∙ᵉ
        ( right-whisker-concat-coherence-square-identificationsᵉ
          ( tr-constant-type-familyᵉ
            ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ xᵉ)
            ( horizontal-map-coconeᵉ fᵉ gᵉ dᵉ (fᵉ xᵉ)))
          ( apᵉ (trᵉ (λ _ → Yᵉ) (coherence-square-coconeᵉ fᵉ gᵉ cᵉ xᵉ)) (Kᵉ (fᵉ xᵉ)))
          ( Kᵉ (fᵉ xᵉ))
          ( tr-constant-type-familyᵉ
            ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ xᵉ)
            ( horizontal-map-coconeᵉ fᵉ gᵉ d'ᵉ (fᵉ xᵉ)))
          ( invᵉ
            ( naturality-tr-constant-type-familyᵉ
              ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ xᵉ)
              ( Kᵉ (fᵉ xᵉ))))
          ( coherence-square-coconeᵉ fᵉ gᵉ d'ᵉ xᵉ)))
```