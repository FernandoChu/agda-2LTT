# Suspensions of types

```agda
module synthetic-homotopy-theory.suspensions-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.connected-typesᵉ
open import foundation.constant-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.diagonal-maps-of-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.path-algebraᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.dependent-cocones-under-spansᵉ
open import synthetic-homotopy-theory.dependent-suspension-structuresᵉ
open import synthetic-homotopy-theory.dependent-universal-property-suspensionsᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
open import synthetic-homotopy-theory.suspension-structuresᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
open import synthetic-homotopy-theory.universal-property-suspensionsᵉ
```

</details>

## Idea

Theᵉ **suspension**ᵉ ofᵉ aᵉ typeᵉ `X`ᵉ isᵉ theᵉ
[pushout](synthetic-homotopy-theory.pushouts.mdᵉ) ofᵉ theᵉ
[span](foundation.spans.mdᵉ)

```text
unitᵉ <--ᵉ Xᵉ -->ᵉ unitᵉ
```

Suspensionsᵉ playᵉ anᵉ importantᵉ roleᵉ in syntheticᵉ homotopyᵉ theory.ᵉ Forᵉ example,ᵉ
theyᵉ starᵉ in theᵉ freudenthalᵉ suspensionᵉ theoremᵉ andᵉ giveᵉ usᵉ aᵉ definitionᵉ ofᵉ
[theᵉ spheres](synthetic-homotopy-theory.spheres.md).ᵉ

## Definitions

### The suspension of a type

```agda
suspensionᵉ :
  {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
suspensionᵉ Xᵉ = pushoutᵉ (terminal-mapᵉ Xᵉ) (terminal-mapᵉ Xᵉ)

north-suspensionᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → suspensionᵉ Xᵉ
north-suspensionᵉ {Xᵉ = Xᵉ} =
  inl-pushoutᵉ (terminal-mapᵉ Xᵉ) (terminal-mapᵉ Xᵉ) starᵉ

south-suspensionᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → suspensionᵉ Xᵉ
south-suspensionᵉ {Xᵉ = Xᵉ} =
  inr-pushoutᵉ (terminal-mapᵉ Xᵉ) (terminal-mapᵉ Xᵉ) starᵉ

meridian-suspensionᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → Xᵉ →
  north-suspensionᵉ {Xᵉ = Xᵉ} ＝ᵉ south-suspensionᵉ {Xᵉ = Xᵉ}
meridian-suspensionᵉ {Xᵉ = Xᵉ} =
  glue-pushoutᵉ (terminal-mapᵉ Xᵉ) (terminal-mapᵉ Xᵉ)

suspension-structure-suspensionᵉ :
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → suspension-structureᵉ Xᵉ (suspensionᵉ Xᵉ)
pr1ᵉ (suspension-structure-suspensionᵉ Xᵉ) = north-suspensionᵉ
pr1ᵉ (pr2ᵉ (suspension-structure-suspensionᵉ Xᵉ)) = south-suspensionᵉ
pr2ᵉ (pr2ᵉ (suspension-structure-suspensionᵉ Xᵉ)) = meridian-suspensionᵉ

cocone-suspensionᵉ :
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) →
  coconeᵉ (terminal-mapᵉ Xᵉ) (terminal-mapᵉ Xᵉ) (suspensionᵉ Xᵉ)
cocone-suspensionᵉ Xᵉ =
  cocone-pushoutᵉ (terminal-mapᵉ Xᵉ) (terminal-mapᵉ Xᵉ)

cogap-suspension'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} →
  coconeᵉ (terminal-mapᵉ Xᵉ) (terminal-mapᵉ Xᵉ) Yᵉ → suspensionᵉ Xᵉ → Yᵉ
cogap-suspension'ᵉ {Xᵉ = Xᵉ} = cogapᵉ (terminal-mapᵉ Xᵉ) (terminal-mapᵉ Xᵉ)

up-suspension'ᵉ :
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) →
  universal-property-pushoutᵉ
    ( terminal-mapᵉ Xᵉ)
    ( terminal-mapᵉ Xᵉ)
    ( cocone-suspensionᵉ Xᵉ)
up-suspension'ᵉ Xᵉ = up-pushoutᵉ (terminal-mapᵉ Xᵉ) (terminal-mapᵉ Xᵉ)
```

### The cogap map of a suspension structure

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (sᵉ : suspension-structureᵉ Xᵉ Yᵉ)
  where

  cogap-suspensionᵉ : suspensionᵉ Xᵉ → Yᵉ
  cogap-suspensionᵉ =
    cogap-suspension'ᵉ (suspension-cocone-suspension-structureᵉ sᵉ)
```

### The property of being a suspension

Theᵉ [proposition](foundation-core.propositions.mdᵉ) `is-suspension`ᵉ isᵉ theᵉ
assertionᵉ thatᵉ theᵉ cogapᵉ mapᵉ isᵉ anᵉ
[equivalence](foundation-core.equivalences.md).ᵉ Noteᵉ thatᵉ thisᵉ propositionᵉ isᵉ
[small](foundation-core.small-types.md),ᵉ whereasᵉ
[theᵉ universalᵉ property](foundation-core.universal-property-pullbacks.mdᵉ) isᵉ aᵉ
largeᵉ proposition.ᵉ

```agda
is-suspensionᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} →
  suspension-structureᵉ Xᵉ Yᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-suspensionᵉ sᵉ = is-equivᵉ (cogap-suspensionᵉ sᵉ)
```

## Properties

### The suspension of `X` has the universal property of suspensions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Zᵉ : UUᵉ l2ᵉ}
  where

  is-section-cogap-suspensionᵉ :
    is-sectionᵉ
      ( ev-suspensionᵉ (suspension-structure-suspensionᵉ Xᵉ) Zᵉ)
      ( cogap-suspensionᵉ)
  is-section-cogap-suspensionᵉ =
    ( suspension-structure-suspension-coconeᵉ) ·lᵉ
    ( is-section-cogapᵉ (terminal-mapᵉ Xᵉ) (terminal-mapᵉ Xᵉ)) ·rᵉ
    ( suspension-cocone-suspension-structureᵉ)

  is-retraction-cogap-suspensionᵉ :
    is-retractionᵉ
      ( ev-suspensionᵉ (suspension-structure-suspensionᵉ Xᵉ) Zᵉ)
      ( cogap-suspensionᵉ)
  is-retraction-cogap-suspensionᵉ =
    ( is-retraction-cogapᵉ (terminal-mapᵉ Xᵉ) (terminal-mapᵉ Xᵉ))

up-suspensionᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} →
  universal-property-suspensionᵉ (suspension-structure-suspensionᵉ Xᵉ)
up-suspensionᵉ Zᵉ =
  is-equiv-is-invertibleᵉ
    ( cogap-suspensionᵉ)
    ( is-section-cogap-suspensionᵉ)
    ( is-retraction-cogap-suspensionᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Zᵉ : UUᵉ l2ᵉ}
  where

  equiv-up-suspensionᵉ :
    (suspensionᵉ Xᵉ → Zᵉ) ≃ᵉ (suspension-structureᵉ Xᵉ Zᵉ)
  pr1ᵉ equiv-up-suspensionᵉ =
    ev-suspensionᵉ (suspension-structure-suspensionᵉ Xᵉ) Zᵉ
  pr2ᵉ equiv-up-suspensionᵉ = up-suspensionᵉ Zᵉ

  compute-north-cogap-suspensionᵉ :
    (cᵉ : suspension-structureᵉ Xᵉ Zᵉ) →
    ( cogap-suspensionᵉ cᵉ north-suspensionᵉ) ＝ᵉ
    ( north-suspension-structureᵉ cᵉ)
  compute-north-cogap-suspensionᵉ cᵉ =
    pr1ᵉ
      ( htpy-eq-suspension-structureᵉ
        ( is-section-cogap-suspensionᵉ cᵉ))

  compute-south-cogap-suspensionᵉ :
    (cᵉ : suspension-structureᵉ Xᵉ Zᵉ) →
    ( cogap-suspensionᵉ cᵉ south-suspensionᵉ) ＝ᵉ
    ( south-suspension-structureᵉ cᵉ)
  compute-south-cogap-suspensionᵉ cᵉ =
    pr1ᵉ
      ( pr2ᵉ
        ( htpy-eq-suspension-structureᵉ
          ( is-section-cogap-suspensionᵉ cᵉ)))

  compute-meridian-cogap-suspensionᵉ :
    (cᵉ : suspension-structureᵉ Xᵉ Zᵉ) (xᵉ : Xᵉ) →
    ( ( apᵉ (cogap-suspensionᵉ cᵉ) (meridian-suspensionᵉ xᵉ)) ∙ᵉ
      ( compute-south-cogap-suspensionᵉ cᵉ)) ＝ᵉ
    ( ( compute-north-cogap-suspensionᵉ cᵉ) ∙ᵉ
      ( meridian-suspension-structureᵉ cᵉ xᵉ))
  compute-meridian-cogap-suspensionᵉ cᵉ =
    pr2ᵉ
      ( pr2ᵉ
        ( htpy-eq-suspension-structureᵉ
          ( is-section-cogap-suspensionᵉ cᵉ)))

  ev-suspension-up-suspensionᵉ :
    (cᵉ : suspension-structureᵉ Xᵉ Zᵉ) →
    ( ev-suspensionᵉ
      ( suspension-structure-suspensionᵉ Xᵉ)
      ( Zᵉ)
      ( cogap-suspensionᵉ cᵉ)) ＝ᵉ cᵉ
  ev-suspension-up-suspensionᵉ cᵉ =
    eq-htpy-suspension-structureᵉ
      ( ( compute-north-cogap-suspensionᵉ cᵉ) ,ᵉ
        ( compute-south-cogap-suspensionᵉ cᵉ) ,ᵉ
        ( compute-meridian-cogap-suspensionᵉ cᵉ))
```

### The suspension of `X` has the dependent universal property of suspensions

```agda
dup-suspensionᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} →
  dependent-universal-property-suspensionᵉ (suspension-structure-suspensionᵉ Xᵉ)
dup-suspensionᵉ {Xᵉ = Xᵉ} Bᵉ =
  is-equiv-htpy-equiv'ᵉ
    ( ( equiv-dependent-suspension-structure-suspension-coconeᵉ
        ( suspension-structure-suspensionᵉ Xᵉ)
        ( Bᵉ)) ∘eᵉ
      ( equiv-dup-pushoutᵉ (terminal-mapᵉ Xᵉ) (terminal-mapᵉ Xᵉ) Bᵉ))
    ( triangle-dependent-ev-suspensionᵉ (suspension-structure-suspensionᵉ Xᵉ) Bᵉ)

equiv-dup-suspensionᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Bᵉ : suspensionᵉ Xᵉ → UUᵉ l2ᵉ) →
  ( (xᵉ : suspensionᵉ Xᵉ) → Bᵉ xᵉ) ≃ᵉ
  ( dependent-suspension-structureᵉ Bᵉ (suspension-structure-suspensionᵉ Xᵉ))
pr1ᵉ (equiv-dup-suspensionᵉ {Xᵉ = Xᵉ} Bᵉ) =
  dependent-ev-suspensionᵉ (suspension-structure-suspensionᵉ Xᵉ) Bᵉ
pr2ᵉ (equiv-dup-suspensionᵉ Bᵉ) = dup-suspensionᵉ Bᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Bᵉ : suspensionᵉ Xᵉ → UUᵉ l2ᵉ)
  where

  dependent-cogap-suspensionᵉ :
    dependent-suspension-structureᵉ Bᵉ (suspension-structure-suspensionᵉ Xᵉ) →
    (xᵉ : suspensionᵉ Xᵉ) → Bᵉ xᵉ
  dependent-cogap-suspensionᵉ = map-inv-is-equivᵉ (dup-suspensionᵉ Bᵉ)

  is-section-dependent-cogap-suspensionᵉ :
    ( ( dependent-ev-suspensionᵉ (suspension-structure-suspensionᵉ Xᵉ) Bᵉ) ∘ᵉ
      ( dependent-cogap-suspensionᵉ)) ~ᵉ idᵉ
  is-section-dependent-cogap-suspensionᵉ =
    is-section-map-inv-is-equivᵉ (dup-suspensionᵉ Bᵉ)

  is-retraction-dependent-cogap-suspensionᵉ :
    ( ( dependent-cogap-suspensionᵉ) ∘ᵉ
      ( dependent-ev-suspensionᵉ (suspension-structure-suspensionᵉ Xᵉ) Bᵉ)) ~ᵉ idᵉ
  is-retraction-dependent-cogap-suspensionᵉ =
    is-retraction-map-inv-is-equivᵉ (dup-suspensionᵉ Bᵉ)

  dup-suspension-north-suspensionᵉ :
    (dᵉ :
      dependent-suspension-structureᵉ
        ( Bᵉ)
        ( suspension-structure-suspensionᵉ Xᵉ)) →
    ( dependent-cogap-suspensionᵉ dᵉ north-suspensionᵉ) ＝ᵉ
    ( north-dependent-suspension-structureᵉ dᵉ)
  dup-suspension-north-suspensionᵉ dᵉ =
    north-htpy-dependent-suspension-structureᵉ
      ( Bᵉ)
      ( htpy-eq-dependent-suspension-structureᵉ
        ( Bᵉ)
        ( is-section-dependent-cogap-suspensionᵉ dᵉ))

  dup-suspension-south-suspensionᵉ :
    (dᵉ :
      dependent-suspension-structureᵉ
        ( Bᵉ)
        ( suspension-structure-suspensionᵉ Xᵉ)) →
    ( dependent-cogap-suspensionᵉ dᵉ south-suspensionᵉ) ＝ᵉ
    ( south-dependent-suspension-structureᵉ dᵉ)
  dup-suspension-south-suspensionᵉ dᵉ =
    south-htpy-dependent-suspension-structureᵉ
      ( Bᵉ)
      ( htpy-eq-dependent-suspension-structureᵉ
        ( Bᵉ)
        ( is-section-dependent-cogap-suspensionᵉ dᵉ))

  dup-suspension-meridian-suspensionᵉ :
    (dᵉ :
      dependent-suspension-structureᵉ
        ( Bᵉ)
        ( suspension-structure-suspensionᵉ Xᵉ))
    (xᵉ : Xᵉ) →
    coherence-square-identificationsᵉ
      ( apᵉ
        ( trᵉ Bᵉ (meridian-suspensionᵉ xᵉ))
        ( dup-suspension-north-suspensionᵉ dᵉ))
      ( apdᵉ
        ( dependent-cogap-suspensionᵉ dᵉ)
        ( meridian-suspensionᵉ xᵉ))
      ( meridian-dependent-suspension-structureᵉ dᵉ xᵉ)
      ( dup-suspension-south-suspensionᵉ dᵉ)
  dup-suspension-meridian-suspensionᵉ dᵉ =
    meridian-htpy-dependent-suspension-structureᵉ
      ( Bᵉ)
      ( htpy-eq-dependent-suspension-structureᵉ
        ( Bᵉ)
        ( is-section-dependent-cogap-suspensionᵉ dᵉ))
```

### Characterization of homotopies between functions with domain a suspension

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) {Yᵉ : UUᵉ l2ᵉ}
  (fᵉ gᵉ : suspensionᵉ Xᵉ → Yᵉ)
  where

  htpy-function-out-of-suspensionᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-function-out-of-suspensionᵉ =
    htpy-suspension-structureᵉ
      ( ev-suspensionᵉ (suspension-structure-suspensionᵉ Xᵉ) Yᵉ fᵉ)
      ( ev-suspensionᵉ (suspension-structure-suspensionᵉ Xᵉ) Yᵉ gᵉ)

  north-htpy-function-out-of-suspensionᵉ :
    htpy-function-out-of-suspensionᵉ →
    fᵉ north-suspensionᵉ ＝ᵉ gᵉ north-suspensionᵉ
  north-htpy-function-out-of-suspensionᵉ = pr1ᵉ

  south-htpy-function-out-of-suspensionᵉ :
    htpy-function-out-of-suspensionᵉ →
    fᵉ south-suspensionᵉ ＝ᵉ gᵉ south-suspensionᵉ
  south-htpy-function-out-of-suspensionᵉ = pr1ᵉ ∘ᵉ pr2ᵉ

  meridian-htpy-function-out-of-suspensionᵉ :
    (hᵉ : htpy-function-out-of-suspensionᵉ) →
    (xᵉ : Xᵉ) →
    coherence-square-identificationsᵉ
      ( north-htpy-function-out-of-suspensionᵉ hᵉ)
      ( apᵉ fᵉ (meridian-suspensionᵉ xᵉ))
      ( apᵉ gᵉ (meridian-suspensionᵉ xᵉ))
      ( south-htpy-function-out-of-suspensionᵉ hᵉ)
  meridian-htpy-function-out-of-suspensionᵉ = pr2ᵉ ∘ᵉ pr2ᵉ

  equiv-htpy-function-out-of-suspension-dependent-suspension-structureᵉ :
    ( dependent-suspension-structureᵉ
      ( eq-valueᵉ fᵉ gᵉ)
      ( suspension-structure-suspensionᵉ Xᵉ)) ≃ᵉ
    ( htpy-function-out-of-suspensionᵉ)
  equiv-htpy-function-out-of-suspension-dependent-suspension-structureᵉ =
    ( equiv-totᵉ
      ( λ pᵉ →
        equiv-totᵉ
          ( λ qᵉ →
            equiv-Π-equiv-familyᵉ
              ( λ xᵉ →
                inv-equivᵉ
                  ( compute-dependent-identification-eq-value-functionᵉ
                    ( fᵉ)
                    ( gᵉ)
                    ( meridian-suspension-structureᵉ
                      ( suspension-structure-suspensionᵉ Xᵉ)
                      ( xᵉ))
                    ( pᵉ)
                    ( qᵉ))))))

  equiv-dependent-suspension-structure-htpy-function-out-of-suspensionᵉ :
    ( htpy-function-out-of-suspensionᵉ) ≃ᵉ
    ( dependent-suspension-structureᵉ
      ( eq-valueᵉ fᵉ gᵉ)
      ( suspension-structure-suspensionᵉ Xᵉ))
  equiv-dependent-suspension-structure-htpy-function-out-of-suspensionᵉ =
    ( equiv-totᵉ
      ( λ pᵉ →
        equiv-totᵉ
          ( λ qᵉ →
            equiv-Π-equiv-familyᵉ
              ( λ xᵉ →
                ( compute-dependent-identification-eq-value-functionᵉ
                  ( fᵉ)
                  ( gᵉ)
                  ( meridian-suspension-structureᵉ
                    ( suspension-structure-suspensionᵉ Xᵉ)
                    ( xᵉ))
                  ( pᵉ)
                  ( qᵉ))))))

  compute-inv-equiv-htpy-function-out-of-suspension-dependent-suspension-structureᵉ :
    htpy-equivᵉ
      ( inv-equivᵉ
        ( equiv-htpy-function-out-of-suspension-dependent-suspension-structureᵉ))
      ( equiv-dependent-suspension-structure-htpy-function-out-of-suspensionᵉ)
  compute-inv-equiv-htpy-function-out-of-suspension-dependent-suspension-structureᵉ =
    ( compute-inv-equiv-totᵉ
      ( λ pᵉ →
        equiv-totᵉ
          ( λ qᵉ →
            equiv-Π-equiv-familyᵉ
              ( λ xᵉ →
                inv-equivᵉ
                  ( compute-dependent-identification-eq-value-functionᵉ
                    ( fᵉ)
                    ( gᵉ)
                    ( meridian-suspension-structureᵉ
                      ( suspension-structure-suspensionᵉ Xᵉ)
                      ( xᵉ))
                    ( pᵉ)
                    ( qᵉ)))))) ∙hᵉ
    ( tot-htpyᵉ
      ( λ pᵉ →
        ( compute-inv-equiv-totᵉ
          ( λ qᵉ →
            equiv-Π-equiv-familyᵉ
              ( λ xᵉ →
                inv-equivᵉ
                  ( compute-dependent-identification-eq-value-functionᵉ
                    ( fᵉ)
                    ( gᵉ)
                    ( meridian-suspension-structureᵉ
                      ( suspension-structure-suspensionᵉ Xᵉ)
                      ( xᵉ))
                    ( pᵉ)
                    ( qᵉ))))) ∙hᵉ
        ( tot-htpyᵉ
          ( λ qᵉ →
            compute-inv-equiv-Π-equiv-familyᵉ
              ( λ xᵉ →
                inv-equivᵉ
                  ( compute-dependent-identification-eq-value-functionᵉ
                    ( fᵉ)
                    ( gᵉ)
                    ( meridian-suspension-structureᵉ
                      ( suspension-structure-suspensionᵉ Xᵉ)
                      ( xᵉ))
                    ( pᵉ)
                    ( qᵉ)))))))

  equiv-htpy-function-out-of-suspension-htpyᵉ :
    (fᵉ ~ᵉ gᵉ) ≃ᵉ htpy-function-out-of-suspensionᵉ
  equiv-htpy-function-out-of-suspension-htpyᵉ =
    ( equiv-htpy-function-out-of-suspension-dependent-suspension-structureᵉ) ∘eᵉ
    ( equiv-dup-suspensionᵉ (eq-valueᵉ fᵉ gᵉ))

  htpy-function-out-of-suspension-htpyᵉ :
    (fᵉ ~ᵉ gᵉ) → htpy-function-out-of-suspensionᵉ
  htpy-function-out-of-suspension-htpyᵉ =
    map-equivᵉ (equiv-htpy-function-out-of-suspension-htpyᵉ)

  equiv-htpy-htpy-function-out-of-suspensionᵉ :
    htpy-function-out-of-suspensionᵉ ≃ᵉ (fᵉ ~ᵉ gᵉ)
  equiv-htpy-htpy-function-out-of-suspensionᵉ =
    ( inv-equivᵉ (equiv-dup-suspensionᵉ (eq-valueᵉ fᵉ gᵉ))) ∘eᵉ
    ( equiv-dependent-suspension-structure-htpy-function-out-of-suspensionᵉ)

  htpy-htpy-function-out-of-suspensionᵉ :
    htpy-function-out-of-suspensionᵉ → (fᵉ ~ᵉ gᵉ)
  htpy-htpy-function-out-of-suspensionᵉ =
    map-equivᵉ equiv-htpy-htpy-function-out-of-suspensionᵉ

  compute-inv-equiv-htpy-function-out-of-suspension-htpyᵉ :
    htpy-equivᵉ
      ( inv-equivᵉ equiv-htpy-function-out-of-suspension-htpyᵉ)
      ( equiv-htpy-htpy-function-out-of-suspensionᵉ)
  compute-inv-equiv-htpy-function-out-of-suspension-htpyᵉ cᵉ =
    ( htpy-eq-equivᵉ
      ( distributive-inv-comp-equivᵉ
        ( equiv-dup-suspensionᵉ (eq-valueᵉ fᵉ gᵉ))
        ( equiv-htpy-function-out-of-suspension-dependent-suspension-structureᵉ))
      ( cᵉ)) ∙ᵉ
    ( apᵉ
      ( map-inv-equivᵉ (equiv-dup-suspensionᵉ (eq-value-functionᵉ fᵉ gᵉ)))
      ( compute-inv-equiv-htpy-function-out-of-suspension-dependent-suspension-structureᵉ
        ( cᵉ)))

  is-section-htpy-htpy-function-out-of-suspensionᵉ :
    ( ( htpy-function-out-of-suspension-htpyᵉ) ∘ᵉ
      ( htpy-htpy-function-out-of-suspensionᵉ)) ~ᵉ
    ( idᵉ)
  is-section-htpy-htpy-function-out-of-suspensionᵉ cᵉ =
    ( apᵉ
      ( htpy-function-out-of-suspension-htpyᵉ)
      ( invᵉ (compute-inv-equiv-htpy-function-out-of-suspension-htpyᵉ cᵉ))) ∙ᵉ
    ( is-section-map-inv-equivᵉ (equiv-htpy-function-out-of-suspension-htpyᵉ) cᵉ)

  equiv-htpy-function-out-of-suspension-htpy-north-suspensionᵉ :
    (cᵉ : htpy-function-out-of-suspensionᵉ) →
    ( htpy-htpy-function-out-of-suspensionᵉ cᵉ north-suspensionᵉ) ＝ᵉ
    ( north-htpy-function-out-of-suspensionᵉ cᵉ)
  equiv-htpy-function-out-of-suspension-htpy-north-suspensionᵉ cᵉ =
    north-htpy-in-htpy-suspension-structureᵉ
      ( htpy-eq-htpy-suspension-structureᵉ
        ( is-section-htpy-htpy-function-out-of-suspensionᵉ cᵉ))

  equiv-htpy-function-out-of-suspension-htpy-south-suspensionᵉ :
    (cᵉ : htpy-function-out-of-suspensionᵉ) →
    ( htpy-htpy-function-out-of-suspensionᵉ cᵉ south-suspensionᵉ) ＝ᵉ
    ( south-htpy-function-out-of-suspensionᵉ cᵉ)
  equiv-htpy-function-out-of-suspension-htpy-south-suspensionᵉ cᵉ =
    south-htpy-in-htpy-suspension-structureᵉ
      ( htpy-eq-htpy-suspension-structureᵉ
        ( is-section-htpy-htpy-function-out-of-suspensionᵉ cᵉ))
```

### The suspension of a contractible type is contractible

```agda
is-contr-suspension-is-contrᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → is-contrᵉ Xᵉ → is-contrᵉ (suspensionᵉ Xᵉ)
is-contr-suspension-is-contrᵉ {lᵉ} {Xᵉ} is-contr-Xᵉ =
  is-contr-is-equiv'ᵉ
    ( unitᵉ)
    ( pr1ᵉ (pr2ᵉ (cocone-suspensionᵉ Xᵉ)))
    ( is-equiv-universal-property-pushoutᵉ
      ( terminal-mapᵉ Xᵉ)
      ( terminal-mapᵉ Xᵉ)
      ( cocone-suspensionᵉ Xᵉ)
      ( is-equiv-is-contrᵉ (terminal-mapᵉ Xᵉ) is-contr-Xᵉ is-contr-unitᵉ)
      ( up-suspension'ᵉ Xᵉ))
    ( is-contr-unitᵉ)
```

### Suspensions increase connectedness

Moreᵉ precisely,ᵉ theᵉ suspensionᵉ ofᵉ aᵉ `k`-connectedᵉ typeᵉ isᵉ `(k+1)`-connected.ᵉ

Forᵉ theᵉ proofᵉ weᵉ useᵉ thatᵉ aᵉ typeᵉ `A`ᵉ isᵉ `n`-connectedᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ
constantᵉ mapᵉ `Bᵉ → (Aᵉ → B)`ᵉ isᵉ anᵉ equivalenceᵉ forᵉ allᵉ `n`-typesᵉ `B`.ᵉ

Soᵉ forᵉ anyᵉ `(k+1)`-typeᵉ `Y`,ᵉ weᵉ haveᵉ theᵉ commutativeᵉ diagramᵉ

```text
                 Δᵉ
     Yᵉ ---------------------->ᵉ  (suspensionᵉ Xᵉ → Yᵉ)
     ∧ᵉ                                  |
 pr1ᵉ | ≃ᵉ                              ≃ᵉ | ev-suspensionᵉ
     |                      ≃ᵉ           ∨ᵉ
  Σᵉ (yᵉ y'ᵉ : Yᵉ) ,ᵉ yᵉ ＝ᵉ y'ᵉ <-----ᵉ suspension-structureᵉ Yᵉ
                                ≐ᵉ Σᵉ (yᵉ y'ᵉ : Yᵉ) ,ᵉ Xᵉ → yᵉ ＝ᵉ y'ᵉ
```

where theᵉ bottomᵉ mapᵉ isᵉ inducedᵉ byᵉ theᵉ equivalenceᵉ `(yᵉ ＝ᵉ y'ᵉ) → (Xᵉ → (yᵉ ＝ᵉ y'))`ᵉ
givenᵉ byᵉ theᵉ factᵉ thatᵉ `X`ᵉ isᵉ `k`-connectedᵉ andᵉ `yᵉ ＝ᵉ y'`ᵉ isᵉ aᵉ `k`-type.ᵉ

Sinceᵉ theᵉ left,ᵉ bottomᵉ andᵉ rightᵉ mapsᵉ areᵉ equivalences,ᵉ soᵉ isᵉ theᵉ topᵉ map,ᵉ asᵉ
desired.ᵉ

```agda
module _
  {lᵉ : Level} {kᵉ : 𝕋ᵉ} {Xᵉ : UUᵉ lᵉ}
  where

  is-equiv-north-suspension-ev-suspension-is-connected-Truncated-Typeᵉ :
    is-connectedᵉ kᵉ Xᵉ →
    {l'ᵉ : Level} (Yᵉ : Truncated-Typeᵉ l'ᵉ (succ-𝕋ᵉ kᵉ)) →
    is-equivᵉ
      ( ( north-suspension-structureᵉ) ∘ᵉ
        ( ev-suspensionᵉ
          ( suspension-structure-suspensionᵉ Xᵉ)
          ( type-Truncated-Typeᵉ Yᵉ)))
  is-equiv-north-suspension-ev-suspension-is-connected-Truncated-Typeᵉ cᵉ Yᵉ =
    is-equiv-compᵉ
      ( north-suspension-structureᵉ)
      ( ev-suspensionᵉ
        ( suspension-structure-suspensionᵉ Xᵉ)
        ( type-Truncated-Typeᵉ Yᵉ))
      ( is-equiv-ev-suspensionᵉ
        ( suspension-structure-suspensionᵉ Xᵉ)
        ( up-suspension'ᵉ Xᵉ)
        ( type-Truncated-Typeᵉ Yᵉ))
      ( is-equiv-pr1-is-contrᵉ
        ( λ yᵉ →
          is-torsorial-fiber-Idᵉ
            ( λ y'ᵉ →
              ( diagonal-exponentialᵉ (yᵉ ＝ᵉ y'ᵉ) Xᵉ ,ᵉ
                is-equiv-diagonal-exponential-is-connectedᵉ
                  ( Id-Truncated-Typeᵉ Yᵉ yᵉ y'ᵉ)
                  ( cᵉ)))))

  is-connected-succ-suspension-is-connectedᵉ :
    is-connectedᵉ kᵉ Xᵉ → is-connectedᵉ (succ-𝕋ᵉ kᵉ) (suspensionᵉ Xᵉ)
  is-connected-succ-suspension-is-connectedᵉ cᵉ =
    is-connected-is-equiv-diagonal-exponentialᵉ
      ( λ Yᵉ →
        is-equiv-right-factorᵉ
          ( ( north-suspension-structureᵉ) ∘ᵉ
            ( ev-suspensionᵉ
              ( suspension-structure-suspensionᵉ Xᵉ)
              ( type-Truncated-Typeᵉ Yᵉ)))
          ( diagonal-exponentialᵉ (type-Truncated-Typeᵉ Yᵉ) (suspensionᵉ Xᵉ))
          ( is-equiv-north-suspension-ev-suspension-is-connected-Truncated-Typeᵉ
              ( cᵉ)
              ( Yᵉ))
          ( is-equiv-idᵉ))
```