# Suspension Structures

```agda
module synthetic-homotopy-theory.suspension-structuresᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.constant-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-systemsᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
```

</details>

## Idea

Theᵉ suspensionᵉ ofᵉ `X`ᵉ isᵉ theᵉ [pushout](synthetic-homotopy-theory.pushouts.mdᵉ) ofᵉ
theᵉ spanᵉ `unitᵉ <--ᵉ Xᵉ -->ᵉ unit`.ᵉ Aᵉ
[coconeᵉ underᵉ suchᵉ aᵉ span](synthetic-homotopy-theory.dependent-cocones-under-spans.mdᵉ)
isᵉ calledᵉ aᵉ `suspension-cocone`.ᵉ Explicitly,ᵉ aᵉ suspensionᵉ coconeᵉ with nadirᵉ `Y`ᵉ
consistsᵉ ofᵉ functionsᵉ

```text
fᵉ : unitᵉ → Yᵉ
gᵉ : unitᵉ → Yᵉ
```

andᵉ aᵉ homotopyᵉ

```text
hᵉ : (xᵉ : Xᵉ) → (fᵉ ∘ᵉ (terminal-mapᵉ Xᵉ)) xᵉ ＝ᵉ (gᵉ ∘ᵉ (terminal-mapᵉ Xᵉ)) xᵉ
```

Usingᵉ theᵉ
[universalᵉ propertyᵉ ofᵉ theᵉ unitᵉ type](foundation.universal-property-unit-type.md),ᵉ
weᵉ canᵉ characterizeᵉ suspensionᵉ coconesᵉ asᵉ equivalentᵉ to aᵉ selectionᵉ ofᵉ "north"ᵉ
andᵉ "south"ᵉ polesᵉ

```text
northᵉ ,ᵉ southᵉ : Yᵉ
```

andᵉ aᵉ meridianᵉ functionᵉ

```text
meridianᵉ : Xᵉ → northᵉ ＝ᵉ southᵉ
```

Weᵉ callᵉ thisᵉ typeᵉ ofᵉ structureᵉ `suspension-structure`.ᵉ

## Definition

### Suspension cocones on a type

```agda
suspension-coconeᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Yᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
suspension-coconeᵉ Xᵉ Yᵉ = coconeᵉ (terminal-mapᵉ Xᵉ) (terminal-mapᵉ Xᵉ) Yᵉ
```

### Suspension structures on a type

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Yᵉ : UUᵉ l2ᵉ)
  where

  suspension-structureᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  suspension-structureᵉ = Σᵉ Yᵉ (λ Nᵉ → Σᵉ Yᵉ (λ Sᵉ → (xᵉ : Xᵉ) → Nᵉ ＝ᵉ Sᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  where

  north-suspension-structureᵉ : suspension-structureᵉ Xᵉ Yᵉ → Yᵉ
  north-suspension-structureᵉ cᵉ = pr1ᵉ cᵉ

  south-suspension-structureᵉ : suspension-structureᵉ Xᵉ Yᵉ → Yᵉ
  south-suspension-structureᵉ cᵉ = (pr1ᵉ ∘ᵉ pr2ᵉ) cᵉ

  meridian-suspension-structureᵉ :
    (cᵉ : suspension-structureᵉ Xᵉ Yᵉ) →
    Xᵉ → north-suspension-structureᵉ cᵉ ＝ᵉ south-suspension-structureᵉ cᵉ
  meridian-suspension-structureᵉ cᵉ = (pr2ᵉ ∘ᵉ pr2ᵉ) cᵉ
```

## Properties

### Equivalence between suspension structures and suspension cocones

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  where

  suspension-cocone-suspension-structureᵉ :
    suspension-structureᵉ Xᵉ Yᵉ → suspension-coconeᵉ Xᵉ Yᵉ
  pr1ᵉ (suspension-cocone-suspension-structureᵉ (Nᵉ ,ᵉ Sᵉ ,ᵉ meridᵉ)) = pointᵉ Nᵉ
  pr1ᵉ (pr2ᵉ (suspension-cocone-suspension-structureᵉ (Nᵉ ,ᵉ Sᵉ ,ᵉ meridᵉ))) = pointᵉ Sᵉ
  pr2ᵉ (pr2ᵉ (suspension-cocone-suspension-structureᵉ (Nᵉ ,ᵉ Sᵉ ,ᵉ meridᵉ))) = meridᵉ

  suspension-structure-suspension-coconeᵉ :
    suspension-coconeᵉ Xᵉ Yᵉ → suspension-structureᵉ Xᵉ Yᵉ
  pr1ᵉ (suspension-structure-suspension-coconeᵉ (Nᵉ ,ᵉ Sᵉ ,ᵉ meridᵉ)) = Nᵉ starᵉ
  pr1ᵉ (pr2ᵉ (suspension-structure-suspension-coconeᵉ (Nᵉ ,ᵉ Sᵉ ,ᵉ meridᵉ))) = Sᵉ starᵉ
  pr2ᵉ (pr2ᵉ (suspension-structure-suspension-coconeᵉ (Nᵉ ,ᵉ Sᵉ ,ᵉ meridᵉ))) = meridᵉ

  is-equiv-suspension-cocone-suspension-structureᵉ :
    is-equivᵉ suspension-cocone-suspension-structureᵉ
  is-equiv-suspension-cocone-suspension-structureᵉ =
    is-equiv-is-invertibleᵉ
      ( suspension-structure-suspension-coconeᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)

  is-equiv-suspension-structure-suspension-coconeᵉ :
    is-equivᵉ suspension-structure-suspension-coconeᵉ
  is-equiv-suspension-structure-suspension-coconeᵉ =
    is-equiv-is-invertibleᵉ
      ( suspension-cocone-suspension-structureᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)

  equiv-suspension-structure-suspension-coconeᵉ :
    suspension-structureᵉ Xᵉ Yᵉ ≃ᵉ suspension-coconeᵉ Xᵉ Yᵉ
  pr1ᵉ equiv-suspension-structure-suspension-coconeᵉ =
    suspension-cocone-suspension-structureᵉ
  pr2ᵉ equiv-suspension-structure-suspension-coconeᵉ =
    is-equiv-suspension-cocone-suspension-structureᵉ

  equiv-suspension-cocone-suspension-structureᵉ :
    suspension-coconeᵉ Xᵉ Yᵉ ≃ᵉ suspension-structureᵉ Xᵉ Yᵉ
  pr1ᵉ equiv-suspension-cocone-suspension-structureᵉ =
    suspension-structure-suspension-coconeᵉ
  pr2ᵉ equiv-suspension-cocone-suspension-structureᵉ =
    is-equiv-suspension-structure-suspension-coconeᵉ
```

#### Characterization of equalities in `suspension-structure`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Zᵉ : UUᵉ l2ᵉ}
  where

  htpy-suspension-structureᵉ :
    (cᵉ c'ᵉ : suspension-structureᵉ Xᵉ Zᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-suspension-structureᵉ cᵉ c'ᵉ =
    Σᵉ ( north-suspension-structureᵉ cᵉ ＝ᵉ north-suspension-structureᵉ c'ᵉ)
      ( λ pᵉ →
        Σᵉ ( south-suspension-structureᵉ cᵉ ＝ᵉ south-suspension-structureᵉ c'ᵉ)
          ( λ qᵉ →
            ( xᵉ : Xᵉ) →
            ( meridian-suspension-structureᵉ cᵉ xᵉ ∙ᵉ qᵉ) ＝ᵉ
            ( pᵉ ∙ᵉ meridian-suspension-structureᵉ c'ᵉ xᵉ)))

  north-htpy-suspension-structureᵉ :
    {cᵉ c'ᵉ : suspension-structureᵉ Xᵉ Zᵉ} →
    htpy-suspension-structureᵉ cᵉ c'ᵉ →
    north-suspension-structureᵉ cᵉ ＝ᵉ north-suspension-structureᵉ c'ᵉ
  north-htpy-suspension-structureᵉ = pr1ᵉ

  south-htpy-suspension-structureᵉ :
    {cᵉ c'ᵉ : suspension-structureᵉ Xᵉ Zᵉ} →
    htpy-suspension-structureᵉ cᵉ c'ᵉ →
    south-suspension-structureᵉ cᵉ ＝ᵉ south-suspension-structureᵉ c'ᵉ
  south-htpy-suspension-structureᵉ = pr1ᵉ ∘ᵉ pr2ᵉ

  meridian-htpy-suspension-structureᵉ :
    {cᵉ c'ᵉ : suspension-structureᵉ Xᵉ Zᵉ} →
    (hᵉ : htpy-suspension-structureᵉ cᵉ c'ᵉ) →
    ( xᵉ : Xᵉ) →
    coherence-square-identificationsᵉ
      ( north-htpy-suspension-structureᵉ hᵉ)
      ( meridian-suspension-structureᵉ cᵉ xᵉ)
      ( meridian-suspension-structureᵉ c'ᵉ xᵉ)
      ( south-htpy-suspension-structureᵉ hᵉ)
  meridian-htpy-suspension-structureᵉ = pr2ᵉ ∘ᵉ pr2ᵉ

  extensionality-suspension-structureᵉ :
    (cᵉ c'ᵉ : suspension-structureᵉ Xᵉ Zᵉ) →
    (cᵉ ＝ᵉ c'ᵉ) ≃ᵉ (htpy-suspension-structureᵉ cᵉ c'ᵉ)
  extensionality-suspension-structureᵉ (Nᵉ ,ᵉ Sᵉ ,ᵉ meridᵉ) =
    extensionality-Σᵉ
      ( λ yᵉ pᵉ →
        Σᵉ (Sᵉ ＝ᵉ pr1ᵉ yᵉ) (λ qᵉ → (xᵉ : Xᵉ) → (meridᵉ xᵉ ∙ᵉ qᵉ) ＝ᵉ (pᵉ ∙ᵉ pr2ᵉ yᵉ xᵉ)))
      ( reflᵉ)
      ( reflᵉ ,ᵉ right-unit-htpyᵉ)
      ( λ zᵉ → id-equivᵉ)
      ( extensionality-Σᵉ
        ( λ Hᵉ qᵉ → (xᵉ : Xᵉ) → (meridᵉ xᵉ ∙ᵉ qᵉ) ＝ᵉ Hᵉ xᵉ)
        ( reflᵉ)
        ( right-unit-htpyᵉ)
        ( λ zᵉ → id-equivᵉ)
        ( λ Hᵉ → equiv-concat-htpyᵉ right-unit-htpyᵉ Hᵉ ∘eᵉ equiv-funextᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Zᵉ : UUᵉ l2ᵉ} {cᵉ c'ᵉ : suspension-structureᵉ Xᵉ Zᵉ}
  where

  htpy-eq-suspension-structureᵉ : (cᵉ ＝ᵉ c'ᵉ) → htpy-suspension-structureᵉ cᵉ c'ᵉ
  htpy-eq-suspension-structureᵉ =
    map-equivᵉ (extensionality-suspension-structureᵉ cᵉ c'ᵉ)

  eq-htpy-suspension-structureᵉ : htpy-suspension-structureᵉ cᵉ c'ᵉ → (cᵉ ＝ᵉ c'ᵉ)
  eq-htpy-suspension-structureᵉ =
    map-inv-equivᵉ (extensionality-suspension-structureᵉ cᵉ c'ᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Zᵉ : UUᵉ l2ᵉ} {cᵉ : suspension-structureᵉ Xᵉ Zᵉ}
  where

  refl-htpy-suspension-structureᵉ : htpy-suspension-structureᵉ cᵉ cᵉ
  pr1ᵉ refl-htpy-suspension-structureᵉ = reflᵉ
  pr1ᵉ (pr2ᵉ refl-htpy-suspension-structureᵉ) = reflᵉ
  pr2ᵉ (pr2ᵉ refl-htpy-suspension-structureᵉ) = right-unit-htpyᵉ

  is-refl-refl-htpy-suspension-structureᵉ :
    refl-htpy-suspension-structureᵉ ＝ᵉ htpy-eq-suspension-structureᵉ reflᵉ
  is-refl-refl-htpy-suspension-structureᵉ = reflᵉ

  extensionality-suspension-structure-refl-htpy-suspension-structureᵉ :
    eq-htpy-suspension-structureᵉ refl-htpy-suspension-structureᵉ ＝ᵉ reflᵉ
  extensionality-suspension-structure-refl-htpy-suspension-structureᵉ =
    is-injective-equivᵉ
      ( extensionality-suspension-structureᵉ cᵉ cᵉ)
      ( is-section-map-inv-equivᵉ
        ( extensionality-suspension-structureᵉ cᵉ cᵉ)
        ( refl-htpy-suspension-structureᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Zᵉ : UUᵉ l2ᵉ} {cᵉ : suspension-structureᵉ Xᵉ Zᵉ}
  where

  ind-htpy-suspension-structureᵉ :
    { lᵉ : Level}
    ( Pᵉ :
      (c'ᵉ : suspension-structureᵉ Xᵉ Zᵉ) → htpy-suspension-structureᵉ cᵉ c'ᵉ → UUᵉ lᵉ) →
    ( Pᵉ cᵉ refl-htpy-suspension-structureᵉ) →
    ( c'ᵉ : suspension-structureᵉ Xᵉ Zᵉ)
    ( Hᵉ : htpy-suspension-structureᵉ cᵉ c'ᵉ) →
    Pᵉ c'ᵉ Hᵉ
  ind-htpy-suspension-structureᵉ Pᵉ =
    pr1ᵉ
      ( is-identity-system-is-torsorialᵉ
        ( cᵉ)
        ( refl-htpy-suspension-structureᵉ)
        ( is-contr-equivᵉ
          ( Σᵉ (suspension-structureᵉ Xᵉ Zᵉ) (λ c'ᵉ → cᵉ ＝ᵉ c'ᵉ))
          ( inv-equivᵉ
            ( equiv-totᵉ (extensionality-suspension-structureᵉ cᵉ)))
          ( is-torsorial-Idᵉ cᵉ))
        ( Pᵉ))
```

#### The action of paths of the projections have the expected effect

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Zᵉ : UUᵉ l2ᵉ} (cᵉ : suspension-structureᵉ Xᵉ Zᵉ)
  where

  ap-pr1-eq-htpy-suspension-structureᵉ :
    (c'ᵉ : suspension-structureᵉ Xᵉ Zᵉ) (Hᵉ : htpy-suspension-structureᵉ cᵉ c'ᵉ) →
    (apᵉ (pr1ᵉ) (eq-htpy-suspension-structureᵉ Hᵉ)) ＝ᵉ (pr1ᵉ Hᵉ)
  ap-pr1-eq-htpy-suspension-structureᵉ =
    ind-htpy-suspension-structureᵉ
      ( λ c'ᵉ Hᵉ → (apᵉ (pr1ᵉ) (eq-htpy-suspension-structureᵉ Hᵉ)) ＝ᵉ (pr1ᵉ Hᵉ))
      ( apᵉ
        ( apᵉ pr1ᵉ)
        ( is-retraction-map-inv-equivᵉ
          ( extensionality-suspension-structureᵉ cᵉ cᵉ)
          ( reflᵉ)))

  ap-pr1∘pr2-eq-htpy-suspension-structureᵉ :
    (c'ᵉ : suspension-structureᵉ Xᵉ Zᵉ) (Hᵉ : htpy-suspension-structureᵉ cᵉ c'ᵉ) →
    (apᵉ (pr1ᵉ ∘ᵉ pr2ᵉ) (eq-htpy-suspension-structureᵉ Hᵉ)) ＝ᵉ ((pr1ᵉ ∘ᵉ pr2ᵉ) Hᵉ)
  ap-pr1∘pr2-eq-htpy-suspension-structureᵉ =
    ind-htpy-suspension-structureᵉ
      ( λ c'ᵉ Hᵉ →
        apᵉ (pr1ᵉ ∘ᵉ pr2ᵉ) (eq-htpy-suspension-structureᵉ Hᵉ) ＝ᵉ (pr1ᵉ ∘ᵉ pr2ᵉ) Hᵉ)
      ( apᵉ
        ( apᵉ (pr1ᵉ ∘ᵉ pr2ᵉ))
        ( is-retraction-map-inv-equivᵉ
          ( extensionality-suspension-structureᵉ cᵉ cᵉ)
          ( reflᵉ)))
```

### Characterization of equalities in `htpy-suspension-structure`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Zᵉ : UUᵉ l2ᵉ}
  {cᵉ c'ᵉ : suspension-structureᵉ Xᵉ Zᵉ}
  where

  htpy-in-htpy-suspension-structureᵉ :
    htpy-suspension-structureᵉ cᵉ c'ᵉ →
    htpy-suspension-structureᵉ cᵉ c'ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-in-htpy-suspension-structureᵉ (nᵉ ,ᵉ sᵉ ,ᵉ hᵉ) (n'ᵉ ,ᵉ s'ᵉ ,ᵉ h'ᵉ) =
    Σᵉ ( nᵉ ＝ᵉ n'ᵉ)
      ( λ pᵉ →
        Σᵉ ( sᵉ ＝ᵉ s'ᵉ)
          ( λ qᵉ →
            (xᵉ : Xᵉ) →
            coherence-square-identificationsᵉ
              ( hᵉ xᵉ)
              ( left-whisker-concatᵉ
                ( meridian-suspension-structureᵉ cᵉ xᵉ)
                ( qᵉ))
              ( right-whisker-concatᵉ
                ( pᵉ)
                ( meridian-suspension-structureᵉ c'ᵉ xᵉ))
              ( h'ᵉ xᵉ)))

  extensionality-htpy-suspension-structureᵉ :
    (hᵉ h'ᵉ : htpy-suspension-structureᵉ cᵉ c'ᵉ) →
      (hᵉ ＝ᵉ h'ᵉ) ≃ᵉ htpy-in-htpy-suspension-structureᵉ hᵉ h'ᵉ
  extensionality-htpy-suspension-structureᵉ (nᵉ ,ᵉ sᵉ ,ᵉ hᵉ) =
    extensionality-Σᵉ
      ( λ yᵉ pᵉ →
        Σᵉ ( sᵉ ＝ᵉ pr1ᵉ yᵉ)
          ( λ qᵉ →
            (xᵉ : Xᵉ) →
            coherence-square-identificationsᵉ
              ( hᵉ xᵉ)
              ( left-whisker-concatᵉ
                ( meridian-suspension-structureᵉ cᵉ xᵉ)
                ( qᵉ))
              ( right-whisker-concatᵉ
                ( pᵉ)
                ( meridian-suspension-structureᵉ c'ᵉ xᵉ))
              ( pr2ᵉ yᵉ xᵉ)))
      ( reflᵉ)
      ( reflᵉ ,ᵉ inv-htpyᵉ right-unit-htpyᵉ)
      ( λ n'ᵉ → id-equivᵉ)
      ( extensionality-Σᵉ
        ( λ h'ᵉ qᵉ →
          (xᵉ : Xᵉ) →
          coherence-square-identificationsᵉ
            ( hᵉ xᵉ)
            ( left-whisker-concatᵉ (meridian-suspension-structureᵉ cᵉ xᵉ) qᵉ)
            ( right-whisker-concatᵉ
              ( reflᵉ)
              ( meridian-suspension-structureᵉ c'ᵉ xᵉ))
            ( h'ᵉ xᵉ))
        ( reflᵉ)
        ( inv-htpyᵉ right-unit-htpyᵉ)
        ( λ qᵉ → id-equivᵉ)
        ( λ h'ᵉ →
          ( inv-equivᵉ (equiv-concat-htpy'ᵉ h'ᵉ (right-unit-htpyᵉ))) ∘eᵉ
          ( equiv-inv-htpyᵉ hᵉ h'ᵉ) ∘eᵉ
          ( equiv-funextᵉ {fᵉ = hᵉ} {gᵉ = h'ᵉ})))

  north-htpy-in-htpy-suspension-structureᵉ :
    {hᵉ h'ᵉ : htpy-suspension-structureᵉ cᵉ c'ᵉ} →
    htpy-in-htpy-suspension-structureᵉ hᵉ h'ᵉ →
    ( north-htpy-suspension-structureᵉ hᵉ) ＝ᵉ
    ( north-htpy-suspension-structureᵉ h'ᵉ)
  north-htpy-in-htpy-suspension-structureᵉ = pr1ᵉ

  south-htpy-in-htpy-suspension-structureᵉ :
    {hᵉ h'ᵉ : htpy-suspension-structureᵉ cᵉ c'ᵉ} →
    htpy-in-htpy-suspension-structureᵉ hᵉ h'ᵉ →
    ( south-htpy-suspension-structureᵉ hᵉ) ＝ᵉ
    ( south-htpy-suspension-structureᵉ h'ᵉ)
  south-htpy-in-htpy-suspension-structureᵉ = pr1ᵉ ∘ᵉ pr2ᵉ

  meridian-htpy-in-htpy-suspension-structureᵉ :
    {hᵉ h'ᵉ : htpy-suspension-structureᵉ cᵉ c'ᵉ} →
    (Hᵉ : htpy-in-htpy-suspension-structureᵉ hᵉ h'ᵉ) →
    (xᵉ : Xᵉ) →
      coherence-square-identificationsᵉ
        ( meridian-htpy-suspension-structureᵉ hᵉ xᵉ)
        ( left-whisker-concatᵉ
          ( meridian-suspension-structureᵉ cᵉ xᵉ)
          ( south-htpy-in-htpy-suspension-structureᵉ Hᵉ))
        ( right-whisker-concatᵉ
          ( north-htpy-in-htpy-suspension-structureᵉ Hᵉ)
          ( meridian-suspension-structureᵉ c'ᵉ xᵉ))
        ( meridian-htpy-suspension-structureᵉ h'ᵉ xᵉ)
  meridian-htpy-in-htpy-suspension-structureᵉ = pr2ᵉ ∘ᵉ pr2ᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Zᵉ : UUᵉ l2ᵉ}
  {cᵉ c'ᵉ : suspension-structureᵉ Xᵉ Zᵉ} {hᵉ h'ᵉ : htpy-suspension-structureᵉ cᵉ c'ᵉ}
  where

  htpy-eq-htpy-suspension-structureᵉ :
    hᵉ ＝ᵉ h'ᵉ → htpy-in-htpy-suspension-structureᵉ hᵉ h'ᵉ
  htpy-eq-htpy-suspension-structureᵉ =
    map-equivᵉ (extensionality-htpy-suspension-structureᵉ hᵉ h'ᵉ)

  eq-htpy-in-htpy-suspension-structureᵉ :
    htpy-in-htpy-suspension-structureᵉ hᵉ h'ᵉ → hᵉ ＝ᵉ h'ᵉ
  eq-htpy-in-htpy-suspension-structureᵉ =
    map-inv-equivᵉ (extensionality-htpy-suspension-structureᵉ hᵉ h'ᵉ)
```