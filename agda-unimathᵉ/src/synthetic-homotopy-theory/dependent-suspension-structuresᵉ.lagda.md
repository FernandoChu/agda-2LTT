# Dependent suspension structures

```agda
module synthetic-homotopy-theory.dependent-suspension-structuresᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.constant-mapsᵉ
open import foundation.dependent-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-unit-typeᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.dependent-cocones-under-spansᵉ
open import synthetic-homotopy-theory.suspension-structuresᵉ
```

</details>

## Idea

Thisᵉ isᵉ theᵉ dependentᵉ analogᵉ ofᵉ
[suspensionᵉ structures](synthetic-homotopy-theory.suspension-structures.md).ᵉ Theᵉ
relationᵉ betweenᵉ
[suspensionᵉ structures](synthetic-homotopy-theory.suspension-structures.mdᵉ) andᵉ
dependentᵉ suspensionᵉ structuresᵉ mirrorsᵉ theᵉ relationᵉ betweenᵉ
[coconesᵉ underᵉ aᵉ span](synthetic-homotopy-theory.cocones-under-spans.mdᵉ) andᵉ
[dependentᵉ coconesᵉ underᵉ aᵉ span](synthetic-homotopy-theory.dependent-cocones-under-spans.md).ᵉ

Fixᵉ aᵉ typeᵉ `X`ᵉ andᵉ considerᵉ aᵉ suspensionᵉ coconeᵉ `(fᵉ ,ᵉ gᵉ ,ᵉ h)`ᵉ with nadirᵉ `Y`.ᵉ
Givenᵉ aᵉ typeᵉ familyᵉ `Pᵉ : Yᵉ → UU`,ᵉ aᵉ dependentᵉ suspensionᵉ coconeᵉ onᵉ `P`ᵉ overᵉ
`(fᵉ ,ᵉ gᵉ ,ᵉ h)`ᵉ consistsᵉ ofᵉ dependentᵉ functionsᵉ

```text
northᵉ : (tᵉ : unitᵉ) → Pᵉ (fᵉ tᵉ)

southᵉ : (tᵉ : unitᵉ) → Pᵉ (gᵉ tᵉ)
```

togetherᵉ with aᵉ familyᵉ ofᵉ dependentᵉ identificationsᵉ

```text
meridᵉ : (xᵉ : Xᵉ) → dependent-identificationᵉ Pᵉ (hᵉ xᵉ) ((northᵉ ∘ᵉ (terminal-mapᵉ Xᵉ)) xᵉ) (southᵉ ∘ᵉ (terminal-mapᵉ Xᵉ) xᵉ)
```

Usingᵉ theᵉ [universalᵉ propertyᵉ ofᵉ `unit`](foundation.unit-type.mdᵉ) andᵉ theᵉ
previousᵉ characterizationᵉ ofᵉ suspensionᵉ coconesᵉ (toᵉ beᵉ foundᵉ in theᵉ fileᵉ
[synthetic-homotopy-theory.suspension-structures](synthetic-homotopy-theory.suspension-structures.md)),ᵉ
weᵉ canᵉ characterizeᵉ dependentᵉ coconesᵉ overᵉ aᵉ suspensionᵉ coconeᵉ asᵉ equivalentᵉ to
theᵉ followingᵉ:

Forᵉ aᵉ suspensionᵉ structureᵉ `(Nᵉ ,ᵉ Sᵉ ,ᵉ m)`,ᵉ aᵉ dependentᵉ suspensionᵉ structureᵉ in
`P`ᵉ overᵉ (Nᵉ ,ᵉ Sᵉ ,ᵉ m)`ᵉ isᵉ givenᵉ byᵉ pointsᵉ

```text
northᵉ : Pᵉ Nᵉ

southᵉ : Pᵉ Sᵉ
```

andᵉ aᵉ familyᵉ ofᵉ dependentᵉ identificationsᵉ

```text
meridianᵉ : (xᵉ : Xᵉ) → dependent-identificationᵉ Pᵉ (mᵉ xᵉ) northᵉ southᵉ
```

## Definition

### Dependent Suspension Cocones

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (Bᵉ : Yᵉ → UUᵉ l3ᵉ)
  (cᵉ : suspension-coconeᵉ Xᵉ Yᵉ)
  where

  dependent-suspension-coconeᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  dependent-suspension-coconeᵉ =
    dependent-coconeᵉ
      ( terminal-mapᵉ Xᵉ)
      ( terminal-mapᵉ Xᵉ)
      ( cᵉ)
      ( Bᵉ)
```

### Dependent Suspension Structures

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  (Bᵉ : Yᵉ → UUᵉ l3ᵉ)
  (cᵉ : suspension-structureᵉ Xᵉ Yᵉ)
  where

  dependent-suspension-structureᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  dependent-suspension-structureᵉ =
    Σᵉ ( Bᵉ (north-suspension-structureᵉ cᵉ))
      ( λ Nᵉ →
        Σᵉ ( Bᵉ (south-suspension-structureᵉ cᵉ))
          ( λ Sᵉ →
            (xᵉ : Xᵉ) →
            dependent-identificationᵉ
              ( Bᵉ)
              ( meridian-suspension-structureᵉ cᵉ xᵉ)
              ( Nᵉ)
              ( Sᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Bᵉ : Yᵉ → UUᵉ l3ᵉ}
  {cᵉ : suspension-structureᵉ Xᵉ Yᵉ}
  (dᵉ : dependent-suspension-structureᵉ Bᵉ cᵉ)
  where

  north-dependent-suspension-structureᵉ : Bᵉ (north-suspension-structureᵉ cᵉ)
  north-dependent-suspension-structureᵉ = pr1ᵉ (dᵉ)

  south-dependent-suspension-structureᵉ : Bᵉ (south-suspension-structureᵉ cᵉ)
  south-dependent-suspension-structureᵉ = (pr1ᵉ ∘ᵉ pr2ᵉ) (dᵉ)

  meridian-dependent-suspension-structureᵉ :
    (xᵉ : Xᵉ) →
    dependent-identificationᵉ
      ( Bᵉ)
      ( meridian-suspension-structureᵉ cᵉ xᵉ)
      ( north-dependent-suspension-structureᵉ)
      ( south-dependent-suspension-structureᵉ)
  meridian-dependent-suspension-structureᵉ = (pr2ᵉ ∘ᵉ pr2ᵉ) (dᵉ)
```

## Properties

#### Equivalence between dependent suspension structures and dependent suspension cocones

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (cᵉ : suspension-structureᵉ Xᵉ Yᵉ)
  (Bᵉ : Yᵉ → UUᵉ l3ᵉ)
  where

  dependent-cocone-dependent-suspension-structureᵉ :
    dependent-suspension-structureᵉ Bᵉ cᵉ →
    dependent-suspension-coconeᵉ Bᵉ (suspension-cocone-suspension-structureᵉ cᵉ)
  pr1ᵉ (dependent-cocone-dependent-suspension-structureᵉ dᵉ) tᵉ =
    north-dependent-suspension-structureᵉ dᵉ
  pr1ᵉ (pr2ᵉ (dependent-cocone-dependent-suspension-structureᵉ dᵉ)) tᵉ =
    south-dependent-suspension-structureᵉ dᵉ
  pr2ᵉ (pr2ᵉ (dependent-cocone-dependent-suspension-structureᵉ dᵉ)) xᵉ =
    meridian-dependent-suspension-structureᵉ dᵉ xᵉ

  equiv-dependent-suspension-structure-suspension-coconeᵉ :
    ( dependent-suspension-coconeᵉ
      ( Bᵉ)
      ( suspension-cocone-suspension-structureᵉ cᵉ)) ≃ᵉ
    ( dependent-suspension-structureᵉ Bᵉ cᵉ)
  equiv-dependent-suspension-structure-suspension-coconeᵉ =
    ( equiv-Σᵉ
      ( λ nᵉ →
        Σᵉ ( Bᵉ (south-suspension-structureᵉ cᵉ))
          ( λ sᵉ →
            (xᵉ : Xᵉ) →
            ( dependent-identificationᵉ
              ( Bᵉ)
              ( meridian-suspension-structureᵉ cᵉ xᵉ)
              ( nᵉ)
              ( sᵉ))))
      ( equiv-dependent-universal-property-unitᵉ
        ( λ xᵉ → Bᵉ (north-suspension-structureᵉ cᵉ)))
      ( λ north-suspension-cᵉ →
        ( equiv-Σᵉ
          ( λ sᵉ →
            (xᵉ : Xᵉ) →
            ( dependent-identificationᵉ
              ( Bᵉ)
              ( meridian-suspension-structureᵉ cᵉ xᵉ)
              ( map-equivᵉ
                ( equiv-dependent-universal-property-unitᵉ
                  ( λ _ → Bᵉ (north-suspension-structureᵉ cᵉ)))
                ( north-suspension-cᵉ))
              ( sᵉ)))
          ( equiv-dependent-universal-property-unitᵉ
            ( pointᵉ (Bᵉ (south-suspension-structureᵉ cᵉ))))
          ( λ south-suspension-cᵉ → id-equivᵉ))))

  htpy-map-inv-equiv-dependent-suspension-structure-suspension-cocone-cocone-dependent-cocone-dependent-suspension-structureᵉ :
    map-inv-equivᵉ equiv-dependent-suspension-structure-suspension-coconeᵉ ~ᵉ
    dependent-cocone-dependent-suspension-structureᵉ
  htpy-map-inv-equiv-dependent-suspension-structure-suspension-cocone-cocone-dependent-cocone-dependent-suspension-structureᵉ
    ( dᵉ) =
      is-injective-equivᵉ
        ( equiv-dependent-suspension-structure-suspension-coconeᵉ)
        ( is-section-map-inv-equivᵉ
          ( equiv-dependent-suspension-structure-suspension-coconeᵉ)
          ( dᵉ))
```

#### Characterizing equality of dependent suspension structures

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (Bᵉ : Yᵉ → UUᵉ l3ᵉ)
  {cᵉ : suspension-structureᵉ Xᵉ Yᵉ}
  (dᵉ d'ᵉ : dependent-suspension-structureᵉ Bᵉ cᵉ)
  where

  htpy-dependent-suspension-structureᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  htpy-dependent-suspension-structureᵉ =
    Σᵉ ( north-dependent-suspension-structureᵉ dᵉ ＝ᵉ
        north-dependent-suspension-structureᵉ d'ᵉ)
      ( λ N-htpyᵉ →
        Σᵉ ( south-dependent-suspension-structureᵉ dᵉ ＝ᵉ
            south-dependent-suspension-structureᵉ d'ᵉ)
          ( λ S-htpyᵉ →
            (xᵉ : Xᵉ) →
            coherence-square-identificationsᵉ
              ( apᵉ
                ( trᵉ Bᵉ (meridian-suspension-structureᵉ cᵉ xᵉ))
                ( N-htpyᵉ))
              ( meridian-dependent-suspension-structureᵉ dᵉ xᵉ)
              ( meridian-dependent-suspension-structureᵉ d'ᵉ xᵉ)
              ( S-htpyᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (Bᵉ : Yᵉ → UUᵉ l3ᵉ)
  {susp-strᵉ : suspension-structureᵉ Xᵉ Yᵉ}
  {d-susp-str0ᵉ d-susp-str1ᵉ : dependent-suspension-structureᵉ Bᵉ susp-strᵉ}
  where

  north-htpy-dependent-suspension-structureᵉ :
    htpy-dependent-suspension-structureᵉ Bᵉ d-susp-str0ᵉ d-susp-str1ᵉ →
    north-dependent-suspension-structureᵉ d-susp-str0ᵉ ＝ᵉ
    north-dependent-suspension-structureᵉ d-susp-str1ᵉ
  north-htpy-dependent-suspension-structureᵉ = pr1ᵉ

  south-htpy-dependent-suspension-structureᵉ :
    htpy-dependent-suspension-structureᵉ Bᵉ d-susp-str0ᵉ d-susp-str1ᵉ →
    south-dependent-suspension-structureᵉ d-susp-str0ᵉ ＝ᵉ
    south-dependent-suspension-structureᵉ d-susp-str1ᵉ
  south-htpy-dependent-suspension-structureᵉ = (pr1ᵉ ∘ᵉ pr2ᵉ)

  meridian-htpy-dependent-suspension-structureᵉ :
    ( d-susp-strᵉ :
      htpy-dependent-suspension-structureᵉ Bᵉ d-susp-str0ᵉ d-susp-str1ᵉ) →
    ( xᵉ : Xᵉ) →
    coherence-square-identificationsᵉ
      ( apᵉ
        ( trᵉ Bᵉ (meridian-suspension-structureᵉ susp-strᵉ xᵉ))
        ( north-htpy-dependent-suspension-structureᵉ d-susp-strᵉ))
      ( meridian-dependent-suspension-structureᵉ d-susp-str0ᵉ xᵉ)
      ( meridian-dependent-suspension-structureᵉ d-susp-str1ᵉ xᵉ)
      ( south-htpy-dependent-suspension-structureᵉ d-susp-strᵉ)
  meridian-htpy-dependent-suspension-structureᵉ = pr2ᵉ ∘ᵉ pr2ᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (Bᵉ : Yᵉ → UUᵉ l3ᵉ)
  {cᵉ : suspension-structureᵉ Xᵉ Yᵉ}
  (dᵉ : dependent-suspension-structureᵉ Bᵉ cᵉ)
  where

  extensionality-dependent-suspension-structureᵉ :
    ( d'ᵉ : dependent-suspension-structureᵉ Bᵉ cᵉ) →
    ( dᵉ ＝ᵉ d'ᵉ) ≃ᵉ
    ( htpy-dependent-suspension-structureᵉ Bᵉ dᵉ d'ᵉ)
  extensionality-dependent-suspension-structureᵉ =
    extensionality-Σᵉ
      ( λ (Sᵉ ,ᵉ mᵉ) (N-htpyᵉ) →
        Σᵉ (south-dependent-suspension-structureᵉ dᵉ ＝ᵉ Sᵉ)
          ( λ S-htpyᵉ →
            (xᵉ : Xᵉ) →
            coherence-square-identificationsᵉ
              ( apᵉ (trᵉ Bᵉ (meridian-suspension-structureᵉ cᵉ xᵉ)) N-htpyᵉ)
              ( meridian-dependent-suspension-structureᵉ dᵉ xᵉ)
              ( mᵉ xᵉ)
              ( S-htpyᵉ)))
      ( reflᵉ)
      ( reflᵉ ,ᵉ λ xᵉ → right-unitᵉ)
      ( λ Nᵉ → id-equivᵉ)
      ( extensionality-Σᵉ
        ( λ mᵉ S-htpyᵉ →
          (xᵉ : Xᵉ) →
          ( meridian-dependent-suspension-structureᵉ dᵉ xᵉ ∙ᵉ S-htpyᵉ) ＝ᵉ
          ( mᵉ xᵉ))
        ( reflᵉ)
        ( λ xᵉ → right-unitᵉ)
        ( λ Sᵉ → id-equivᵉ)
        ( λ mᵉ →
          equiv-concat-htpyᵉ right-unit-htpyᵉ mᵉ ∘eᵉ inv-equivᵉ equiv-eq-htpyᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (Bᵉ : Yᵉ → UUᵉ l3ᵉ)
  {cᵉ : suspension-structureᵉ Xᵉ Yᵉ}
  {dᵉ d'ᵉ : dependent-suspension-structureᵉ Bᵉ cᵉ}
  where

  htpy-eq-dependent-suspension-structureᵉ :
    (dᵉ ＝ᵉ d'ᵉ) →
    htpy-dependent-suspension-structureᵉ Bᵉ dᵉ d'ᵉ
  htpy-eq-dependent-suspension-structureᵉ =
    map-equivᵉ
      ( extensionality-dependent-suspension-structureᵉ Bᵉ dᵉ d'ᵉ)

  eq-htpy-dependent-suspension-structureᵉ :
    htpy-dependent-suspension-structureᵉ Bᵉ dᵉ d'ᵉ →
    dᵉ ＝ᵉ d'ᵉ
  eq-htpy-dependent-suspension-structureᵉ =
    map-inv-equivᵉ
      ( extensionality-dependent-suspension-structureᵉ Bᵉ dᵉ d'ᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (Bᵉ : Yᵉ → UUᵉ l3ᵉ)
  {cᵉ : suspension-structureᵉ Xᵉ Yᵉ}
  (dᵉ : dependent-suspension-structureᵉ Bᵉ cᵉ)
  where

  refl-htpy-dependent-suspension-structureᵉ :
    htpy-dependent-suspension-structureᵉ Bᵉ dᵉ dᵉ
  pr1ᵉ refl-htpy-dependent-suspension-structureᵉ = reflᵉ
  pr1ᵉ (pr2ᵉ refl-htpy-dependent-suspension-structureᵉ) = reflᵉ
  pr2ᵉ (pr2ᵉ refl-htpy-dependent-suspension-structureᵉ) xᵉ = right-unitᵉ

  is-refl-refl-htpy-dependent-suspension-structureᵉ :
    refl-htpy-dependent-suspension-structureᵉ ＝ᵉ
    htpy-eq-dependent-suspension-structureᵉ Bᵉ reflᵉ
  is-refl-refl-htpy-dependent-suspension-structureᵉ = reflᵉ
```