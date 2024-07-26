# Dependent sums of pullbacks

```agda
module foundation.dependent-sums-pullbacksᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.families-of-equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.pullbacksᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.universal-property-pullbacksᵉ
```

</details>

## Properties

### Computing the standard pullback of a dependent sum

Squaresᵉ ofᵉ theᵉ formᵉ

```text
  Σᵉ (xᵉ : Aᵉ) (Qᵉ (fᵉ xᵉ)) ---->ᵉ Σᵉ (yᵉ : Bᵉ) Qᵉ
      |                          |
      |                          |
  pr1ᵉ |                          | pr1ᵉ
      |                          |
      ∨ᵉ                          ∨ᵉ
      Aᵉ ----------------------->ᵉ Bᵉ
                   fᵉ
```

areᵉ pullbacks.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Qᵉ : Bᵉ → UUᵉ l3ᵉ)
  where

  standard-pullback-Σᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  standard-pullback-Σᵉ = Σᵉ Aᵉ (λ xᵉ → Qᵉ (fᵉ xᵉ))

  cone-standard-pullback-Σᵉ : coneᵉ fᵉ pr1ᵉ standard-pullback-Σᵉ
  pr1ᵉ cone-standard-pullback-Σᵉ = pr1ᵉ
  pr1ᵉ (pr2ᵉ cone-standard-pullback-Σᵉ) = map-Σ-map-baseᵉ fᵉ Qᵉ
  pr2ᵉ (pr2ᵉ cone-standard-pullback-Σᵉ) = refl-htpyᵉ

  inv-gap-cone-standard-pullback-Σᵉ :
    standard-pullbackᵉ fᵉ (pr1ᵉ {Bᵉ = Qᵉ}) → standard-pullback-Σᵉ
  pr1ᵉ (inv-gap-cone-standard-pullback-Σᵉ (xᵉ ,ᵉ _)) = xᵉ
  pr2ᵉ (inv-gap-cone-standard-pullback-Σᵉ (xᵉ ,ᵉ (.(fᵉ xᵉ) ,ᵉ qᵉ) ,ᵉ reflᵉ)) = qᵉ

  abstract
    is-section-inv-gap-cone-standard-pullback-Σᵉ :
      is-sectionᵉ
        ( gapᵉ fᵉ pr1ᵉ cone-standard-pullback-Σᵉ)
        ( inv-gap-cone-standard-pullback-Σᵉ)
    is-section-inv-gap-cone-standard-pullback-Σᵉ (xᵉ ,ᵉ (.(fᵉ xᵉ) ,ᵉ qᵉ) ,ᵉ reflᵉ) = reflᵉ

  abstract
    is-retraction-inv-gap-cone-standard-pullback-Σᵉ :
      is-retractionᵉ
        ( gapᵉ fᵉ pr1ᵉ cone-standard-pullback-Σᵉ)
        ( inv-gap-cone-standard-pullback-Σᵉ)
    is-retraction-inv-gap-cone-standard-pullback-Σᵉ = refl-htpyᵉ

  abstract
    is-pullback-cone-standard-pullback-Σᵉ :
      is-pullbackᵉ fᵉ pr1ᵉ cone-standard-pullback-Σᵉ
    is-pullback-cone-standard-pullback-Σᵉ =
      is-equiv-is-invertibleᵉ
        inv-gap-cone-standard-pullback-Σᵉ
        is-section-inv-gap-cone-standard-pullback-Σᵉ
        is-retraction-inv-gap-cone-standard-pullback-Σᵉ

  compute-standard-pullback-Σᵉ :
    standard-pullback-Σᵉ ≃ᵉ standard-pullbackᵉ fᵉ pr1ᵉ
  pr1ᵉ compute-standard-pullback-Σᵉ = gapᵉ fᵉ pr1ᵉ cone-standard-pullback-Σᵉ
  pr2ᵉ compute-standard-pullback-Σᵉ = is-pullback-cone-standard-pullback-Σᵉ
```

### A family of maps over a base map induces a pullback square if and only if it is a family of equivalences

Givenᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ with aᵉ familyᵉ ofᵉ mapsᵉ overᵉ itᵉ
`gᵉ : (xᵉ : Aᵉ) → Pᵉ xᵉ → Qᵉ (fᵉ x)`,ᵉ thenᵉ theᵉ squareᵉ

```text
         map-Σᵉ fᵉ gᵉ
  Σᵉ Aᵉ Pᵉ ---------->ᵉ Σᵉ Bᵉ Qᵉ
    |                |
    |                |
    ∨ᵉ                ∨ᵉ
    Aᵉ ------------->ᵉ Bᵉ
             fᵉ
```

isᵉ aᵉ pullbackᵉ ifᵉ andᵉ onlyᵉ ifᵉ `g`ᵉ isᵉ aᵉ
[fiberwiseᵉ equivalence](foundation-core.families-of-equivalences.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Pᵉ : Aᵉ → UUᵉ l3ᵉ}
  (Qᵉ : Bᵉ → UUᵉ l4ᵉ) (fᵉ : Aᵉ → Bᵉ) (gᵉ : (xᵉ : Aᵉ) → Pᵉ xᵉ → Qᵉ (fᵉ xᵉ))
  where

  cone-map-Σᵉ : coneᵉ fᵉ pr1ᵉ (Σᵉ Aᵉ Pᵉ)
  pr1ᵉ cone-map-Σᵉ = pr1ᵉ
  pr1ᵉ (pr2ᵉ cone-map-Σᵉ) = map-Σᵉ Qᵉ fᵉ gᵉ
  pr2ᵉ (pr2ᵉ cone-map-Σᵉ) = refl-htpyᵉ

  abstract
    is-pullback-is-fiberwise-equivᵉ :
      is-fiberwise-equivᵉ gᵉ → is-pullbackᵉ fᵉ pr1ᵉ cone-map-Σᵉ
    is-pullback-is-fiberwise-equivᵉ is-equiv-gᵉ =
      is-equiv-compᵉ
        ( gapᵉ fᵉ pr1ᵉ (cone-standard-pullback-Σᵉ fᵉ Qᵉ))
        ( totᵉ gᵉ)
        ( is-equiv-tot-is-fiberwise-equivᵉ is-equiv-gᵉ)
        ( is-pullback-cone-standard-pullback-Σᵉ fᵉ Qᵉ)

  abstract
    universal-property-pullback-is-fiberwise-equivᵉ :
      is-fiberwise-equivᵉ gᵉ →
      universal-property-pullbackᵉ fᵉ pr1ᵉ cone-map-Σᵉ
    universal-property-pullback-is-fiberwise-equivᵉ is-equiv-gᵉ =
      universal-property-pullback-is-pullbackᵉ fᵉ pr1ᵉ
        ( cone-map-Σᵉ)
        ( is-pullback-is-fiberwise-equivᵉ is-equiv-gᵉ)

  abstract
    is-fiberwise-equiv-is-pullbackᵉ :
      is-pullbackᵉ fᵉ pr1ᵉ cone-map-Σᵉ → is-fiberwise-equivᵉ gᵉ
    is-fiberwise-equiv-is-pullbackᵉ is-pullback-cone-map-Σᵉ =
      is-fiberwise-equiv-is-equiv-totᵉ
        ( is-equiv-right-factorᵉ
          ( gapᵉ fᵉ pr1ᵉ (cone-standard-pullback-Σᵉ fᵉ Qᵉ))
          ( totᵉ gᵉ)
          ( is-pullback-cone-standard-pullback-Σᵉ fᵉ Qᵉ)
          ( is-pullback-cone-map-Σᵉ))

  abstract
    is-fiberwise-equiv-universal-property-pullbackᵉ :
      ( universal-property-pullbackᵉ fᵉ pr1ᵉ cone-map-Σᵉ) →
      is-fiberwise-equivᵉ gᵉ
    is-fiberwise-equiv-universal-property-pullbackᵉ upᵉ =
      is-fiberwise-equiv-is-pullbackᵉ
        ( is-pullback-universal-property-pullbackᵉ fᵉ pr1ᵉ cone-map-Σᵉ upᵉ)
```

### Pullbacks are preserved by dependent sums

#### A family of squares over a pullback square is a family of pullback squares if and only if the total square is a pullback

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level}
  {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (PXᵉ : Xᵉ → UUᵉ l5ᵉ) {PAᵉ : Aᵉ → UUᵉ l6ᵉ} {PBᵉ : Bᵉ → UUᵉ l7ᵉ} {PCᵉ : Cᵉ → UUᵉ l8ᵉ}
  {fᵉ : Aᵉ → Xᵉ} {gᵉ : Bᵉ → Xᵉ}
  (f'ᵉ : (aᵉ : Aᵉ) → PAᵉ aᵉ → PXᵉ (fᵉ aᵉ)) (g'ᵉ : (bᵉ : Bᵉ) → PBᵉ bᵉ → PXᵉ (gᵉ bᵉ))
  (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : cone-familyᵉ PXᵉ f'ᵉ g'ᵉ cᵉ PCᵉ)
  where

  tot-cone-cone-familyᵉ :
    coneᵉ (map-Σᵉ PXᵉ fᵉ f'ᵉ) (map-Σᵉ PXᵉ gᵉ g'ᵉ) (Σᵉ Cᵉ PCᵉ)
  pr1ᵉ tot-cone-cone-familyᵉ =
    map-Σᵉ _ (vertical-map-coneᵉ fᵉ gᵉ cᵉ) (λ xᵉ → pr1ᵉ (c'ᵉ xᵉ))
  pr1ᵉ (pr2ᵉ tot-cone-cone-familyᵉ) =
    map-Σᵉ _ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) (λ xᵉ → (pr1ᵉ (pr2ᵉ (c'ᵉ xᵉ))))
  pr2ᵉ (pr2ᵉ tot-cone-cone-familyᵉ) =
    htpy-map-Σᵉ PXᵉ
      ( coherence-square-coneᵉ fᵉ gᵉ cᵉ)
      ( λ zᵉ →
        ( f'ᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ zᵉ)) ∘ᵉ
        ( vertical-map-coneᵉ
          ( ( trᵉ PXᵉ (coherence-square-coneᵉ fᵉ gᵉ cᵉ zᵉ)) ∘ᵉ
            ( f'ᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ zᵉ)))
          ( g'ᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ zᵉ))
          ( c'ᵉ zᵉ)))
      ( λ zᵉ →
        coherence-square-coneᵉ
          ( ( trᵉ PXᵉ (coherence-square-coneᵉ fᵉ gᵉ cᵉ zᵉ)) ∘ᵉ
            ( f'ᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ zᵉ)))
          ( g'ᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ zᵉ))
          ( c'ᵉ zᵉ))

  map-standard-pullback-tot-cone-cone-fam-right-factorᵉ :
    Σᵉ ( standard-pullbackᵉ fᵉ gᵉ)
      ( λ tᵉ →
        standard-pullbackᵉ
          ( trᵉ PXᵉ (coherence-square-standard-pullbackᵉ tᵉ) ∘ᵉ
            f'ᵉ (vertical-map-standard-pullbackᵉ tᵉ))
          ( g'ᵉ (horizontal-map-standard-pullbackᵉ tᵉ))) →
    Σᵉ ( Σᵉ Aᵉ PAᵉ)
      ( λ aa'ᵉ → Σᵉ (Σᵉ Bᵉ (λ bᵉ → fᵉ (pr1ᵉ aa'ᵉ) ＝ᵉ gᵉ bᵉ))
        ( λ bαᵉ → Σᵉ (PBᵉ (pr1ᵉ bαᵉ))
          ( λ b'ᵉ → trᵉ PXᵉ (pr2ᵉ bαᵉ) (f'ᵉ (pr1ᵉ aa'ᵉ) (pr2ᵉ aa'ᵉ)) ＝ᵉ g'ᵉ (pr1ᵉ bαᵉ) b'ᵉ)))
  map-standard-pullback-tot-cone-cone-fam-right-factorᵉ =
    map-interchange-Σ-Σᵉ
      ( λ aᵉ bαᵉ a'ᵉ →
        Σᵉ ( PBᵉ (pr1ᵉ bαᵉ))
          ( λ b'ᵉ → trᵉ PXᵉ (pr2ᵉ bαᵉ) (f'ᵉ aᵉ a'ᵉ) ＝ᵉ g'ᵉ (pr1ᵉ bαᵉ) b'ᵉ))

  map-standard-pullback-tot-cone-cone-fam-left-factorᵉ :
    (aa'ᵉ : Σᵉ Aᵉ PAᵉ) →
    Σᵉ (Σᵉ Bᵉ (λ bᵉ → fᵉ (pr1ᵉ aa'ᵉ) ＝ᵉ gᵉ bᵉ))
      ( λ bαᵉ →
        Σᵉ ( PBᵉ (pr1ᵉ bαᵉ))
          ( λ b'ᵉ → trᵉ PXᵉ (pr2ᵉ bαᵉ) (f'ᵉ (pr1ᵉ aa'ᵉ) (pr2ᵉ aa'ᵉ)) ＝ᵉ g'ᵉ (pr1ᵉ bαᵉ) b'ᵉ)) →
    Σᵉ ( Σᵉ Bᵉ PBᵉ)
      ( λ bb'ᵉ → Σᵉ (fᵉ (pr1ᵉ aa'ᵉ) ＝ᵉ gᵉ (pr1ᵉ bb'ᵉ))
        ( λ αᵉ → trᵉ PXᵉ αᵉ (f'ᵉ (pr1ᵉ aa'ᵉ) (pr2ᵉ aa'ᵉ)) ＝ᵉ g'ᵉ (pr1ᵉ bb'ᵉ) (pr2ᵉ bb'ᵉ)))
  map-standard-pullback-tot-cone-cone-fam-left-factorᵉ aa'ᵉ =
    ( map-interchange-Σ-Σᵉ
      ( λ bᵉ αᵉ b'ᵉ → trᵉ PXᵉ αᵉ (f'ᵉ (pr1ᵉ aa'ᵉ) (pr2ᵉ aa'ᵉ)) ＝ᵉ g'ᵉ bᵉ b'ᵉ))

  map-standard-pullback-tot-cone-cone-familyᵉ :
    Σᵉ ( standard-pullbackᵉ fᵉ gᵉ)
      ( λ tᵉ →
        standard-pullbackᵉ
          ( ( trᵉ PXᵉ (coherence-square-standard-pullbackᵉ tᵉ)) ∘ᵉ
            ( f'ᵉ (vertical-map-standard-pullbackᵉ tᵉ)))
          ( g'ᵉ (horizontal-map-standard-pullbackᵉ tᵉ))) →
    standard-pullbackᵉ (map-Σᵉ PXᵉ fᵉ f'ᵉ) (map-Σᵉ PXᵉ gᵉ g'ᵉ)
  map-standard-pullback-tot-cone-cone-familyᵉ =
    ( totᵉ
      (λ aa'ᵉ →
        ( totᵉ (λ bb'ᵉ → eq-pair-Σ'ᵉ)) ∘ᵉ
        ( map-standard-pullback-tot-cone-cone-fam-left-factorᵉ aa'ᵉ))) ∘ᵉ
    ( map-standard-pullback-tot-cone-cone-fam-right-factorᵉ)

  is-equiv-map-standard-pullback-tot-cone-cone-familyᵉ :
    is-equivᵉ map-standard-pullback-tot-cone-cone-familyᵉ
  is-equiv-map-standard-pullback-tot-cone-cone-familyᵉ =
    is-equiv-compᵉ
      ( totᵉ
        ( λ aa'ᵉ →
          ( totᵉ (λ bb'ᵉ → eq-pair-Σ'ᵉ)) ∘ᵉ
          ( map-standard-pullback-tot-cone-cone-fam-left-factorᵉ aa'ᵉ)))
      ( map-standard-pullback-tot-cone-cone-fam-right-factorᵉ)
      ( is-equiv-map-interchange-Σ-Σᵉ
        ( λ aᵉ bαᵉ a'ᵉ → Σᵉ (PBᵉ (pr1ᵉ bαᵉ))
          ( λ b'ᵉ → trᵉ PXᵉ (pr2ᵉ bαᵉ) (f'ᵉ aᵉ a'ᵉ) ＝ᵉ g'ᵉ (pr1ᵉ bαᵉ) b'ᵉ)))
      ( is-equiv-tot-is-fiberwise-equivᵉ
        ( λ aa'ᵉ →
          is-equiv-compᵉ
            ( totᵉ (λ bb'ᵉ → eq-pair-Σ'ᵉ))
            ( map-standard-pullback-tot-cone-cone-fam-left-factorᵉ aa'ᵉ)
            ( is-equiv-map-interchange-Σ-Σᵉ _)
            ( is-equiv-tot-is-fiberwise-equivᵉ
              ( λ bb'ᵉ →
                is-equiv-eq-pair-Σᵉ
                  ( fᵉ (pr1ᵉ aa'ᵉ) ,ᵉ f'ᵉ (pr1ᵉ aa'ᵉ) (pr2ᵉ aa'ᵉ))
                  ( gᵉ (pr1ᵉ bb'ᵉ) ,ᵉ g'ᵉ (pr1ᵉ bb'ᵉ) (pr2ᵉ bb'ᵉ))))))

  triangle-standard-pullback-tot-cone-cone-familyᵉ :
    ( gapᵉ (map-Σᵉ PXᵉ fᵉ f'ᵉ) (map-Σᵉ PXᵉ gᵉ g'ᵉ) tot-cone-cone-familyᵉ) ~ᵉ
    ( ( map-standard-pullback-tot-cone-cone-familyᵉ) ∘ᵉ
      ( map-Σᵉ _
        ( gapᵉ fᵉ gᵉ cᵉ)
        ( λ xᵉ → gapᵉ
          ( ( trᵉ PXᵉ (coherence-square-coneᵉ fᵉ gᵉ cᵉ xᵉ)) ∘ᵉ
            ( f'ᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ)))
          ( g'ᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ xᵉ))
          ( c'ᵉ xᵉ))))
  triangle-standard-pullback-tot-cone-cone-familyᵉ = refl-htpyᵉ

  is-pullback-family-is-pullback-totᵉ :
    is-pullbackᵉ fᵉ gᵉ cᵉ →
    is-pullbackᵉ
      (map-Σᵉ PXᵉ fᵉ f'ᵉ) (map-Σᵉ PXᵉ gᵉ g'ᵉ) tot-cone-cone-familyᵉ →
    (xᵉ : Cᵉ) →
    is-pullbackᵉ
      ( ( trᵉ PXᵉ (coherence-square-coneᵉ fᵉ gᵉ cᵉ xᵉ)) ∘ᵉ
        ( f'ᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ)))
      ( g'ᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ xᵉ))
      ( c'ᵉ xᵉ)
  is-pullback-family-is-pullback-totᵉ is-pb-cᵉ is-pb-totᵉ =
    is-fiberwise-equiv-is-equiv-map-Σᵉ _
      ( gapᵉ fᵉ gᵉ cᵉ)
      ( λ xᵉ →
        gapᵉ
          ( ( trᵉ PXᵉ (coherence-square-coneᵉ fᵉ gᵉ cᵉ xᵉ)) ∘ᵉ
            ( f'ᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ)))
          ( g'ᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ xᵉ))
          ( c'ᵉ xᵉ))
      ( is-pb-cᵉ)
      ( is-equiv-top-map-triangleᵉ
        ( gapᵉ (map-Σᵉ PXᵉ fᵉ f'ᵉ) (map-Σᵉ PXᵉ gᵉ g'ᵉ) tot-cone-cone-familyᵉ)
        ( map-standard-pullback-tot-cone-cone-familyᵉ)
        ( map-Σᵉ _
          ( gapᵉ fᵉ gᵉ cᵉ)
          ( λ xᵉ →
            gapᵉ
              ( ( trᵉ PXᵉ (coherence-square-coneᵉ fᵉ gᵉ cᵉ xᵉ)) ∘ᵉ
                ( f'ᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ)))
              ( g'ᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ xᵉ))
              ( c'ᵉ xᵉ)))
        ( triangle-standard-pullback-tot-cone-cone-familyᵉ)
        ( is-equiv-map-standard-pullback-tot-cone-cone-familyᵉ)
        ( is-pb-totᵉ))

  is-pullback-tot-is-pullback-familyᵉ :
    is-pullbackᵉ fᵉ gᵉ cᵉ →
    ( (xᵉ : Cᵉ) →
      is-pullbackᵉ
        ( ( trᵉ PXᵉ (coherence-square-coneᵉ fᵉ gᵉ cᵉ xᵉ)) ∘ᵉ
          ( f'ᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ)))
        ( g'ᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ xᵉ))
        ( c'ᵉ xᵉ)) →
    is-pullbackᵉ
      (map-Σᵉ PXᵉ fᵉ f'ᵉ) (map-Σᵉ PXᵉ gᵉ g'ᵉ) tot-cone-cone-familyᵉ
  is-pullback-tot-is-pullback-familyᵉ is-pb-cᵉ is-pb-c'ᵉ =
    is-equiv-left-map-triangleᵉ
      ( gapᵉ (map-Σᵉ PXᵉ fᵉ f'ᵉ) (map-Σᵉ PXᵉ gᵉ g'ᵉ) tot-cone-cone-familyᵉ)
      ( map-standard-pullback-tot-cone-cone-familyᵉ)
      ( map-Σᵉ _
        ( gapᵉ fᵉ gᵉ cᵉ)
        ( λ xᵉ → gapᵉ
          ( ( trᵉ PXᵉ (coherence-square-coneᵉ fᵉ gᵉ cᵉ xᵉ)) ∘ᵉ
            ( f'ᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ)))
          ( g'ᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ xᵉ))
          ( c'ᵉ xᵉ)))
      ( triangle-standard-pullback-tot-cone-cone-familyᵉ)
      ( is-equiv-map-Σᵉ _ is-pb-cᵉ is-pb-c'ᵉ)
      ( is-equiv-map-standard-pullback-tot-cone-cone-familyᵉ)
```

#### A family of squares is a family of pullback squares if and only if the total square is a pullback

Asᵉ aᵉ corollaryᵉ ofᵉ theᵉ previousᵉ result,ᵉ aᵉ dependentᵉ sumᵉ ofᵉ squaresᵉ overᵉ theᵉ
constantᵉ diagramᵉ isᵉ aᵉ pullbackᵉ squareᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ familyᵉ isᵉ aᵉ familyᵉ ofᵉ
pullbackᵉ squares.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Iᵉ : UUᵉ l5ᵉ} {Aᵉ : Iᵉ → UUᵉ l1ᵉ} {Bᵉ : Iᵉ → UUᵉ l2ᵉ} {Xᵉ : Iᵉ → UUᵉ l3ᵉ} {Yᵉ : Iᵉ → UUᵉ l4ᵉ}
  (fᵉ : (iᵉ : Iᵉ) → Bᵉ iᵉ → Yᵉ iᵉ) (gᵉ : (iᵉ : Iᵉ) → Xᵉ iᵉ → Yᵉ iᵉ)
  (cᵉ : (iᵉ : Iᵉ) → coneᵉ (fᵉ iᵉ) (gᵉ iᵉ) (Aᵉ iᵉ))
  where

  tot-coneᵉ : coneᵉ (totᵉ fᵉ) (totᵉ gᵉ) (Σᵉ Iᵉ Aᵉ)
  pr1ᵉ tot-coneᵉ = totᵉ (λ iᵉ → vertical-map-coneᵉ (fᵉ iᵉ) (gᵉ iᵉ) (cᵉ iᵉ))
  pr1ᵉ (pr2ᵉ tot-coneᵉ) = totᵉ (λ iᵉ → horizontal-map-coneᵉ (fᵉ iᵉ) (gᵉ iᵉ) (cᵉ iᵉ))
  pr2ᵉ (pr2ᵉ tot-coneᵉ) = tot-htpyᵉ (λ iᵉ → coherence-square-coneᵉ (fᵉ iᵉ) (gᵉ iᵉ) (cᵉ iᵉ))

  is-pullback-tot-is-pullback-family-id-coneᵉ :
    ((iᵉ : Iᵉ) → is-pullbackᵉ (fᵉ iᵉ) (gᵉ iᵉ) (cᵉ iᵉ)) →
    is-pullbackᵉ (totᵉ fᵉ) (totᵉ gᵉ) tot-coneᵉ
  is-pullback-tot-is-pullback-family-id-coneᵉ =
    is-pullback-tot-is-pullback-familyᵉ Yᵉ fᵉ gᵉ
      ( id-coneᵉ Iᵉ)
      ( cᵉ)
      ( is-pullback-is-equiv-vertical-mapsᵉ idᵉ idᵉ
        ( id-coneᵉ Iᵉ)
        ( is-equiv-idᵉ)
        ( is-equiv-idᵉ))

  is-pullback-family-id-cone-is-pullback-totᵉ :
    is-pullbackᵉ (totᵉ fᵉ) (totᵉ gᵉ) tot-coneᵉ →
    (iᵉ : Iᵉ) → is-pullbackᵉ (fᵉ iᵉ) (gᵉ iᵉ) (cᵉ iᵉ)
  is-pullback-family-id-cone-is-pullback-totᵉ =
    is-pullback-family-is-pullback-totᵉ Yᵉ fᵉ gᵉ
      ( id-coneᵉ Iᵉ)
      ( cᵉ)
      ( is-pullback-is-equiv-vertical-mapsᵉ idᵉ idᵉ
        ( id-coneᵉ Iᵉ)
        ( is-equiv-idᵉ)
        ( is-equiv-idᵉ))
```

## Table of files about pullbacks

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ pullbacksᵉ asᵉ aᵉ generalᵉ concept.ᵉ

{{#includeᵉ tables/pullbacks.mdᵉ}}