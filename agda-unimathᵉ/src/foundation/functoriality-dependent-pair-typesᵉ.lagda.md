# Functoriality of dependent pair types

```agda
module foundation.functoriality-dependent-pair-typesᵉ where

open import foundation-core.functoriality-dependent-pair-typesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-homotopiesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.contractible-mapsᵉ
open import foundation-core.dependent-identificationsᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.transport-along-identificationsᵉ
open import foundation-core.truncated-mapsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Properties

### The map `htpy-map-Σ` preserves homotopies

Givenᵉ aᵉ [homotopy](foundation.homotopies.mdᵉ) `Hᵉ : fᵉ ~ᵉ f'`ᵉ andᵉ aᵉ familyᵉ ofᵉ
[dependentᵉ homotopies](foundation.dependent-homotopies.mdᵉ) `Kᵉ aᵉ : gᵉ aᵉ ~ᵉ g'ᵉ a`ᵉ
overᵉ `H`,ᵉ expressedᵉ asᵉ
[commutingᵉ triangles](foundation.commuting-triangles-of-maps.mdᵉ)

```text
        gᵉ aᵉ
   Cᵉ aᵉ ----->ᵉ Dᵉ (fᵉ aᵉ)
      \ᵉ      /ᵉ
  g'ᵉ aᵉ \ᵉ    /ᵉ trᵉ Dᵉ (Hᵉ aᵉ)
        ∨ᵉ  ∨ᵉ
      Dᵉ (f'ᵉ aᵉ)         ,ᵉ
```

weᵉ getᵉ aᵉ homotopyᵉ `htpy-map-Σᵉ Hᵉ Kᵉ : map-Σᵉ fᵉ gᵉ ~ᵉ map-Σᵉ f'ᵉ g'`.ᵉ

Thisᵉ assignmentᵉ itselfᵉ preservesᵉ homotopiesᵉ: givenᵉ `H`ᵉ andᵉ `K`ᵉ asᵉ above,ᵉ
`H'ᵉ : fᵉ ~ᵉ f'`ᵉ with `K'ᵉ aᵉ : gᵉ aᵉ ~ᵉ g'ᵉ a`ᵉ overᵉ `H'`,ᵉ weᵉ wouldᵉ likeᵉ to expressᵉ
coherencesᵉ betweenᵉ theᵉ pairsᵉ `H,ᵉ H'`ᵉ andᵉ `K,ᵉ K'`ᵉ whichᵉ wouldᵉ ensureᵉ
`htpy-map-Σᵉ Hᵉ Kᵉ ~ᵉ htpy-map-Σᵉ H'ᵉ K'`.ᵉ Becauseᵉ `H`ᵉ andᵉ `H'`ᵉ haveᵉ theᵉ sameᵉ type,ᵉ weᵉ
mayᵉ requireᵉ aᵉ homotopyᵉ `αᵉ : Hᵉ ~ᵉ H'`,ᵉ butᵉ `K`ᵉ andᵉ `K'`ᵉ areᵉ familiesᵉ ofᵉ dependentᵉ
homotopiesᵉ overᵉ differentᵉ homotopies,ᵉ soᵉ theirᵉ coherenceᵉ isᵉ providedᵉ asᵉ aᵉ familyᵉ
ofᵉ
[commutingᵉ trianglesᵉ ofᵉ identifications](foundation.commuting-triangles-of-identifications.mdᵉ)

```text
                      apᵉ (λ pᵉ → trᵉ Dᵉ pᵉ (gᵉ aᵉ cᵉ)) (αᵉ aᵉ)
  trᵉ Dᵉ (Hᵉ aᵉ) (gᵉ aᵉ cᵉ) ---------------------------------ᵉ trᵉ Dᵉ (H'ᵉ aᵉ) (gᵉ aᵉ cᵉ)
                     \ᵉ                               /ᵉ
                        \ᵉ                         /ᵉ
                           \ᵉ                   /ᵉ
                      Kᵉ aᵉ cᵉ   \ᵉ             /ᵉ   K'ᵉ aᵉ cᵉ
                                 \ᵉ       /ᵉ
                                    \ᵉ /ᵉ
                                  g'ᵉ aᵉ cᵉ        .ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ} (Dᵉ : Bᵉ → UUᵉ l4ᵉ)
  {fᵉ f'ᵉ : Aᵉ → Bᵉ} {Hᵉ H'ᵉ : fᵉ ~ᵉ f'ᵉ}
  {gᵉ : (aᵉ : Aᵉ) → Cᵉ aᵉ → Dᵉ (fᵉ aᵉ)}
  {g'ᵉ : (aᵉ : Aᵉ) → Cᵉ aᵉ → Dᵉ (f'ᵉ aᵉ)}
  {Kᵉ : (aᵉ : Aᵉ) → dependent-homotopyᵉ (λ _ → Dᵉ) (λ _ → Hᵉ aᵉ) (gᵉ aᵉ) (g'ᵉ aᵉ)}
  {K'ᵉ : (aᵉ : Aᵉ) → dependent-homotopyᵉ (λ _ → Dᵉ) (λ _ → H'ᵉ aᵉ) (gᵉ aᵉ) (g'ᵉ aᵉ)}
  where

  abstract
    htpy-htpy-map-Σᵉ :
      (αᵉ : Hᵉ ~ᵉ H'ᵉ) →
      (βᵉ :
        (aᵉ : Aᵉ) (cᵉ : Cᵉ aᵉ) →
        Kᵉ aᵉ cᵉ ＝ᵉ apᵉ (λ pᵉ → trᵉ Dᵉ pᵉ (gᵉ aᵉ cᵉ)) (αᵉ aᵉ) ∙ᵉ K'ᵉ aᵉ cᵉ) →
      htpy-map-Σᵉ Dᵉ Hᵉ gᵉ Kᵉ ~ᵉ htpy-map-Σᵉ Dᵉ H'ᵉ gᵉ K'ᵉ
    htpy-htpy-map-Σᵉ αᵉ βᵉ (aᵉ ,ᵉ cᵉ) =
      apᵉ
        ( eq-pair-Σ'ᵉ)
        ( eq-pair-Σᵉ
          ( αᵉ aᵉ)
          ( map-compute-dependent-identification-eq-value-functionᵉ
            ( λ pᵉ → trᵉ Dᵉ pᵉ (gᵉ aᵉ cᵉ))
            ( λ _ → g'ᵉ aᵉ cᵉ)
            ( αᵉ aᵉ)
            ( Kᵉ aᵉ cᵉ)
            ( K'ᵉ aᵉ cᵉ)
            ( invᵉ
              ( ( apᵉ
                  ( Kᵉ aᵉ cᵉ ∙ᵉ_)
                  ( ap-constᵉ (g'ᵉ aᵉ cᵉ) (αᵉ aᵉ))) ∙ᵉ
                ( right-unitᵉ) ∙ᵉ
                ( βᵉ aᵉ cᵉ)))))
```

Asᵉ aᵉ corollaryᵉ ofᵉ theᵉ aboveᵉ statement,ᵉ weᵉ canᵉ provideᵉ aᵉ conditionᵉ whichᵉ
guaranteesᵉ thatᵉ `htpy-map-Σ`ᵉ isᵉ homotopicᵉ to theᵉ trivialᵉ homotopy.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ} (Dᵉ : Bᵉ → UUᵉ l4ᵉ)
  {fᵉ : Aᵉ → Bᵉ} {Hᵉ : fᵉ ~ᵉ fᵉ}
  {gᵉ : (aᵉ : Aᵉ) → Cᵉ aᵉ → Dᵉ (fᵉ aᵉ)}
  {Kᵉ : (aᵉ : Aᵉ) → trᵉ Dᵉ (Hᵉ aᵉ) ∘ᵉ gᵉ aᵉ ~ᵉ gᵉ aᵉ}
  where

  abstract
    htpy-htpy-map-Σ-refl-htpyᵉ :
      (αᵉ : Hᵉ ~ᵉ refl-htpyᵉ) →
      (βᵉ : (aᵉ : Aᵉ) (cᵉ : Cᵉ aᵉ) → Kᵉ aᵉ cᵉ ＝ᵉ apᵉ (λ pᵉ → trᵉ Dᵉ pᵉ (gᵉ aᵉ cᵉ)) (αᵉ aᵉ)) →
      htpy-map-Σᵉ Dᵉ Hᵉ gᵉ Kᵉ ~ᵉ refl-htpyᵉ
    htpy-htpy-map-Σ-refl-htpyᵉ αᵉ βᵉ =
      htpy-htpy-map-Σᵉ Dᵉ αᵉ (λ aᵉ cᵉ → βᵉ aᵉ cᵉ ∙ᵉ invᵉ right-unitᵉ)
```

### The map on total spaces induced by a family of truncated maps is truncated

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ}
  where

  abstract
    is-trunc-map-totᵉ : ((xᵉ : Aᵉ) → is-trunc-mapᵉ kᵉ (fᵉ xᵉ)) → is-trunc-mapᵉ kᵉ (totᵉ fᵉ)
    is-trunc-map-totᵉ Hᵉ yᵉ =
      is-trunc-equivᵉ kᵉ
        ( fiberᵉ (fᵉ (pr1ᵉ yᵉ)) (pr2ᵉ yᵉ))
        ( compute-fiber-totᵉ fᵉ yᵉ)
        ( Hᵉ (pr1ᵉ yᵉ) (pr2ᵉ yᵉ))

  abstract
    is-trunc-map-is-trunc-map-totᵉ :
      is-trunc-mapᵉ kᵉ (totᵉ fᵉ) → ((xᵉ : Aᵉ) → is-trunc-mapᵉ kᵉ (fᵉ xᵉ))
    is-trunc-map-is-trunc-map-totᵉ is-trunc-tot-fᵉ xᵉ zᵉ =
      is-trunc-equivᵉ kᵉ
        ( fiberᵉ (totᵉ fᵉ) (xᵉ ,ᵉ zᵉ))
        ( inv-compute-fiber-totᵉ fᵉ (xᵉ ,ᵉ zᵉ))
        ( is-trunc-tot-fᵉ (xᵉ ,ᵉ zᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ}
  where

  abstract
    is-contr-map-totᵉ :
      ((xᵉ : Aᵉ) → is-contr-mapᵉ (fᵉ xᵉ)) → is-contr-mapᵉ (totᵉ fᵉ)
    is-contr-map-totᵉ =
      is-trunc-map-totᵉ neg-two-𝕋ᵉ

  abstract
    is-prop-map-totᵉ : ((xᵉ : Aᵉ) → is-prop-mapᵉ (fᵉ xᵉ)) → is-prop-mapᵉ (totᵉ fᵉ)
    is-prop-map-totᵉ = is-trunc-map-totᵉ neg-one-𝕋ᵉ
```

### The functoriality of dependent pair types preserves truncatedness

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-trunc-map-map-Σ-map-baseᵉ :
      (kᵉ : 𝕋ᵉ) {fᵉ : Aᵉ → Bᵉ} (Cᵉ : Bᵉ → UUᵉ l3ᵉ) →
      is-trunc-mapᵉ kᵉ fᵉ → is-trunc-mapᵉ kᵉ (map-Σ-map-baseᵉ fᵉ Cᵉ)
    is-trunc-map-map-Σ-map-baseᵉ kᵉ {fᵉ} Cᵉ Hᵉ yᵉ =
      is-trunc-equiv'ᵉ kᵉ
        ( fiberᵉ fᵉ (pr1ᵉ yᵉ))
        ( equiv-fiber-map-Σ-map-base-fiberᵉ fᵉ Cᵉ yᵉ)
        ( Hᵉ (pr1ᵉ yᵉ))

  abstract
    is-prop-map-map-Σ-map-baseᵉ :
      {fᵉ : Aᵉ → Bᵉ} (Cᵉ : Bᵉ → UUᵉ l3ᵉ) →
      is-prop-mapᵉ fᵉ → is-prop-mapᵉ (map-Σ-map-baseᵉ fᵉ Cᵉ)
    is-prop-map-map-Σ-map-baseᵉ Cᵉ = is-trunc-map-map-Σ-map-baseᵉ neg-one-𝕋ᵉ Cᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  where

  abstract
    is-trunc-map-map-Σᵉ :
      (kᵉ : 𝕋ᵉ) (Dᵉ : Bᵉ → UUᵉ l4ᵉ) {fᵉ : Aᵉ → Bᵉ} {gᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ → Dᵉ (fᵉ xᵉ)} →
      is-trunc-mapᵉ kᵉ fᵉ → ((xᵉ : Aᵉ) → is-trunc-mapᵉ kᵉ (gᵉ xᵉ)) →
      is-trunc-mapᵉ kᵉ (map-Σᵉ Dᵉ fᵉ gᵉ)
    is-trunc-map-map-Σᵉ kᵉ Dᵉ {fᵉ} {gᵉ} Hᵉ Kᵉ =
      is-trunc-map-left-map-triangleᵉ kᵉ
        ( map-Σᵉ Dᵉ fᵉ gᵉ)
        ( map-Σ-map-baseᵉ fᵉ Dᵉ)
        ( totᵉ gᵉ)
        ( triangle-map-Σᵉ Dᵉ fᵉ gᵉ)
        ( is-trunc-map-map-Σ-map-baseᵉ kᵉ Dᵉ Hᵉ)
        ( is-trunc-map-totᵉ kᵉ Kᵉ)

  module _
    (Dᵉ : Bᵉ → UUᵉ l4ᵉ) {fᵉ : Aᵉ → Bᵉ} {gᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ → Dᵉ (fᵉ xᵉ)}
    where

    abstract
      is-contr-map-map-Σᵉ :
        is-contr-mapᵉ fᵉ → ((xᵉ : Aᵉ) → is-contr-mapᵉ (gᵉ xᵉ)) →
        is-contr-mapᵉ (map-Σᵉ Dᵉ fᵉ gᵉ)
      is-contr-map-map-Σᵉ = is-trunc-map-map-Σᵉ neg-two-𝕋ᵉ Dᵉ

    abstract
      is-prop-map-map-Σᵉ :
        is-prop-mapᵉ fᵉ → ((xᵉ : Aᵉ) → is-prop-mapᵉ (gᵉ xᵉ)) →
        is-prop-mapᵉ (map-Σᵉ Dᵉ fᵉ gᵉ)
      is-prop-map-map-Σᵉ = is-trunc-map-map-Σᵉ neg-one-𝕋ᵉ Dᵉ
```

### Commuting squares of maps on total spaces

#### Functoriality of `Σ` preserves commuting squares of maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Pᵉ : Aᵉ → UUᵉ l2ᵉ}
  {Bᵉ : UUᵉ l3ᵉ} {Qᵉ : Bᵉ → UUᵉ l4ᵉ}
  {Cᵉ : UUᵉ l5ᵉ} {Rᵉ : Cᵉ → UUᵉ l6ᵉ}
  {Dᵉ : UUᵉ l7ᵉ} (Sᵉ : Dᵉ → UUᵉ l8ᵉ)
  {top'ᵉ : Aᵉ → Cᵉ} {left'ᵉ : Aᵉ → Bᵉ} {right'ᵉ : Cᵉ → Dᵉ} {bottom'ᵉ : Bᵉ → Dᵉ}
  (topᵉ : (aᵉ : Aᵉ) → Pᵉ aᵉ → Rᵉ (top'ᵉ aᵉ))
  (leftᵉ : (aᵉ : Aᵉ) → Pᵉ aᵉ → Qᵉ (left'ᵉ aᵉ))
  (rightᵉ : (cᵉ : Cᵉ) → Rᵉ cᵉ → Sᵉ (right'ᵉ cᵉ))
  (bottomᵉ : (bᵉ : Bᵉ) → Qᵉ bᵉ → Sᵉ (bottom'ᵉ bᵉ))
  where

  coherence-square-maps-Σᵉ :
    {H'ᵉ : coherence-square-mapsᵉ top'ᵉ left'ᵉ right'ᵉ bottom'ᵉ} →
    ( (aᵉ : Aᵉ) (pᵉ : Pᵉ aᵉ) →
      dependent-identificationᵉ Sᵉ
        ( H'ᵉ aᵉ)
        ( bottomᵉ _ (leftᵉ _ pᵉ))
        ( rightᵉ _ (topᵉ _ pᵉ))) →
    coherence-square-mapsᵉ
      ( map-Σᵉ Rᵉ top'ᵉ topᵉ)
      ( map-Σᵉ Qᵉ left'ᵉ leftᵉ)
      ( map-Σᵉ Sᵉ right'ᵉ rightᵉ)
      ( map-Σᵉ Sᵉ bottom'ᵉ bottomᵉ)
  coherence-square-maps-Σᵉ {H'ᵉ} Hᵉ (aᵉ ,ᵉ pᵉ) = eq-pair-Σᵉ (H'ᵉ aᵉ) (Hᵉ aᵉ pᵉ)
```

#### Commuting squares of induced maps on total spaces

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Pᵉ : Aᵉ → UUᵉ l2ᵉ} {Qᵉ : Aᵉ → UUᵉ l3ᵉ} {Rᵉ : Aᵉ → UUᵉ l4ᵉ} {Sᵉ : Aᵉ → UUᵉ l5ᵉ}
  (topᵉ : (aᵉ : Aᵉ) → Pᵉ aᵉ → Rᵉ aᵉ)
  (leftᵉ : (aᵉ : Aᵉ) → Pᵉ aᵉ → Qᵉ aᵉ)
  (rightᵉ : (aᵉ : Aᵉ) → Rᵉ aᵉ → Sᵉ aᵉ)
  (bottomᵉ : (aᵉ : Aᵉ) → Qᵉ aᵉ → Sᵉ aᵉ)
  where

  coherence-square-maps-totᵉ :
    ((aᵉ : Aᵉ) → coherence-square-mapsᵉ (topᵉ aᵉ) (leftᵉ aᵉ) (rightᵉ aᵉ) (bottomᵉ aᵉ)) →
    coherence-square-mapsᵉ (totᵉ topᵉ) (totᵉ leftᵉ) (totᵉ rightᵉ) (totᵉ bottomᵉ)
  coherence-square-maps-totᵉ Hᵉ (aᵉ ,ᵉ pᵉ) = eq-pair-eq-fiberᵉ (Hᵉ aᵉ pᵉ)
```

#### `map-Σ-map-base` preserves commuting squares of maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ} (Sᵉ : Dᵉ → UUᵉ l5ᵉ)
  (topᵉ : Aᵉ → Cᵉ) (leftᵉ : Aᵉ → Bᵉ) (rightᵉ : Cᵉ → Dᵉ) (bottomᵉ : Bᵉ → Dᵉ)
  where

  coherence-square-maps-map-Σ-map-baseᵉ :
    (Hᵉ : coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ) →
    coherence-square-mapsᵉ
      ( map-Σᵉ (Sᵉ ∘ᵉ rightᵉ) topᵉ (λ aᵉ → trᵉ Sᵉ (Hᵉ aᵉ)))
      ( map-Σ-map-baseᵉ leftᵉ (Sᵉ ∘ᵉ bottomᵉ))
      ( map-Σ-map-baseᵉ rightᵉ Sᵉ)
      ( map-Σ-map-baseᵉ bottomᵉ Sᵉ)
  coherence-square-maps-map-Σ-map-baseᵉ Hᵉ (aᵉ ,ᵉ pᵉ) = eq-pair-Σᵉ (Hᵉ aᵉ) reflᵉ
```

### Commuting triangles of maps on total spaces

#### Functoriality of `Σ` preserves commuting triangles of maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Pᵉ : Aᵉ → UUᵉ l2ᵉ}
  {Bᵉ : UUᵉ l3ᵉ} {Qᵉ : Bᵉ → UUᵉ l4ᵉ}
  {Cᵉ : UUᵉ l5ᵉ} (Rᵉ : Cᵉ → UUᵉ l6ᵉ)
  {left'ᵉ : Aᵉ → Cᵉ} {right'ᵉ : Bᵉ → Cᵉ} {top'ᵉ : Aᵉ → Bᵉ}
  (leftᵉ : (aᵉ : Aᵉ) → Pᵉ aᵉ → Rᵉ (left'ᵉ aᵉ))
  (rightᵉ : (bᵉ : Bᵉ) → Qᵉ bᵉ → Rᵉ (right'ᵉ bᵉ))
  (topᵉ : (aᵉ : Aᵉ) → Pᵉ aᵉ → Qᵉ (top'ᵉ aᵉ))
  where

  coherence-triangle-maps-Σᵉ :
    {H'ᵉ : coherence-triangle-mapsᵉ left'ᵉ right'ᵉ top'ᵉ} →
    ( (aᵉ : Aᵉ) (pᵉ : Pᵉ aᵉ) →
      dependent-identificationᵉ Rᵉ (H'ᵉ aᵉ) (leftᵉ _ pᵉ) (rightᵉ _ (topᵉ _ pᵉ))) →
    coherence-triangle-mapsᵉ
      ( map-Σᵉ Rᵉ left'ᵉ leftᵉ)
      ( map-Σᵉ Rᵉ right'ᵉ rightᵉ)
      ( map-Σᵉ Qᵉ top'ᵉ topᵉ)
  coherence-triangle-maps-Σᵉ {H'ᵉ} Hᵉ (aᵉ ,ᵉ pᵉ) = eq-pair-Σᵉ (H'ᵉ aᵉ) (Hᵉ aᵉ pᵉ)
```

#### `map-Σ-map-base` preserves commuting triangles of maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (Sᵉ : Xᵉ → UUᵉ l4ᵉ)
  (leftᵉ : Aᵉ → Xᵉ) (rightᵉ : Bᵉ → Xᵉ) (topᵉ : Aᵉ → Bᵉ)
  where

  coherence-triangle-maps-map-Σ-map-baseᵉ :
    (Hᵉ : coherence-triangle-mapsᵉ leftᵉ rightᵉ topᵉ) →
    coherence-triangle-mapsᵉ
      ( map-Σ-map-baseᵉ leftᵉ Sᵉ)
      ( map-Σ-map-baseᵉ rightᵉ Sᵉ)
      ( map-Σᵉ (Sᵉ ∘ᵉ rightᵉ) topᵉ (λ aᵉ → trᵉ Sᵉ (Hᵉ aᵉ)))
  coherence-triangle-maps-map-Σ-map-baseᵉ Hᵉ (aᵉ ,ᵉ _) = eq-pair-Σᵉ (Hᵉ aᵉ) reflᵉ
```

### The action of `map-Σ-map-base` on identifications of the form `eq-pair-Σ` is given by the action on the base

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Cᵉ : Bᵉ → UUᵉ l3ᵉ)
  where

  compute-ap-map-Σ-map-base-eq-pair-Σᵉ :
    { sᵉ s'ᵉ : Aᵉ} (pᵉ : sᵉ ＝ᵉ s'ᵉ) {tᵉ : Cᵉ (fᵉ sᵉ)} {t'ᵉ : Cᵉ (fᵉ s'ᵉ)}
    ( qᵉ : trᵉ (Cᵉ ∘ᵉ fᵉ) pᵉ tᵉ ＝ᵉ t'ᵉ) →
    apᵉ (map-Σ-map-baseᵉ fᵉ Cᵉ) (eq-pair-Σᵉ pᵉ qᵉ) ＝ᵉ
    eq-pair-Σᵉ (apᵉ fᵉ pᵉ) (substitution-law-trᵉ Cᵉ fᵉ pᵉ ∙ᵉ qᵉ)
  compute-ap-map-Σ-map-base-eq-pair-Σᵉ reflᵉ reflᵉ = reflᵉ
```

### The action of `ind-Σ` on identifications in fibers of dependent pair types is given by the action of the fibers of the function with the first argument fixed

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  (fᵉ : (aᵉ : Aᵉ) (bᵉ : Bᵉ aᵉ) → Cᵉ)
  where

  compute-ap-ind-Σ-eq-pair-eq-fiberᵉ :
    {aᵉ : Aᵉ} {bᵉ b'ᵉ : Bᵉ aᵉ} (pᵉ : bᵉ ＝ᵉ b'ᵉ) →
    apᵉ (ind-Σᵉ fᵉ) (eq-pair-eq-fiberᵉ pᵉ) ＝ᵉ apᵉ (fᵉ aᵉ) pᵉ
  compute-ap-ind-Σ-eq-pair-eq-fiberᵉ reflᵉ = reflᵉ
```

### Computing the inverse of `equiv-tot`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  where

  compute-inv-equiv-totᵉ :
    (eᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ ≃ᵉ Cᵉ xᵉ) →
    map-inv-equivᵉ (equiv-totᵉ eᵉ) ~ᵉ
    map-equivᵉ (equiv-totᵉ (λ xᵉ → inv-equivᵉ (eᵉ xᵉ)))
  compute-inv-equiv-totᵉ eᵉ (aᵉ ,ᵉ cᵉ) =
    is-injective-equivᵉ
      ( equiv-totᵉ eᵉ)
      ( ( is-section-map-inv-equivᵉ (equiv-totᵉ eᵉ) (aᵉ ,ᵉ cᵉ)) ∙ᵉ
        ( eq-pair-eq-fiberᵉ (invᵉ (is-section-map-inv-equivᵉ (eᵉ aᵉ) cᵉ))))
```

### Dependent sums of morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Iᵉ : UUᵉ l5ᵉ} {Aᵉ : Iᵉ → UUᵉ l1ᵉ} {Bᵉ : Iᵉ → UUᵉ l2ᵉ} {Xᵉ : Iᵉ → UUᵉ l3ᵉ} {Yᵉ : Iᵉ → UUᵉ l4ᵉ}
  (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ) (gᵉ : (iᵉ : Iᵉ) → Xᵉ iᵉ → Yᵉ iᵉ)
  (αᵉ : (iᵉ : Iᵉ) → hom-arrowᵉ (fᵉ iᵉ) (gᵉ iᵉ))
  where

  tot-hom-arrowᵉ : hom-arrowᵉ (totᵉ fᵉ) (totᵉ gᵉ)
  pr1ᵉ tot-hom-arrowᵉ =
    totᵉ (λ iᵉ → map-domain-hom-arrowᵉ (fᵉ iᵉ) (gᵉ iᵉ) (αᵉ iᵉ))
  pr1ᵉ (pr2ᵉ tot-hom-arrowᵉ) =
    totᵉ (λ iᵉ → map-codomain-hom-arrowᵉ (fᵉ iᵉ) (gᵉ iᵉ) (αᵉ iᵉ))
  pr2ᵉ (pr2ᵉ tot-hom-arrowᵉ) =
    tot-htpyᵉ (λ iᵉ → coh-hom-arrowᵉ (fᵉ iᵉ) (gᵉ iᵉ) (αᵉ iᵉ))
```

## See also

-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ dependentᵉ pairᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-dependent-pair-types`](foundation.type-arithmetic-dependent-pair-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in dependentᵉ pairᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).ᵉ
-ᵉ Theᵉ universalᵉ propertyᵉ ofᵉ dependentᵉ pairᵉ typesᵉ isᵉ treatedᵉ in
  [`foundation.universal-property-dependent-pair-types`](foundation.universal-property-dependent-pair-types.md).ᵉ
-ᵉ Functorialᵉ propertiesᵉ ofᵉ cartesianᵉ productᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-cartesian-product-types`](foundation.functoriality-cartesian-product-types.md).ᵉ
-ᵉ Functorialᵉ propertiesᵉ ofᵉ dependentᵉ productᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).ᵉ