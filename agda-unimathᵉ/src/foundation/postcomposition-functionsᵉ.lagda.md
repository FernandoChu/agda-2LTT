# Postcomposition of functions

```agda
module foundation.postcomposition-functionsᵉ where

open import foundation-core.postcomposition-functionsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.postcomposition-dependent-functionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
```

</details>

## Idea

Givenᵉ aᵉ mapᵉ `fᵉ : Xᵉ → Y`ᵉ andᵉ aᵉ typeᵉ `A`,ᵉ theᵉ
{{#conceptᵉ "postcompositionᵉ function"ᵉ}}

```text
  fᵉ ∘ᵉ -ᵉ : (Aᵉ → Xᵉ) → (Aᵉ → Yᵉ)
```

isᵉ definedᵉ byᵉ `λᵉ hᵉ xᵉ → fᵉ (hᵉ x)`.ᵉ

## Properties

### Postcomposition preserves homotopies

```agda
htpy-postcompᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (Aᵉ : UUᵉ l3ᵉ) →
  {fᵉ gᵉ : Xᵉ → Yᵉ} → (fᵉ ~ᵉ gᵉ) → postcompᵉ Aᵉ fᵉ ~ᵉ postcompᵉ Aᵉ gᵉ
htpy-postcompᵉ Aᵉ Hᵉ hᵉ = eq-htpyᵉ (Hᵉ ·rᵉ hᵉ)

compute-htpy-postcomp-refl-htpyᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (fᵉ : Bᵉ → Cᵉ) →
  (htpy-postcompᵉ Aᵉ (refl-htpy'ᵉ fᵉ)) ~ᵉ refl-htpyᵉ
compute-htpy-postcomp-refl-htpyᵉ Aᵉ fᵉ hᵉ = eq-htpy-refl-htpyᵉ (fᵉ ∘ᵉ hᵉ)
```

### Computations of the fibers of `postcomp`

Weᵉ giveᵉ threeᵉ computationsᵉ ofᵉ theᵉ fibersᵉ ofᵉ aᵉ postcompositionᵉ functionᵉ:

1.ᵉ `fiberᵉ (postcompᵉ Aᵉ fᵉ) hᵉ ≃ᵉ ((xᵉ : Aᵉ) → fiberᵉ fᵉ (hᵉ x))`ᵉ
2.ᵉ `fiberᵉ (postcompᵉ Aᵉ fᵉ) hᵉ ≃ᵉ Σᵉ (Aᵉ → Xᵉ) (coherence-triangle-mapsᵉ hᵉ f)`,ᵉ andᵉ
3.ᵉ `fiberᵉ (postcompᵉ Aᵉ fᵉ) (fᵉ ∘ᵉ hᵉ) ≃ᵉ Σᵉ (Aᵉ → Xᵉ) (λ gᵉ → coherence-square-mapsᵉ gᵉ hᵉ fᵉ f)`ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (Aᵉ : UUᵉ l3ᵉ)
  (fᵉ : Xᵉ → Yᵉ)
  where

  inv-compute-Π-fiber-postcompᵉ :
    (hᵉ : Aᵉ → Yᵉ) → fiberᵉ (postcompᵉ Aᵉ fᵉ) hᵉ ≃ᵉ ((xᵉ : Aᵉ) → fiberᵉ fᵉ (hᵉ xᵉ))
  inv-compute-Π-fiber-postcompᵉ hᵉ =
    inv-distributive-Π-Σᵉ ∘eᵉ equiv-totᵉ (λ _ → equiv-funextᵉ)

  compute-Π-fiber-postcompᵉ :
    (hᵉ : Aᵉ → Yᵉ) → ((xᵉ : Aᵉ) → fiberᵉ fᵉ (hᵉ xᵉ)) ≃ᵉ fiberᵉ (postcompᵉ Aᵉ fᵉ) hᵉ
  compute-Π-fiber-postcompᵉ hᵉ =
    equiv-totᵉ (λ _ → equiv-eq-htpyᵉ) ∘eᵉ distributive-Π-Σᵉ

  inv-compute-coherence-triangle-fiber-postcompᵉ :
    (hᵉ : Aᵉ → Yᵉ) →
    fiberᵉ (postcompᵉ Aᵉ fᵉ) hᵉ ≃ᵉ Σᵉ (Aᵉ → Xᵉ) (coherence-triangle-mapsᵉ hᵉ fᵉ)
  inv-compute-coherence-triangle-fiber-postcompᵉ hᵉ =
    equiv-totᵉ (λ _ → equiv-funextᵉ) ∘eᵉ equiv-fiberᵉ (postcompᵉ Aᵉ fᵉ) hᵉ

  compute-coherence-triangle-fiber-postcompᵉ :
    (hᵉ : Aᵉ → Yᵉ) →
    Σᵉ (Aᵉ → Xᵉ) (coherence-triangle-mapsᵉ hᵉ fᵉ) ≃ᵉ fiberᵉ (postcompᵉ Aᵉ fᵉ) hᵉ
  compute-coherence-triangle-fiber-postcompᵉ hᵉ =
    inv-equivᵉ (inv-compute-coherence-triangle-fiber-postcompᵉ hᵉ)

  inv-compute-fiber-postcompᵉ :
    (hᵉ : Aᵉ → Xᵉ) →
    fiberᵉ (postcompᵉ Aᵉ fᵉ) (fᵉ ∘ᵉ hᵉ) ≃ᵉ
    Σᵉ (Aᵉ → Xᵉ) (λ gᵉ → coherence-square-mapsᵉ gᵉ hᵉ fᵉ fᵉ)
  inv-compute-fiber-postcompᵉ hᵉ =
    inv-compute-coherence-triangle-fiber-postcompᵉ (fᵉ ∘ᵉ hᵉ)

  compute-fiber-postcompᵉ :
    (hᵉ : Aᵉ → Xᵉ) →
    Σᵉ (Aᵉ → Xᵉ) (λ gᵉ → coherence-square-mapsᵉ gᵉ hᵉ fᵉ fᵉ) ≃ᵉ
    fiberᵉ (postcompᵉ Aᵉ fᵉ) (fᵉ ∘ᵉ hᵉ)
  compute-fiber-postcompᵉ hᵉ = compute-coherence-triangle-fiber-postcompᵉ (fᵉ ∘ᵉ hᵉ)
```

### Postcomposition and equivalences

#### A map `f` is an equivalence if and only if postcomposing by `f` is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ → Yᵉ)
  (Hᵉ : {l3ᵉ : Level} (Aᵉ : UUᵉ l3ᵉ) → is-equivᵉ (postcompᵉ Aᵉ fᵉ))
  where

  map-inv-is-equiv-is-equiv-postcompᵉ : Yᵉ → Xᵉ
  map-inv-is-equiv-is-equiv-postcompᵉ = map-inv-is-equivᵉ (Hᵉ Yᵉ) idᵉ

  is-section-map-inv-is-equiv-is-equiv-postcompᵉ :
    ( fᵉ ∘ᵉ map-inv-is-equiv-is-equiv-postcompᵉ) ~ᵉ idᵉ
  is-section-map-inv-is-equiv-is-equiv-postcompᵉ =
    htpy-eqᵉ (is-section-map-inv-is-equivᵉ (Hᵉ Yᵉ) idᵉ)

  is-retraction-map-inv-is-equiv-is-equiv-postcompᵉ :
    ( map-inv-is-equiv-is-equiv-postcompᵉ ∘ᵉ fᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-is-equiv-is-equiv-postcompᵉ =
    htpy-eqᵉ
      ( apᵉ
        ( pr1ᵉ)
        ( eq-is-contrᵉ
          ( is-contr-map-is-equivᵉ (Hᵉ Xᵉ) fᵉ)
          { xᵉ =
              ( map-inv-is-equiv-is-equiv-postcompᵉ ∘ᵉ fᵉ) ,ᵉ
              ( apᵉ (_∘ᵉ fᵉ) (is-section-map-inv-is-equivᵉ (Hᵉ Yᵉ) idᵉ))}
          { yᵉ = idᵉ ,ᵉ reflᵉ}))

  abstract
    is-equiv-is-equiv-postcompᵉ : is-equivᵉ fᵉ
    is-equiv-is-equiv-postcompᵉ =
      is-equiv-is-invertibleᵉ
        map-inv-is-equiv-is-equiv-postcompᵉ
        is-section-map-inv-is-equiv-is-equiv-postcompᵉ
        is-retraction-map-inv-is-equiv-is-equiv-postcompᵉ
```

Theᵉ followingᵉ versionᵉ ofᵉ theᵉ sameᵉ theoremᵉ worksᵉ whenᵉ `X`ᵉ andᵉ `Y`ᵉ areᵉ in theᵉ sameᵉ
universe.ᵉ Theᵉ conditionᵉ ofᵉ inducingᵉ equivalencesᵉ byᵉ postcompositionᵉ isᵉ
simplifiedᵉ to thatᵉ universe.ᵉ

```agda
is-equiv-is-equiv-postcomp'ᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} {Yᵉ : UUᵉ lᵉ} (fᵉ : Xᵉ → Yᵉ) →
  ((Aᵉ : UUᵉ lᵉ) → is-equivᵉ (postcompᵉ Aᵉ fᵉ)) → is-equivᵉ fᵉ
is-equiv-is-equiv-postcomp'ᵉ {lᵉ} {Xᵉ} {Yᵉ} fᵉ is-equiv-postcomp-fᵉ =
  let section-fᵉ = centerᵉ (is-contr-map-is-equivᵉ (is-equiv-postcomp-fᵉ Yᵉ) idᵉ)
  in
  is-equiv-is-invertibleᵉ
    ( pr1ᵉ section-fᵉ)
    ( htpy-eqᵉ (pr2ᵉ section-fᵉ))
    ( htpy-eqᵉ
      ( apᵉ
        ( pr1ᵉ)
        ( eq-is-contr'ᵉ
          ( is-contr-map-is-equivᵉ (is-equiv-postcomp-fᵉ Xᵉ) fᵉ)
          ( pr1ᵉ section-fᵉ ∘ᵉ fᵉ ,ᵉ apᵉ (_∘ᵉ fᵉ) (pr2ᵉ section-fᵉ))
          ( idᵉ ,ᵉ reflᵉ))))

abstract
  is-equiv-postcomp-is-equivᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ → Yᵉ) → is-equivᵉ fᵉ →
    {l3ᵉ : Level} (Aᵉ : UUᵉ l3ᵉ) → is-equivᵉ (postcompᵉ Aᵉ fᵉ)
  is-equiv-postcomp-is-equivᵉ {Xᵉ = Xᵉ} {Yᵉ = Yᵉ} fᵉ is-equiv-fᵉ Aᵉ =
    is-equiv-is-invertibleᵉ
      ( postcompᵉ Aᵉ (map-inv-is-equivᵉ is-equiv-fᵉ))
      ( eq-htpyᵉ ∘ᵉ
        right-whisker-compᵉ (is-section-map-inv-is-equivᵉ is-equiv-fᵉ))
      ( eq-htpyᵉ ∘ᵉ
        right-whisker-compᵉ (is-retraction-map-inv-is-equivᵉ is-equiv-fᵉ))

  is-equiv-postcomp-equivᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ ≃ᵉ Yᵉ) →
    {l3ᵉ : Level} (Aᵉ : UUᵉ l3ᵉ) → is-equivᵉ (postcompᵉ Aᵉ (map-equivᵉ fᵉ))
  is-equiv-postcomp-equivᵉ fᵉ =
    is-equiv-postcomp-is-equivᵉ (map-equivᵉ fᵉ) (is-equiv-map-equivᵉ fᵉ)

equiv-postcompᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (Aᵉ : UUᵉ l3ᵉ) →
  (Xᵉ ≃ᵉ Yᵉ) → (Aᵉ → Xᵉ) ≃ᵉ (Aᵉ → Yᵉ)
pr1ᵉ (equiv-postcompᵉ Aᵉ eᵉ) = postcompᵉ Aᵉ (map-equivᵉ eᵉ)
pr2ᵉ (equiv-postcompᵉ Aᵉ eᵉ) =
  is-equiv-postcomp-is-equivᵉ (map-equivᵉ eᵉ) (is-equiv-map-equivᵉ eᵉ) Aᵉ
```

### Two maps being homotopic is equivalent to them being homotopic after pre- or postcomposition by an equivalence

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  equiv-htpy-postcomp-htpyᵉ :
    (eᵉ : Bᵉ ≃ᵉ Cᵉ) (fᵉ gᵉ : Aᵉ → Bᵉ) → (fᵉ ~ᵉ gᵉ) ≃ᵉ (map-equivᵉ eᵉ ∘ᵉ fᵉ ~ᵉ map-equivᵉ eᵉ ∘ᵉ gᵉ)
  equiv-htpy-postcomp-htpyᵉ eᵉ fᵉ gᵉ =
    equiv-Π-equiv-familyᵉ (λ aᵉ → equiv-apᵉ eᵉ (fᵉ aᵉ) (gᵉ aᵉ))
```

### Computing the action on identifications of postcomposition by a map

Considerᵉ aᵉ mapᵉ `fᵉ : Bᵉ → C`ᵉ andᵉ twoᵉ functionsᵉ `gᵉ hᵉ : Aᵉ → B`.ᵉ Thenᵉ theᵉ
[actionᵉ onᵉ identifications](foundation.action-on-identifications-functions.mdᵉ)
`apᵉ (postcompᵉ Aᵉ f)`ᵉ fitsᵉ in aᵉ
[commutingᵉ square](foundation-core.commuting-squares-of-maps.mdᵉ)

```text
                    apᵉ (postcompᵉ Aᵉ fᵉ)
       (gᵉ = hᵉ) -------------------------->ᵉ (fᵉ ∘ᵉ gᵉ = fᵉ ∘ᵉ hᵉ)
          |                                       |
  htpy-eqᵉ |                                       | htpy-eqᵉ
          ∨ᵉ                                       ∨ᵉ
       (gᵉ ~ᵉ hᵉ) -------------------------->ᵉ (fᵉ ∘ᵉ gᵉ ~ᵉ fᵉ ∘ᵉ h).ᵉ
                          fᵉ ·lᵉ_
```

Similarly,ᵉ theᵉ actionᵉ onᵉ identificationsᵉ `apᵉ (postcompᵉ Aᵉ f)`ᵉ alsoᵉ fitsᵉ in aᵉ
commutingᵉ squareᵉ

```text
                          fᵉ ·lᵉ_
       (gᵉ ~ᵉ hᵉ) -------------------------->ᵉ (fᵉ ∘ᵉ gᵉ ~ᵉ fᵉ ∘ᵉ hᵉ)
          |                                       |
  eq-htpyᵉ |                                       | eq-htpyᵉ
          ∨ᵉ                                       ∨ᵉ
       (gᵉ = hᵉ) -------------------------->ᵉ (fᵉ ∘ᵉ gᵉ = fᵉ ∘ᵉ h).ᵉ
                     apᵉ (postcompᵉ Aᵉ fᵉ)
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  {gᵉ hᵉ : Aᵉ → Bᵉ} (fᵉ : Bᵉ → Cᵉ)
  where

  compute-htpy-eq-ap-postcompᵉ :
    coherence-square-mapsᵉ
      ( apᵉ (postcompᵉ Aᵉ fᵉ) {xᵉ = gᵉ} {yᵉ = hᵉ})
      ( htpy-eqᵉ)
      ( htpy-eqᵉ)
      ( fᵉ ·lᵉ_)
  compute-htpy-eq-ap-postcompᵉ =
    compute-htpy-eq-ap-postcomp-Πᵉ fᵉ

  compute-eq-htpy-ap-postcompᵉ :
    coherence-square-mapsᵉ
      ( fᵉ ·lᵉ_)
      ( eq-htpyᵉ)
      ( eq-htpyᵉ)
      ( apᵉ (postcompᵉ Aᵉ fᵉ) {xᵉ = gᵉ} {yᵉ = hᵉ})
  compute-eq-htpy-ap-postcompᵉ =
    compute-eq-htpy-ap-postcomp-Πᵉ fᵉ
```