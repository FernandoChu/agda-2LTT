# Functoriality of dependent function types

```agda
module foundation.functoriality-dependent-function-typesᵉ where

open import foundation-core.functoriality-dependent-function-typesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.function-extensionalityᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.families-of-equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.precomposition-dependent-functionsᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.truncated-mapsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Theᵉ typeᵉ constructor forᵉ dependentᵉ functionᵉ typesᵉ actsᵉ contravariantlyᵉ in itsᵉ
firstᵉ argument,ᵉ andᵉ covariantlyᵉ in itsᵉ secondᵉ argument.ᵉ

## Properties

### An equivalence of base types and a family of equivalences induce an equivalence on dependent function types

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  { A'ᵉ : UUᵉ l1ᵉ} {B'ᵉ : A'ᵉ → UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ} (Bᵉ : Aᵉ → UUᵉ l4ᵉ)
  ( eᵉ : A'ᵉ ≃ᵉ Aᵉ) (fᵉ : (a'ᵉ : A'ᵉ) → B'ᵉ a'ᵉ ≃ᵉ Bᵉ (map-equivᵉ eᵉ a'ᵉ))
  where

  map-equiv-Πᵉ : ((a'ᵉ : A'ᵉ) → B'ᵉ a'ᵉ) → ((aᵉ : Aᵉ) → Bᵉ aᵉ)
  map-equiv-Πᵉ =
    ( map-Πᵉ
      ( λ aᵉ →
        ( trᵉ Bᵉ (is-section-map-inv-equivᵉ eᵉ aᵉ)) ∘ᵉ
        ( map-equivᵉ (fᵉ (map-inv-equivᵉ eᵉ aᵉ))))) ∘ᵉ
    ( precomp-Πᵉ (map-inv-equivᵉ eᵉ) B'ᵉ)

  abstract
    is-equiv-map-equiv-Πᵉ : is-equivᵉ map-equiv-Πᵉ
    is-equiv-map-equiv-Πᵉ =
      is-equiv-compᵉ
        ( map-Πᵉ
          ( λ aᵉ →
            ( trᵉ Bᵉ (is-section-map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ) aᵉ)) ∘ᵉ
            ( map-equivᵉ (fᵉ (map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ) aᵉ)))))
        ( precomp-Πᵉ (map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ)) B'ᵉ)
        ( is-equiv-precomp-Π-is-equivᵉ
          ( is-equiv-map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ))
          ( B'ᵉ))
        ( is-equiv-map-Π-is-fiberwise-equivᵉ
          ( λ aᵉ →
            is-equiv-compᵉ
              ( trᵉ Bᵉ (is-section-map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ) aᵉ))
              ( map-equivᵉ (fᵉ (map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ) aᵉ)))
              ( is-equiv-map-equivᵉ
                ( fᵉ (map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ) aᵉ)))
              ( is-equiv-trᵉ Bᵉ
                ( is-section-map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ) aᵉ))))

  equiv-Πᵉ : ((a'ᵉ : A'ᵉ) → B'ᵉ a'ᵉ) ≃ᵉ ((aᵉ : Aᵉ) → Bᵉ aᵉ)
  pr1ᵉ equiv-Πᵉ = map-equiv-Πᵉ
  pr2ᵉ equiv-Πᵉ = is-equiv-map-equiv-Πᵉ
```

#### Computing `map-equiv-Π`

```agda
  compute-map-equiv-Πᵉ :
    (hᵉ : (a'ᵉ : A'ᵉ) → B'ᵉ a'ᵉ) (a'ᵉ : A'ᵉ) →
    map-equiv-Πᵉ hᵉ (map-equivᵉ eᵉ a'ᵉ) ＝ᵉ map-equivᵉ (fᵉ a'ᵉ) (hᵉ a'ᵉ)
  compute-map-equiv-Πᵉ hᵉ a'ᵉ =
    ( apᵉ
      ( λ tᵉ →
        trᵉ Bᵉ tᵉ
          ( map-equivᵉ
            ( fᵉ (map-inv-equivᵉ eᵉ (map-equivᵉ eᵉ a'ᵉ)))
            ( hᵉ (map-inv-equivᵉ eᵉ (map-equivᵉ eᵉ a'ᵉ)))))
      ( coherence-map-inv-equivᵉ eᵉ a'ᵉ)) ∙ᵉ
    ( ( tr-apᵉ
        ( map-equivᵉ eᵉ)
        ( λ _ → idᵉ)
        ( is-retraction-map-inv-equivᵉ eᵉ a'ᵉ)
        ( map-equivᵉ
          ( fᵉ (map-inv-equivᵉ eᵉ (map-equivᵉ eᵉ a'ᵉ)))
          ( hᵉ (map-inv-equivᵉ eᵉ (map-equivᵉ eᵉ a'ᵉ))))) ∙ᵉ
      ( αᵉ ( map-inv-equivᵉ eᵉ (map-equivᵉ eᵉ a'ᵉ))
          ( is-retraction-map-inv-equivᵉ eᵉ a'ᵉ)))
    where
    αᵉ :
      (xᵉ : A'ᵉ) (pᵉ : xᵉ ＝ᵉ a'ᵉ) →
      trᵉ (Bᵉ ∘ᵉ map-equivᵉ eᵉ) pᵉ (map-equivᵉ (fᵉ xᵉ) (hᵉ xᵉ)) ＝ᵉ map-equivᵉ (fᵉ a'ᵉ) (hᵉ a'ᵉ)
    αᵉ xᵉ reflᵉ = reflᵉ

id-map-equiv-Πᵉ :
  { l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) →
  ( map-equiv-Πᵉ Bᵉ (id-equivᵉ {Aᵉ = Aᵉ}) (λ aᵉ → id-equivᵉ {Aᵉ = Bᵉ aᵉ})) ~ᵉ idᵉ
id-map-equiv-Πᵉ Bᵉ hᵉ = eq-htpyᵉ (compute-map-equiv-Πᵉ Bᵉ id-equivᵉ (λ _ → id-equivᵉ) hᵉ)
```

### Two maps being homotopic is equivalent to them being homotopic after pre- or postcomposition by an equivalence

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  equiv-htpy-map-Π-fam-equivᵉ :
    { Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ} →
    ( eᵉ : fam-equivᵉ Bᵉ Cᵉ) (fᵉ gᵉ : (aᵉ : Aᵉ) → Bᵉ aᵉ) →
    ( fᵉ ~ᵉ gᵉ) ≃ᵉ (map-Πᵉ (map-fam-equivᵉ eᵉ) fᵉ ~ᵉ map-Πᵉ (map-fam-equivᵉ eᵉ) gᵉ)
  equiv-htpy-map-Π-fam-equivᵉ eᵉ fᵉ gᵉ =
    equiv-Π-equiv-familyᵉ
      ( λ aᵉ → equiv-apᵉ (eᵉ aᵉ) (fᵉ aᵉ) (gᵉ aᵉ))
```

### Truncated families of maps induce truncated maps on dependent function types

```agda
abstract
  is-trunc-map-map-Πᵉ :
    (kᵉ : 𝕋ᵉ) {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
    (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ) →
    ((iᵉ : Iᵉ) → is-trunc-mapᵉ kᵉ (fᵉ iᵉ)) → is-trunc-mapᵉ kᵉ (map-Πᵉ fᵉ)
  is-trunc-map-map-Πᵉ kᵉ {Iᵉ = Iᵉ} fᵉ Hᵉ hᵉ =
    is-trunc-equiv'ᵉ kᵉ
      ( (iᵉ : Iᵉ) → fiberᵉ (fᵉ iᵉ) (hᵉ iᵉ))
      ( compute-fiber-map-Πᵉ fᵉ hᵉ)
      ( is-trunc-Πᵉ kᵉ (λ iᵉ → Hᵉ iᵉ (hᵉ iᵉ)))

abstract
  is-emb-map-Πᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
    {fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ} →
    ((iᵉ : Iᵉ) → is-embᵉ (fᵉ iᵉ)) → is-embᵉ (map-Πᵉ fᵉ)
  is-emb-map-Πᵉ {fᵉ = fᵉ} Hᵉ =
    is-emb-is-prop-mapᵉ
      ( is-trunc-map-map-Πᵉ neg-one-𝕋ᵉ fᵉ
        ( λ iᵉ → is-prop-map-is-embᵉ (Hᵉ iᵉ)))

emb-Πᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ} →
  ((iᵉ : Iᵉ) → Aᵉ iᵉ ↪ᵉ Bᵉ iᵉ) → ((iᵉ : Iᵉ) → Aᵉ iᵉ) ↪ᵉ ((iᵉ : Iᵉ) → Bᵉ iᵉ)
pr1ᵉ (emb-Πᵉ fᵉ) = map-Πᵉ (λ iᵉ → map-embᵉ (fᵉ iᵉ))
pr2ᵉ (emb-Πᵉ fᵉ) = is-emb-map-Πᵉ (λ iᵉ → is-emb-map-embᵉ (fᵉ iᵉ))
```

### A family of truncated maps over any map induces a truncated map on dependent function types

```agda
is-trunc-map-map-Π-is-trunc-map'ᵉ :
  (kᵉ : 𝕋ᵉ) {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
  {Jᵉ : UUᵉ l4ᵉ} (αᵉ : Jᵉ → Iᵉ) (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ) →
  ((iᵉ : Iᵉ) → is-trunc-mapᵉ kᵉ (fᵉ iᵉ)) → is-trunc-mapᵉ kᵉ (map-Π'ᵉ αᵉ fᵉ)
is-trunc-map-map-Π-is-trunc-map'ᵉ kᵉ {Jᵉ = Jᵉ} αᵉ fᵉ Hᵉ hᵉ =
  is-trunc-equiv'ᵉ kᵉ
    ( (jᵉ : Jᵉ) → fiberᵉ (fᵉ (αᵉ jᵉ)) (hᵉ jᵉ))
    ( compute-fiber-map-Π'ᵉ αᵉ fᵉ hᵉ)
    ( is-trunc-Πᵉ kᵉ (λ jᵉ → Hᵉ (αᵉ jᵉ) (hᵉ jᵉ)))

is-trunc-map-is-trunc-map-map-Π'ᵉ :
  (kᵉ : 𝕋ᵉ) {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
  (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ) →
  ({lᵉ : Level} {Jᵉ : UUᵉ lᵉ} (αᵉ : Jᵉ → Iᵉ) → is-trunc-mapᵉ kᵉ (map-Π'ᵉ αᵉ fᵉ)) →
  (iᵉ : Iᵉ) → is-trunc-mapᵉ kᵉ (fᵉ iᵉ)
is-trunc-map-is-trunc-map-map-Π'ᵉ kᵉ {Aᵉ = Aᵉ} {Bᵉ} fᵉ Hᵉ iᵉ bᵉ =
  is-trunc-equiv'ᵉ kᵉ
    ( fiberᵉ (map-Πᵉ (λ _ → fᵉ iᵉ)) (pointᵉ bᵉ))
    ( equiv-Σᵉ
      ( λ aᵉ → fᵉ iᵉ aᵉ ＝ᵉ bᵉ)
      ( equiv-universal-property-unitᵉ (Aᵉ iᵉ))
      ( λ hᵉ → equiv-apᵉ
        ( equiv-universal-property-unitᵉ (Bᵉ iᵉ))
        ( map-Πᵉ (λ _ → fᵉ iᵉ) hᵉ)
        ( pointᵉ bᵉ)))
    ( Hᵉ (λ _ → iᵉ) (pointᵉ bᵉ))

is-emb-map-Π-is-emb'ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ} →
  {Jᵉ : UUᵉ l4ᵉ} (αᵉ : Jᵉ → Iᵉ) (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ) →
  ((iᵉ : Iᵉ) → is-embᵉ (fᵉ iᵉ)) → is-embᵉ (map-Π'ᵉ αᵉ fᵉ)
is-emb-map-Π-is-emb'ᵉ αᵉ fᵉ Hᵉ =
  is-emb-is-prop-mapᵉ
    ( is-trunc-map-map-Π-is-trunc-map'ᵉ neg-one-𝕋ᵉ αᵉ fᵉ
      ( λ iᵉ → is-prop-map-is-embᵉ (Hᵉ iᵉ)))
```

###

```agda
HTPY-map-equiv-Πᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  { A'ᵉ : UUᵉ l1ᵉ} (B'ᵉ : A'ᵉ → UUᵉ l2ᵉ) {Aᵉ : UUᵉ l3ᵉ} (Bᵉ : Aᵉ → UUᵉ l4ᵉ)
  ( eᵉ e'ᵉ : A'ᵉ ≃ᵉ Aᵉ) (Hᵉ : htpy-equivᵉ eᵉ e'ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
HTPY-map-equiv-Πᵉ {A'ᵉ = A'ᵉ} B'ᵉ {Aᵉ} Bᵉ eᵉ e'ᵉ Hᵉ =
  ( fᵉ : (a'ᵉ : A'ᵉ) → B'ᵉ a'ᵉ ≃ᵉ Bᵉ (map-equivᵉ eᵉ a'ᵉ)) →
  ( f'ᵉ : (a'ᵉ : A'ᵉ) → B'ᵉ a'ᵉ ≃ᵉ Bᵉ (map-equivᵉ e'ᵉ a'ᵉ)) →
  ( Kᵉ : (a'ᵉ : A'ᵉ) →
        ((trᵉ Bᵉ (Hᵉ a'ᵉ)) ∘ᵉ (map-equivᵉ (fᵉ a'ᵉ))) ~ᵉ (map-equivᵉ (f'ᵉ a'ᵉ))) →
  ( map-equiv-Πᵉ Bᵉ eᵉ fᵉ) ~ᵉ (map-equiv-Πᵉ Bᵉ e'ᵉ f'ᵉ)

htpy-map-equiv-Π-refl-htpyᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  { A'ᵉ : UUᵉ l1ᵉ} {B'ᵉ : A'ᵉ → UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ} (Bᵉ : Aᵉ → UUᵉ l4ᵉ)
  ( eᵉ : A'ᵉ ≃ᵉ Aᵉ) →
  HTPY-map-equiv-Πᵉ B'ᵉ Bᵉ eᵉ eᵉ (refl-htpy-equivᵉ eᵉ)
htpy-map-equiv-Π-refl-htpyᵉ {B'ᵉ = B'ᵉ} Bᵉ eᵉ fᵉ f'ᵉ Kᵉ =
  ( htpy-map-Πᵉ
    ( λ aᵉ →
      ( trᵉ Bᵉ (is-section-map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ) aᵉ)) ·lᵉ
      ( Kᵉ (map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ) aᵉ)))) ·rᵉ
  ( precomp-Πᵉ (map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ)) B'ᵉ)

abstract
  htpy-map-equiv-Πᵉ :
    { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    { A'ᵉ : UUᵉ l1ᵉ} {B'ᵉ : A'ᵉ → UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ} (Bᵉ : Aᵉ → UUᵉ l4ᵉ)
    ( eᵉ e'ᵉ : A'ᵉ ≃ᵉ Aᵉ) (Hᵉ : htpy-equivᵉ eᵉ e'ᵉ) →
    HTPY-map-equiv-Πᵉ B'ᵉ Bᵉ eᵉ e'ᵉ Hᵉ
  htpy-map-equiv-Πᵉ {B'ᵉ = B'ᵉ} Bᵉ eᵉ e'ᵉ Hᵉ fᵉ f'ᵉ Kᵉ =
    ind-htpy-equivᵉ eᵉ
      ( HTPY-map-equiv-Πᵉ B'ᵉ Bᵉ eᵉ)
      ( htpy-map-equiv-Π-refl-htpyᵉ Bᵉ eᵉ)
      e'ᵉ Hᵉ fᵉ f'ᵉ Kᵉ

  compute-htpy-map-equiv-Πᵉ :
    { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    { A'ᵉ : UUᵉ l1ᵉ} {B'ᵉ : A'ᵉ → UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ} (Bᵉ : Aᵉ → UUᵉ l4ᵉ)
    ( eᵉ : A'ᵉ ≃ᵉ Aᵉ) →
    ( htpy-map-equiv-Πᵉ {B'ᵉ = B'ᵉ} Bᵉ eᵉ eᵉ (refl-htpy-equivᵉ eᵉ)) ＝ᵉ
    ( ( htpy-map-equiv-Π-refl-htpyᵉ Bᵉ eᵉ))
  compute-htpy-map-equiv-Πᵉ {B'ᵉ = B'ᵉ} Bᵉ eᵉ =
    compute-ind-htpy-equivᵉ eᵉ
      ( HTPY-map-equiv-Πᵉ B'ᵉ Bᵉ eᵉ)
      ( htpy-map-equiv-Π-refl-htpyᵉ Bᵉ eᵉ)

map-automorphism-Πᵉ :
  { l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  ( eᵉ : Aᵉ ≃ᵉ Aᵉ) (fᵉ : (aᵉ : Aᵉ) → Bᵉ aᵉ ≃ᵉ Bᵉ (map-equivᵉ eᵉ aᵉ)) →
  ( (aᵉ : Aᵉ) → Bᵉ aᵉ) → ((aᵉ : Aᵉ) → Bᵉ aᵉ)
map-automorphism-Πᵉ {Bᵉ = Bᵉ} eᵉ fᵉ =
  ( map-Πᵉ (λ aᵉ → (map-inv-is-equivᵉ (is-equiv-map-equivᵉ (fᵉ aᵉ))))) ∘ᵉ
  ( precomp-Πᵉ (map-equivᵉ eᵉ) Bᵉ)

abstract
  is-equiv-map-automorphism-Πᵉ :
    { l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
    ( eᵉ : Aᵉ ≃ᵉ Aᵉ) (fᵉ : (aᵉ : Aᵉ) → Bᵉ aᵉ ≃ᵉ Bᵉ (map-equivᵉ eᵉ aᵉ)) →
    is-equivᵉ (map-automorphism-Πᵉ eᵉ fᵉ)
  is-equiv-map-automorphism-Πᵉ {Bᵉ = Bᵉ} eᵉ fᵉ =
    is-equiv-compᵉ _ _
      ( is-equiv-precomp-Π-is-equivᵉ (is-equiv-map-equivᵉ eᵉ) Bᵉ)
      ( is-equiv-map-Π-is-fiberwise-equivᵉ
        ( λ aᵉ → is-equiv-map-inv-is-equivᵉ (is-equiv-map-equivᵉ (fᵉ aᵉ))))

automorphism-Πᵉ :
  { l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  ( eᵉ : Aᵉ ≃ᵉ Aᵉ) (fᵉ : (aᵉ : Aᵉ) → Bᵉ aᵉ ≃ᵉ Bᵉ (map-equivᵉ eᵉ aᵉ)) →
  ( (aᵉ : Aᵉ) → Bᵉ aᵉ) ≃ᵉ ((aᵉ : Aᵉ) → Bᵉ aᵉ)
pr1ᵉ (automorphism-Πᵉ eᵉ fᵉ) = map-automorphism-Πᵉ eᵉ fᵉ
pr2ᵉ (automorphism-Πᵉ eᵉ fᵉ) = is-equiv-map-automorphism-Πᵉ eᵉ fᵉ
```

## See also

-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ dependentᵉ functionᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in dependentᵉ functionᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).ᵉ
-ᵉ Functorialᵉ propertiesᵉ ofᵉ functionᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-function-types`](foundation.functoriality-function-types.md).ᵉ
-ᵉ Functorialᵉ propertiesᵉ ofᵉ dependentᵉ pairᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-dependent-pair-types`](foundation.functoriality-dependent-pair-types.md).ᵉ
-ᵉ Functorialᵉ propertiesᵉ ofᵉ cartesianᵉ productᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-cartesian-product-types`](foundation.functoriality-cartesian-product-types.md).ᵉ