# Precomposition of dependent functions

```agda
module foundation.precomposition-dependent-functionsᵉ where

open import foundation-core.precomposition-dependent-functionsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.truncated-mapsᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Properties

### Equivalences induce an equivalence from the type of homotopies between two dependent functions to the type of homotopies between their precomposites

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  equiv-htpy-precomp-htpy-Πᵉ :
    {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Bᵉ → UUᵉ l3ᵉ} (fᵉ gᵉ : (bᵉ : Bᵉ) → Cᵉ bᵉ) (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
    (fᵉ ~ᵉ gᵉ) ≃ᵉ (fᵉ ∘ᵉ map-equivᵉ eᵉ ~ᵉ gᵉ ∘ᵉ map-equivᵉ eᵉ)
  equiv-htpy-precomp-htpy-Πᵉ fᵉ gᵉ eᵉ =
    equiv-precomp-Πᵉ eᵉ (eq-valueᵉ fᵉ gᵉ)
```

### The action on identifications of precomposition of dependent functions

Considerᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ twoᵉ dependentᵉ functionsᵉ `gᵉ hᵉ : (xᵉ : Bᵉ) → Cᵉ x`.ᵉ
Thenᵉ theᵉ squareᵉ

```text
                     apᵉ (precomp-Πᵉ fᵉ Cᵉ)
       (gᵉ ＝ᵉ hᵉ) --------------------------->ᵉ (gᵉ ∘ᵉ fᵉ ＝ᵉ hᵉ ∘ᵉ fᵉ)
          |                                         |
  htpy-eqᵉ |                                         | htpy-eqᵉ
          ∨ᵉ                                         ∨ᵉ
       (gᵉ ~ᵉ hᵉ) ---------------------------->ᵉ (gᵉ ∘ᵉ fᵉ ~ᵉ hᵉ ∘ᵉ fᵉ)
                precomp-Πᵉ fᵉ (eq-valueᵉ gᵉ hᵉ)
```

[commutes](foundation-core.commuting-squares-of-maps.md).ᵉ

Similarly,ᵉ theᵉ mapᵉ `apᵉ (precomp-Πᵉ fᵉ C)`ᵉ fitsᵉ in aᵉ commutingᵉ squareᵉ

```text
                precomp-Πᵉ fᵉ (eq-valueᵉ gᵉ hᵉ)
       (gᵉ ~ᵉ hᵉ) ---------------------------->ᵉ (gᵉ ∘ᵉ fᵉ ~ᵉ hᵉ ∘ᵉ fᵉ)
          |                                         |
  eq-htpyᵉ |                                         | eq-htpyᵉ
          ∨ᵉ                                         ∨ᵉ
       (gᵉ ＝ᵉ hᵉ) --------------------------->ᵉ (gᵉ ∘ᵉ fᵉ ＝ᵉ hᵉ ∘ᵉ f).ᵉ
                     apᵉ (precomp-Πᵉ fᵉ Cᵉ)
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) {Cᵉ : Bᵉ → UUᵉ l3ᵉ}
  {gᵉ hᵉ : (bᵉ : Bᵉ) → Cᵉ bᵉ}
  where

  compute-htpy-eq-ap-precomp-Πᵉ :
    coherence-square-mapsᵉ
      ( apᵉ (precomp-Πᵉ fᵉ Cᵉ) {gᵉ} {hᵉ})
      ( htpy-eqᵉ)
      ( htpy-eqᵉ)
      ( precomp-Πᵉ fᵉ (eq-valueᵉ gᵉ hᵉ))
  compute-htpy-eq-ap-precomp-Πᵉ reflᵉ = reflᵉ

  compute-eq-htpy-ap-precomp-Πᵉ :
    coherence-square-mapsᵉ
      ( precomp-Πᵉ fᵉ (eq-valueᵉ gᵉ hᵉ))
      ( eq-htpyᵉ)
      ( eq-htpyᵉ)
      ( apᵉ (precomp-Πᵉ fᵉ Cᵉ) {gᵉ} {hᵉ})
  compute-eq-htpy-ap-precomp-Πᵉ =
    vertical-inv-equiv-coherence-square-mapsᵉ
      ( apᵉ (precomp-Πᵉ fᵉ Cᵉ))
      ( equiv-funextᵉ)
      ( equiv-funextᵉ)
      ( precomp-Πᵉ fᵉ (eq-valueᵉ gᵉ hᵉ))
      ( compute-htpy-eq-ap-precomp-Πᵉ)
```

### Precomposing functions `Π B C` by `f : A → B` is `k+1`-truncated if and only if precomposing homotopies is `k`-truncated

```agda
is-trunc-map-succ-precomp-Πᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  {Cᵉ : Bᵉ → UUᵉ l3ᵉ} →
  ((gᵉ hᵉ : (bᵉ : Bᵉ) → Cᵉ bᵉ) → is-trunc-mapᵉ kᵉ (precomp-Πᵉ fᵉ (eq-valueᵉ gᵉ hᵉ))) →
  is-trunc-mapᵉ (succ-𝕋ᵉ kᵉ) (precomp-Πᵉ fᵉ Cᵉ)
is-trunc-map-succ-precomp-Πᵉ {kᵉ = kᵉ} {fᵉ = fᵉ} {Cᵉ = Cᵉ} Hᵉ =
  is-trunc-map-is-trunc-map-apᵉ kᵉ (precomp-Πᵉ fᵉ Cᵉ)
    ( λ gᵉ hᵉ →
      is-trunc-map-top-is-trunc-map-bottom-is-equivᵉ kᵉ
        ( apᵉ (precomp-Πᵉ fᵉ Cᵉ))
        ( htpy-eqᵉ)
        ( htpy-eqᵉ)
        ( precomp-Πᵉ fᵉ (eq-valueᵉ gᵉ hᵉ))
        ( compute-htpy-eq-ap-precomp-Πᵉ fᵉ)
        ( funextᵉ gᵉ hᵉ)
        ( funextᵉ (gᵉ ∘ᵉ fᵉ) (hᵉ ∘ᵉ fᵉ))
        ( Hᵉ gᵉ hᵉ))
```