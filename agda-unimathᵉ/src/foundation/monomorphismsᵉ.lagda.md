# Monomorphisms

```agda
module foundation.monomorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-function-typesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Aᵉ functionᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ aᵉ monomorphismᵉ ifᵉ wheneverᵉ weᵉ haveᵉ twoᵉ functionsᵉ
`gᵉ hᵉ : Xᵉ → A`ᵉ suchᵉ thatᵉ `fᵉ ∘ᵉ gᵉ = fᵉ ∘ᵉ h`,ᵉ thenᵉ in factᵉ `gᵉ = h`.ᵉ Theᵉ wayᵉ to stateᵉ
thisᵉ in Homotopyᵉ Typeᵉ Theoryᵉ isᵉ to sayᵉ thatᵉ postcompositionᵉ byᵉ `f`ᵉ isᵉ anᵉ
embedding.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level)
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-mono-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  is-mono-Propᵉ = Π-Propᵉ (UUᵉ l3ᵉ) λ Xᵉ → is-emb-Propᵉ (postcompᵉ Xᵉ fᵉ)

  is-monoᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  is-monoᵉ = type-Propᵉ is-mono-Propᵉ

  is-prop-is-monoᵉ : is-propᵉ is-monoᵉ
  is-prop-is-monoᵉ = is-prop-type-Propᵉ is-mono-Propᵉ
```

## Properties

Ifᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ aᵉ monomorphismᵉ thenᵉ forᵉ anyᵉ `gᵉ hᵉ : Xᵉ → A`ᵉ weᵉ haveᵉ anᵉ
equivalenceᵉ `(fᵉ ∘ᵉ gᵉ = fᵉ ∘ᵉ hᵉ) ≃ᵉ (gᵉ = h)`.ᵉ Inᵉ particular,ᵉ ifᵉ `fᵉ ∘ᵉ gᵉ = fᵉ ∘ᵉ h`ᵉ thenᵉ
`gᵉ = h`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level)
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  (pᵉ : is-monoᵉ l3ᵉ fᵉ) {Xᵉ : UUᵉ l3ᵉ} (gᵉ hᵉ : Xᵉ → Aᵉ)
  where

  equiv-postcomp-is-monoᵉ : (gᵉ ＝ᵉ hᵉ) ≃ᵉ ((fᵉ ∘ᵉ gᵉ) ＝ᵉ (fᵉ ∘ᵉ hᵉ))
  pr1ᵉ equiv-postcomp-is-monoᵉ = apᵉ (fᵉ ∘ᵉ_)
  pr2ᵉ equiv-postcomp-is-monoᵉ = pᵉ Xᵉ gᵉ hᵉ

  is-injective-postcomp-is-monoᵉ : (fᵉ ∘ᵉ gᵉ) ＝ᵉ (fᵉ ∘ᵉ hᵉ) → gᵉ ＝ᵉ hᵉ
  is-injective-postcomp-is-monoᵉ = map-inv-equivᵉ equiv-postcomp-is-monoᵉ
```

Aᵉ functionᵉ isᵉ aᵉ monomorphismᵉ ifᵉ andᵉ onlyᵉ ifᵉ itᵉ isᵉ anᵉ embedding.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-mono-is-embᵉ : is-embᵉ fᵉ → {l3ᵉ : Level} → is-monoᵉ l3ᵉ fᵉ
  is-mono-is-embᵉ is-emb-fᵉ Xᵉ =
    is-emb-is-prop-mapᵉ
      ( is-trunc-map-postcomp-is-trunc-mapᵉ neg-one-𝕋ᵉ fᵉ
        ( is-prop-map-is-embᵉ is-emb-fᵉ)
        ( Xᵉ))

  is-emb-is-monoᵉ : ({l3ᵉ : Level} → is-monoᵉ l3ᵉ fᵉ) → is-embᵉ fᵉ
  is-emb-is-monoᵉ is-mono-fᵉ =
    is-emb-is-prop-mapᵉ
      ( is-trunc-map-is-trunc-map-postcompᵉ neg-one-𝕋ᵉ fᵉ
        ( λ Xᵉ → is-prop-map-is-embᵉ (is-mono-fᵉ Xᵉ)))
```

Weᵉ constructᵉ anᵉ explicitᵉ equivalenceᵉ forᵉ postcompositionᵉ forᵉ homotopiesᵉ betweenᵉ
functionsᵉ (ratherᵉ thanᵉ equalityᵉ) whenᵉ theᵉ mapᵉ isᵉ anᵉ embedding.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ ↪ᵉ Bᵉ)
  {Xᵉ : UUᵉ l3ᵉ} (gᵉ hᵉ : Xᵉ → Aᵉ)
  where

  map-inv-equiv-htpy-postcomp-is-embᵉ :
    (pr1ᵉ fᵉ ∘ᵉ gᵉ) ~ᵉ (pr1ᵉ fᵉ ∘ᵉ hᵉ) → gᵉ ~ᵉ hᵉ
  map-inv-equiv-htpy-postcomp-is-embᵉ Hᵉ xᵉ =
    map-inv-is-equivᵉ (pr2ᵉ fᵉ (gᵉ xᵉ) (hᵉ xᵉ)) (Hᵉ xᵉ)

  is-section-map-inv-equiv-htpy-postcomp-is-embᵉ :
    (pr1ᵉ fᵉ ·lᵉ_) ∘ᵉ map-inv-equiv-htpy-postcomp-is-embᵉ ~ᵉ idᵉ
  is-section-map-inv-equiv-htpy-postcomp-is-embᵉ Hᵉ =
    eq-htpyᵉ (λ xᵉ →
      is-section-map-inv-is-equivᵉ (pr2ᵉ fᵉ (gᵉ xᵉ) (hᵉ xᵉ)) (Hᵉ xᵉ))

  is-retraction-map-inv-equiv-htpy-postcomp-is-embᵉ :
    map-inv-equiv-htpy-postcomp-is-embᵉ ∘ᵉ (pr1ᵉ fᵉ ·lᵉ_) ~ᵉ idᵉ
  is-retraction-map-inv-equiv-htpy-postcomp-is-embᵉ Hᵉ =
    eq-htpyᵉ (λ xᵉ →
      is-retraction-map-inv-is-equivᵉ (pr2ᵉ fᵉ (gᵉ xᵉ) (hᵉ xᵉ)) (Hᵉ xᵉ))

  equiv-htpy-postcomp-is-embᵉ :
    (gᵉ ~ᵉ hᵉ) ≃ᵉ ((pr1ᵉ fᵉ ∘ᵉ gᵉ) ~ᵉ (pr1ᵉ fᵉ ∘ᵉ hᵉ))
  pr1ᵉ equiv-htpy-postcomp-is-embᵉ = pr1ᵉ fᵉ ·lᵉ_
  pr2ᵉ equiv-htpy-postcomp-is-embᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-equiv-htpy-postcomp-is-embᵉ
      is-section-map-inv-equiv-htpy-postcomp-is-embᵉ
      is-retraction-map-inv-equiv-htpy-postcomp-is-embᵉ
```