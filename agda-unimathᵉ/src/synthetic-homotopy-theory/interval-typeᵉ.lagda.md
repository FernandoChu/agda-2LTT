# The interval

```agda
module synthetic-homotopy-theory.interval-typeᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

**Theᵉ intervalᵉ type**ᵉ isᵉ aᵉ higherᵉ inductive typeᵉ with twoᵉ pointsᵉ andᵉ anᵉ
[identification](foundation.identity-types.mdᵉ) betweenᵉ them.ᵉ

## Postulates

```agda
postulate

  𝕀ᵉ : UUᵉ lzero

  source-𝕀ᵉ : 𝕀ᵉ

  target-𝕀ᵉ : 𝕀ᵉ

  path-𝕀ᵉ : Idᵉ source-𝕀ᵉ target-𝕀ᵉ

  ind-𝕀ᵉ :
    {lᵉ : Level} (Pᵉ : 𝕀ᵉ → UUᵉ lᵉ) (uᵉ : Pᵉ source-𝕀ᵉ) (vᵉ : Pᵉ target-𝕀ᵉ)
    (qᵉ : dependent-identificationᵉ Pᵉ path-𝕀ᵉ uᵉ vᵉ) → (xᵉ : 𝕀ᵉ) → Pᵉ xᵉ

  compute-source-𝕀ᵉ :
    {lᵉ : Level} {Pᵉ : 𝕀ᵉ → UUᵉ lᵉ} (uᵉ : Pᵉ source-𝕀ᵉ) (vᵉ : Pᵉ target-𝕀ᵉ)
    (qᵉ : dependent-identificationᵉ Pᵉ path-𝕀ᵉ uᵉ vᵉ) → Idᵉ (ind-𝕀ᵉ Pᵉ uᵉ vᵉ qᵉ source-𝕀ᵉ) uᵉ

  compute-target-𝕀ᵉ :
    {lᵉ : Level} {Pᵉ : 𝕀ᵉ → UUᵉ lᵉ} (uᵉ : Pᵉ source-𝕀ᵉ) (vᵉ : Pᵉ target-𝕀ᵉ)
    (qᵉ : dependent-identificationᵉ Pᵉ path-𝕀ᵉ uᵉ vᵉ) → Idᵉ (ind-𝕀ᵉ Pᵉ uᵉ vᵉ qᵉ target-𝕀ᵉ) vᵉ

  compute-path-𝕀ᵉ :
    {lᵉ : Level} {Pᵉ : 𝕀ᵉ → UUᵉ lᵉ} (uᵉ : Pᵉ source-𝕀ᵉ) (vᵉ : Pᵉ target-𝕀ᵉ)
    (qᵉ : dependent-identificationᵉ Pᵉ path-𝕀ᵉ uᵉ vᵉ) →
    coherence-square-identificationsᵉ
      ( apᵉ (trᵉ Pᵉ path-𝕀ᵉ) (compute-source-𝕀ᵉ uᵉ vᵉ qᵉ))
      ( apdᵉ (ind-𝕀ᵉ Pᵉ uᵉ vᵉ qᵉ) path-𝕀ᵉ)
      ( qᵉ)
      ( compute-target-𝕀ᵉ uᵉ vᵉ qᵉ)
```

## Properties

### The data that is used to apply the inductiopn principle of the interval

```agda
Data-𝕀ᵉ : {lᵉ : Level} → (𝕀ᵉ → UUᵉ lᵉ) → UUᵉ lᵉ
Data-𝕀ᵉ Pᵉ =
  Σᵉ ( Pᵉ source-𝕀ᵉ)
    ( λ uᵉ →
      Σᵉ ( Pᵉ target-𝕀ᵉ) (dependent-identificationᵉ Pᵉ path-𝕀ᵉ uᵉ))

ev-𝕀ᵉ : {lᵉ : Level} {Pᵉ : 𝕀ᵉ → UUᵉ lᵉ} → ((xᵉ : 𝕀ᵉ) → Pᵉ xᵉ) → Data-𝕀ᵉ Pᵉ
ev-𝕀ᵉ fᵉ = tripleᵉ (fᵉ source-𝕀ᵉ) (fᵉ target-𝕀ᵉ) (apdᵉ fᵉ path-𝕀ᵉ)

module _
  {lᵉ : Level} {Pᵉ : 𝕀ᵉ → UUᵉ lᵉ}
  where

  Eq-Data-𝕀ᵉ : (xᵉ yᵉ : Data-𝕀ᵉ Pᵉ) → UUᵉ lᵉ
  Eq-Data-𝕀ᵉ xᵉ yᵉ =
    Σᵉ ( pr1ᵉ xᵉ ＝ᵉ pr1ᵉ yᵉ)
      ( λ αᵉ →
        Σᵉ ( pr1ᵉ (pr2ᵉ xᵉ) ＝ᵉ pr1ᵉ (pr2ᵉ yᵉ))
          ( λ βᵉ →
            coherence-square-identificationsᵉ
              ( apᵉ (trᵉ Pᵉ path-𝕀ᵉ) αᵉ)
              ( pr2ᵉ (pr2ᵉ xᵉ))
              ( pr2ᵉ (pr2ᵉ yᵉ))
              ( βᵉ)))

  extensionality-Data-𝕀ᵉ : (xᵉ yᵉ : Data-𝕀ᵉ Pᵉ) → Idᵉ xᵉ yᵉ ≃ᵉ Eq-Data-𝕀ᵉ xᵉ yᵉ
  extensionality-Data-𝕀ᵉ (pairᵉ uᵉ (pairᵉ vᵉ αᵉ)) =
    extensionality-Σᵉ
      ( λ {u'ᵉ} vα'ᵉ pᵉ →
        Σᵉ ( vᵉ ＝ᵉ pr1ᵉ vα'ᵉ)
          ( λ qᵉ →
            coherence-square-identificationsᵉ
              ( apᵉ (trᵉ Pᵉ path-𝕀ᵉ) pᵉ)
              ( αᵉ)
              ( pr2ᵉ vα'ᵉ)
              ( qᵉ)))
      ( reflᵉ)
      ( pairᵉ reflᵉ right-unitᵉ)
      ( λ u'ᵉ → id-equivᵉ)
      ( extensionality-Σᵉ
        ( λ {v'ᵉ} α'ᵉ qᵉ → Idᵉ (αᵉ ∙ᵉ qᵉ) α'ᵉ)
        ( reflᵉ)
        ( right-unitᵉ)
        ( λ v'ᵉ → id-equivᵉ)
        ( λ γᵉ → equiv-concatᵉ right-unitᵉ γᵉ))

  refl-Eq-Data-𝕀ᵉ : (xᵉ : Data-𝕀ᵉ Pᵉ) → Eq-Data-𝕀ᵉ xᵉ xᵉ
  refl-Eq-Data-𝕀ᵉ xᵉ = tripleᵉ reflᵉ reflᵉ right-unitᵉ

  Eq-eq-Data-𝕀ᵉ : {xᵉ yᵉ : Data-𝕀ᵉ Pᵉ} → Idᵉ xᵉ yᵉ → Eq-Data-𝕀ᵉ xᵉ yᵉ
  Eq-eq-Data-𝕀ᵉ {xᵉ = xᵉ} reflᵉ = refl-Eq-Data-𝕀ᵉ xᵉ

  eq-Eq-Data-𝕀'ᵉ : {xᵉ yᵉ : Data-𝕀ᵉ Pᵉ} → Eq-Data-𝕀ᵉ xᵉ yᵉ → Idᵉ xᵉ yᵉ
  eq-Eq-Data-𝕀'ᵉ {xᵉ} {yᵉ} = map-inv-equivᵉ (extensionality-Data-𝕀ᵉ xᵉ yᵉ)

  eq-Eq-Data-𝕀ᵉ :
    {xᵉ yᵉ : Data-𝕀ᵉ Pᵉ} (αᵉ : pr1ᵉ xᵉ ＝ᵉ pr1ᵉ yᵉ) (βᵉ : pr1ᵉ (pr2ᵉ xᵉ) ＝ᵉ pr1ᵉ (pr2ᵉ yᵉ))
    (γᵉ :
      coherence-square-identificationsᵉ
        ( apᵉ (trᵉ Pᵉ path-𝕀ᵉ) αᵉ)
        ( pr2ᵉ (pr2ᵉ xᵉ))
        ( pr2ᵉ (pr2ᵉ yᵉ))
        ( βᵉ)) →
    xᵉ ＝ᵉ yᵉ
  eq-Eq-Data-𝕀ᵉ αᵉ βᵉ γᵉ = eq-Eq-Data-𝕀'ᵉ (tripleᵉ αᵉ βᵉ γᵉ)
```

### The interval is contractible

```agda
inv-ev-𝕀ᵉ : {lᵉ : Level} {Pᵉ : 𝕀ᵉ → UUᵉ lᵉ} → Data-𝕀ᵉ Pᵉ → (xᵉ : 𝕀ᵉ) → Pᵉ xᵉ
inv-ev-𝕀ᵉ xᵉ = ind-𝕀ᵉ _ (pr1ᵉ xᵉ) (pr1ᵉ (pr2ᵉ xᵉ)) (pr2ᵉ (pr2ᵉ xᵉ))

is-section-inv-ev-𝕀ᵉ :
  {lᵉ : Level} {Pᵉ : 𝕀ᵉ → UUᵉ lᵉ} (xᵉ : Data-𝕀ᵉ Pᵉ) → ev-𝕀ᵉ (inv-ev-𝕀ᵉ xᵉ) ＝ᵉ xᵉ
is-section-inv-ev-𝕀ᵉ (pairᵉ uᵉ (pairᵉ vᵉ qᵉ)) =
  eq-Eq-Data-𝕀ᵉ
    ( compute-source-𝕀ᵉ uᵉ vᵉ qᵉ)
    ( compute-target-𝕀ᵉ uᵉ vᵉ qᵉ)
    ( compute-path-𝕀ᵉ uᵉ vᵉ qᵉ)

tr-valueᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) {xᵉ yᵉ : Aᵉ}
  (pᵉ : Idᵉ xᵉ yᵉ) (qᵉ : Idᵉ (fᵉ xᵉ) (gᵉ xᵉ)) (rᵉ : Idᵉ (fᵉ yᵉ) (gᵉ yᵉ)) →
  Idᵉ (apdᵉ fᵉ pᵉ ∙ᵉ rᵉ) (apᵉ (trᵉ Bᵉ pᵉ) qᵉ ∙ᵉ apdᵉ gᵉ pᵉ) →
  Idᵉ (trᵉ (λ xᵉ → Idᵉ (fᵉ xᵉ) (gᵉ xᵉ)) pᵉ qᵉ) rᵉ
tr-valueᵉ fᵉ gᵉ reflᵉ qᵉ rᵉ sᵉ = (invᵉ (ap-idᵉ qᵉ) ∙ᵉ invᵉ right-unitᵉ) ∙ᵉ invᵉ sᵉ

is-retraction-inv-ev-𝕀ᵉ :
  {lᵉ : Level} {Pᵉ : 𝕀ᵉ → UUᵉ lᵉ} (fᵉ : (xᵉ : 𝕀ᵉ) → Pᵉ xᵉ) → Idᵉ (inv-ev-𝕀ᵉ (ev-𝕀ᵉ fᵉ)) fᵉ
is-retraction-inv-ev-𝕀ᵉ {lᵉ} {Pᵉ} fᵉ =
  eq-htpyᵉ
    ( ind-𝕀ᵉ
      ( eq-valueᵉ (inv-ev-𝕀ᵉ (ev-𝕀ᵉ fᵉ)) fᵉ)
      ( compute-source-𝕀ᵉ (fᵉ source-𝕀ᵉ) (fᵉ target-𝕀ᵉ) (apdᵉ fᵉ path-𝕀ᵉ))
      ( compute-target-𝕀ᵉ (fᵉ source-𝕀ᵉ) (fᵉ target-𝕀ᵉ) (apdᵉ fᵉ path-𝕀ᵉ))
      ( map-compute-dependent-identification-eq-valueᵉ
        ( inv-ev-𝕀ᵉ (ev-𝕀ᵉ fᵉ))
        ( fᵉ)
        ( path-𝕀ᵉ)
        ( compute-source-𝕀ᵉ (fᵉ source-𝕀ᵉ) (fᵉ target-𝕀ᵉ) (apdᵉ fᵉ path-𝕀ᵉ))
        ( compute-target-𝕀ᵉ (fᵉ source-𝕀ᵉ) (fᵉ target-𝕀ᵉ) (apdᵉ fᵉ path-𝕀ᵉ))
        ( compute-path-𝕀ᵉ (fᵉ source-𝕀ᵉ) (fᵉ target-𝕀ᵉ) (apdᵉ fᵉ path-𝕀ᵉ))))

abstract
  is-equiv-ev-𝕀ᵉ :
    {lᵉ : Level} (Pᵉ : 𝕀ᵉ → UUᵉ lᵉ) → is-equivᵉ (ev-𝕀ᵉ {Pᵉ = Pᵉ})
  is-equiv-ev-𝕀ᵉ Pᵉ =
    is-equiv-is-invertibleᵉ inv-ev-𝕀ᵉ is-section-inv-ev-𝕀ᵉ is-retraction-inv-ev-𝕀ᵉ

contraction-𝕀ᵉ : (xᵉ : 𝕀ᵉ) → Idᵉ source-𝕀ᵉ xᵉ
contraction-𝕀ᵉ =
  ind-𝕀ᵉ
    ( Idᵉ source-𝕀ᵉ)
    ( reflᵉ)
    ( path-𝕀ᵉ)
    ( tr-Id-rightᵉ path-𝕀ᵉ reflᵉ)

abstract
  is-contr-𝕀ᵉ : is-contrᵉ 𝕀ᵉ
  pr1ᵉ is-contr-𝕀ᵉ = source-𝕀ᵉ
  pr2ᵉ is-contr-𝕀ᵉ = contraction-𝕀ᵉ
```