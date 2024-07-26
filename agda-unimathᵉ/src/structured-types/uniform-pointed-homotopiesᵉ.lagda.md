# Uniform pointed homotopies

```agda
module structured-types.uniform-pointed-homotopiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-dependent-functionsᵉ
open import structured-types.pointed-families-of-typesᵉ
open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Theᵉ conceptᵉ ofᵉ _uniformᵉ pointedᵉ homotopyᵉ_ isᵉ anᵉ
[equivalent](foundation-core.equivalences.mdᵉ) wayᵉ ofᵉ definingᵉ
[pointedᵉ homotopies](structured-types.pointed-homotopies.md).ᵉ Aᵉ uniformᵉ pointedᵉ
homotopyᵉ `H`ᵉ betweenᵉ twoᵉ
[pointedᵉ dependentᵉ functions](structured-types.pointed-dependent-functions.mdᵉ)
`f`ᵉ andᵉ `g`ᵉ isᵉ definedᵉ to beᵉ aᵉ pointedᵉ dependentᵉ functionᵉ ofᵉ theᵉ
[pointedᵉ typeᵉ family](structured-types.pointed-families-of-types.mdᵉ) ofᵉ
[identifications](foundation-core.identity-types.mdᵉ) betweenᵉ theᵉ valuesᵉ ofᵉ `f`ᵉ
andᵉ `g`.ᵉ Theᵉ mainᵉ ideaᵉ isᵉ that,ᵉ sinceᵉ uniformᵉ pointedᵉ homotopiesᵉ betweenᵉ pointedᵉ
dependentᵉ functionsᵉ areᵉ againᵉ pointedᵉ dependentᵉ functions,ᵉ weᵉ canᵉ easilyᵉ
considerᵉ uniformᵉ pointedᵉ homotopiesᵉ betweenᵉ uniformᵉ pointedᵉ homotopiesᵉ andᵉ soᵉ
on.ᵉ Theᵉ definitionᵉ ofᵉ uniformᵉ pointedᵉ homotopiesᵉ isᵉ uniformᵉ in theᵉ senseᵉ thatᵉ
theyᵉ canᵉ beᵉ iteratedᵉ in thisᵉ way.ᵉ Weᵉ nowᵉ giveᵉ aᵉ moreᵉ detailedᵉ descriptionᵉ ofᵉ theᵉ
definition.ᵉ

Considerᵉ twoᵉ pointedᵉ dependentᵉ functionsᵉ `fᵉ :=ᵉ (f₀ᵉ ,ᵉ f₁)`ᵉ andᵉ `gᵉ :=ᵉ (g₀ᵉ ,ᵉ g₁)`ᵉ
in theᵉ pointedᵉ dependentᵉ functionᵉ typeᵉ `Π∗ᵉ Aᵉ B`.ᵉ Thenᵉ theᵉ typeᵉ familyᵉ
`xᵉ ↦ᵉ f₀ᵉ xᵉ ＝ᵉ g₀ᵉ x`ᵉ overᵉ theᵉ baseᵉ typeᵉ `A`ᵉ isᵉ aᵉ pointedᵉ typeᵉ family,ᵉ where theᵉ
baseᵉ pointᵉ isᵉ theᵉ identificationᵉ

```text
  f₁ᵉ ∙ᵉ invᵉ g₁ᵉ : f₀ᵉ *ᵉ ＝ᵉ g₀ᵉ *.ᵉ
```

Aᵉ {{#conceptᵉ "uniformᵉ pointedᵉ homotopy"ᵉ Agda=uniform-pointed-htpyᵉ}} fromᵉ `f`ᵉ to
`g`ᵉ isᵉ definedᵉ to beᵉ aᵉ
[pointedᵉ dependentᵉ function](structured-types.pointed-dependent-functions.mdᵉ) ofᵉ
theᵉ pointedᵉ typeᵉ familyᵉ `xᵉ ↦ᵉ f₀ᵉ xᵉ ＝ᵉ g₀ᵉ x`.ᵉ Inᵉ otherᵉ words,ᵉ aᵉ pointedᵉ dependentᵉ
functionᵉ consistsᵉ ofᵉ anᵉ unpointedᵉ [homotopy](foundation-core.homotopies.mdᵉ)
`H₀ᵉ : f₀ᵉ ~ᵉ g₀`ᵉ betweenᵉ theᵉ underlyingᵉ dependentᵉ functionsᵉ andᵉ anᵉ identificationᵉ
witnessingᵉ thatᵉ theᵉ triangleᵉ ofᵉ identificationsᵉ

```text
        H₀ᵉ *ᵉ
  f₀ᵉ *ᵉ ------>ᵉ g₀ᵉ *ᵉ
      \ᵉ       ∧ᵉ
    f₁ᵉ \ᵉ     /ᵉ invᵉ g₁ᵉ
        \ᵉ   /ᵉ
         ∨ᵉ /ᵉ
          *ᵉ
```

[commutes](foundation.commuting-triangles-of-identifications.md).ᵉ

Noticeᵉ thatᵉ in comparisonᵉ to theᵉ pointedᵉ homotopies,ᵉ theᵉ identificationᵉ onᵉ theᵉ
rightᵉ in thisᵉ triangleᵉ goesᵉ up,ᵉ in theᵉ inverseᵉ directionᵉ ofᵉ theᵉ identificationᵉ
`g₁`.ᵉ Thisᵉ makesᵉ itᵉ slightlyᵉ moreᵉ complicatedᵉ to constructᵉ anᵉ identificationᵉ
witnessingᵉ thatᵉ theᵉ triangleᵉ commutesᵉ in theᵉ caseᵉ ofᵉ uniformᵉ pointedᵉ homotopies.ᵉ
Furthermore,ᵉ thisᵉ complicationᵉ becomesᵉ moreᵉ significantᵉ andᵉ bothersomeᵉ whenᵉ weᵉ
areᵉ tryingᵉ to constructᵉ aᵉ
[pointedᵉ `2`-homotopy](structured-types.pointed-2-homotopies.md).ᵉ

## Definitions

### Preservation of the base point of unpointed homotopies between pointed maps

Theᵉ underlyingᵉ homotopyᵉ ofᵉ aᵉ uniformᵉ pointedᵉ homotopyᵉ preservesᵉ theᵉ baseᵉ pointᵉ
in theᵉ senseᵉ thatᵉ theᵉ triangleᵉ ofᵉ identificationsᵉ

```text
                      Hᵉ *ᵉ
                fᵉ *ᵉ ------>ᵉ gᵉ *ᵉ
                   \ᵉ       ∧ᵉ
  preserves-pointᵉ fᵉ \ᵉ     /ᵉ invᵉ (preserves-pointᵉ gᵉ)
                     \ᵉ   /ᵉ
                      ∨ᵉ /ᵉ
                       *ᵉ
```

commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  (fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ) (Gᵉ : unpointed-htpy-pointed-Πᵉ fᵉ gᵉ)
  where

  preserves-point-unpointed-htpy-pointed-Πᵉ : UUᵉ l2ᵉ
  preserves-point-unpointed-htpy-pointed-Πᵉ =
    coherence-triangle-identificationsᵉ
      ( Gᵉ (point-Pointed-Typeᵉ Aᵉ))
      ( invᵉ (preserves-point-function-pointed-Πᵉ gᵉ))
      ( preserves-point-function-pointed-Πᵉ fᵉ)

  compute-coherence-point-unpointed-htpy-pointed-Πᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ fᵉ gᵉ Gᵉ ≃ᵉ
    preserves-point-unpointed-htpy-pointed-Πᵉ
  compute-coherence-point-unpointed-htpy-pointed-Πᵉ =
    equiv-transpose-right-coherence-triangle-identificationsᵉ _ _ _

  preserves-point-coherence-point-unpointed-htpy-pointed-Πᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ fᵉ gᵉ Gᵉ →
    preserves-point-unpointed-htpy-pointed-Πᵉ
  preserves-point-coherence-point-unpointed-htpy-pointed-Πᵉ =
    transpose-right-coherence-triangle-identificationsᵉ _ _ _ reflᵉ

  coherence-point-preserves-point-unpointed-htpy-pointed-Πᵉ :
    preserves-point-unpointed-htpy-pointed-Πᵉ →
    coherence-point-unpointed-htpy-pointed-Πᵉ fᵉ gᵉ Gᵉ
  coherence-point-preserves-point-unpointed-htpy-pointed-Πᵉ =
    invᵉ ∘ᵉ inv-right-transpose-eq-concatᵉ _ _ _

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ} (Hᵉ : fᵉ ~∗ᵉ gᵉ)
  where

  preserves-point-pointed-htpyᵉ :
    preserves-point-unpointed-htpy-pointed-Πᵉ fᵉ gᵉ (htpy-pointed-htpyᵉ Hᵉ)
  preserves-point-pointed-htpyᵉ =
    preserves-point-coherence-point-unpointed-htpy-pointed-Πᵉ fᵉ gᵉ
      ( htpy-pointed-htpyᵉ Hᵉ)
      ( coherence-point-pointed-htpyᵉ Hᵉ)
```

### Uniform pointed homotopies

**Note.**ᵉ Theᵉ operationᵉ `htpy-uniform-pointed-htpy`ᵉ thatᵉ convertsᵉ aᵉ uniformᵉ
pointedᵉ homotopyᵉ to anᵉ unpointedᵉ homotopyᵉ isᵉ setᵉ upᵉ with theᵉ pointedᵉ functionsᵉ
asᵉ explicitᵉ arguments,ᵉ becauseᵉ Agdaᵉ hasᵉ troubleᵉ inferringᵉ them.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  (fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ)
  where

  eq-value-Pointed-Famᵉ : Pointed-Famᵉ l2ᵉ Aᵉ
  pr1ᵉ eq-value-Pointed-Famᵉ =
    eq-valueᵉ (function-pointed-Πᵉ fᵉ) (function-pointed-Πᵉ gᵉ)
  pr2ᵉ eq-value-Pointed-Famᵉ =
    ( preserves-point-function-pointed-Πᵉ fᵉ) ∙ᵉ
    ( invᵉ (preserves-point-function-pointed-Πᵉ gᵉ))

  uniform-pointed-htpyᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  uniform-pointed-htpyᵉ = pointed-Πᵉ Aᵉ eq-value-Pointed-Famᵉ

  htpy-uniform-pointed-htpyᵉ :
    uniform-pointed-htpyᵉ → function-pointed-Πᵉ fᵉ ~ᵉ function-pointed-Πᵉ gᵉ
  htpy-uniform-pointed-htpyᵉ = pr1ᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ}
  (Hᵉ : uniform-pointed-htpyᵉ fᵉ gᵉ)
  where

  preserves-point-uniform-pointed-htpyᵉ :
    preserves-point-unpointed-htpy-pointed-Πᵉ fᵉ gᵉ
      ( htpy-uniform-pointed-htpyᵉ fᵉ gᵉ Hᵉ)
  preserves-point-uniform-pointed-htpyᵉ = pr2ᵉ Hᵉ

  coherence-point-uniform-pointed-htpyᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ fᵉ gᵉ
      ( htpy-uniform-pointed-htpyᵉ fᵉ gᵉ Hᵉ)
  coherence-point-uniform-pointed-htpyᵉ =
    coherence-point-preserves-point-unpointed-htpy-pointed-Πᵉ fᵉ gᵉ
      ( htpy-uniform-pointed-htpyᵉ fᵉ gᵉ Hᵉ)
      ( preserves-point-uniform-pointed-htpyᵉ)

  pointed-htpy-uniform-pointed-htpyᵉ : fᵉ ~∗ᵉ gᵉ
  pr1ᵉ pointed-htpy-uniform-pointed-htpyᵉ =
    htpy-uniform-pointed-htpyᵉ fᵉ gᵉ Hᵉ
  pr2ᵉ pointed-htpy-uniform-pointed-htpyᵉ =
    coherence-point-uniform-pointed-htpyᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ}
  where

  make-uniform-pointed-htpyᵉ :
    (Gᵉ : unpointed-htpy-pointed-Πᵉ fᵉ gᵉ) →
    coherence-point-unpointed-htpy-pointed-Πᵉ fᵉ gᵉ Gᵉ →
    uniform-pointed-htpyᵉ fᵉ gᵉ
  pr1ᵉ (make-uniform-pointed-htpyᵉ Gᵉ pᵉ) = Gᵉ
  pr2ᵉ (make-uniform-pointed-htpyᵉ Gᵉ pᵉ) =
    preserves-point-coherence-point-unpointed-htpy-pointed-Πᵉ fᵉ gᵉ Gᵉ pᵉ

  uniform-pointed-htpy-pointed-htpyᵉ : fᵉ ~∗ᵉ gᵉ → uniform-pointed-htpyᵉ fᵉ gᵉ
  pr1ᵉ (uniform-pointed-htpy-pointed-htpyᵉ Hᵉ) = htpy-pointed-htpyᵉ Hᵉ
  pr2ᵉ (uniform-pointed-htpy-pointed-htpyᵉ Hᵉ) = preserves-point-pointed-htpyᵉ Hᵉ

  compute-uniform-pointed-htpyᵉ : (fᵉ ~∗ᵉ gᵉ) ≃ᵉ uniform-pointed-htpyᵉ fᵉ gᵉ
  compute-uniform-pointed-htpyᵉ =
    equiv-totᵉ (compute-coherence-point-unpointed-htpy-pointed-Πᵉ fᵉ gᵉ)
```

### The reflexive uniform pointed homotopy

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  (fᵉ : pointed-Πᵉ Aᵉ Bᵉ)
  where

  refl-uniform-pointed-htpyᵉ : uniform-pointed-htpyᵉ fᵉ fᵉ
  pr1ᵉ refl-uniform-pointed-htpyᵉ = refl-htpyᵉ
  pr2ᵉ refl-uniform-pointed-htpyᵉ =
    invᵉ (right-invᵉ (preserves-point-function-pointed-Πᵉ fᵉ))
```

### Concatenation of uniform pointed homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ hᵉ : pointed-Πᵉ Aᵉ Bᵉ}
  (Gᵉ : uniform-pointed-htpyᵉ fᵉ gᵉ) (Hᵉ : uniform-pointed-htpyᵉ gᵉ hᵉ)
  where

  htpy-concat-uniform-pointed-htpyᵉ : unpointed-htpy-pointed-Πᵉ fᵉ hᵉ
  htpy-concat-uniform-pointed-htpyᵉ =
    htpy-uniform-pointed-htpyᵉ fᵉ gᵉ Gᵉ ∙hᵉ htpy-uniform-pointed-htpyᵉ gᵉ hᵉ Hᵉ

  coherence-point-concat-uniform-pointed-htpyᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ fᵉ hᵉ
      ( htpy-concat-uniform-pointed-htpyᵉ)
  coherence-point-concat-uniform-pointed-htpyᵉ =
    coherence-point-concat-pointed-htpyᵉ
      ( pointed-htpy-uniform-pointed-htpyᵉ Gᵉ)
      ( pointed-htpy-uniform-pointed-htpyᵉ Hᵉ)

  concat-uniform-pointed-htpyᵉ : uniform-pointed-htpyᵉ fᵉ hᵉ
  concat-uniform-pointed-htpyᵉ =
    make-uniform-pointed-htpyᵉ
      ( htpy-concat-uniform-pointed-htpyᵉ)
      ( coherence-point-concat-uniform-pointed-htpyᵉ)
```

### Inverses of uniform pointed homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ} (Hᵉ : uniform-pointed-htpyᵉ fᵉ gᵉ)
  where

  htpy-inv-uniform-pointed-htpyᵉ : unpointed-htpy-pointed-Πᵉ gᵉ fᵉ
  htpy-inv-uniform-pointed-htpyᵉ = inv-htpyᵉ (htpy-uniform-pointed-htpyᵉ fᵉ gᵉ Hᵉ)

  coherence-point-inv-uniform-pointed-htpyᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ gᵉ fᵉ htpy-inv-uniform-pointed-htpyᵉ
  coherence-point-inv-uniform-pointed-htpyᵉ =
    coherence-point-inv-pointed-htpyᵉ
      ( pointed-htpy-uniform-pointed-htpyᵉ Hᵉ)

  inv-uniform-pointed-htpyᵉ : uniform-pointed-htpyᵉ gᵉ fᵉ
  inv-uniform-pointed-htpyᵉ =
    make-uniform-pointed-htpyᵉ
      ( htpy-inv-uniform-pointed-htpyᵉ)
      ( coherence-point-inv-uniform-pointed-htpyᵉ)
```

## Properties

### Extensionality of pointed dependent function types by uniform pointed homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  (fᵉ : pointed-Πᵉ Aᵉ Bᵉ)
  where

  uniform-extensionality-pointed-Πᵉ :
    (gᵉ : pointed-Πᵉ Aᵉ Bᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ uniform-pointed-htpyᵉ fᵉ gᵉ
  uniform-extensionality-pointed-Πᵉ =
    extensionality-Σᵉ
      ( λ {gᵉ} qᵉ Hᵉ →
        Hᵉ (point-Pointed-Typeᵉ Aᵉ) ＝ᵉ
        preserves-point-function-pointed-Πᵉ fᵉ ∙ᵉ
        invᵉ (preserves-point-function-pointed-Πᵉ (gᵉ ,ᵉ qᵉ)))
      ( refl-htpyᵉ)
      ( invᵉ (right-invᵉ (preserves-point-function-pointed-Πᵉ fᵉ)))
      ( λ gᵉ → equiv-funextᵉ)
      ( λ pᵉ →
        ( equiv-right-transpose-eq-concatᵉ
          ( reflᵉ)
          ( pᵉ)
          ( preserves-point-function-pointed-Πᵉ fᵉ)) ∘eᵉ
        ( equiv-invᵉ (preserves-point-function-pointed-Πᵉ fᵉ) pᵉ))

  eq-uniform-pointed-htpyᵉ :
    (gᵉ : pointed-Πᵉ Aᵉ Bᵉ) → uniform-pointed-htpyᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-uniform-pointed-htpyᵉ gᵉ = map-inv-equivᵉ (uniform-extensionality-pointed-Πᵉ gᵉ)
```