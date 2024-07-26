# Pointed homotopies

```agda
module structured-types.pointed-homotopiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functionsᵉ
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.commuting-triangles-of-identificationsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.path-algebraᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import foundation-core.torsorial-type-familiesᵉ

open import structured-types.pointed-dependent-functionsᵉ
open import structured-types.pointed-families-of-typesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "pointedᵉ homotopy"ᵉ Agda=_~∗ᵉ_}} betweenᵉ
[pointedᵉ dependentᵉ functions](structured-types.pointed-dependent-functions.mdᵉ)
`fᵉ :=ᵉ (f₀ᵉ ,ᵉ f₁)`ᵉ andᵉ `gᵉ :=ᵉ (g₀ᵉ ,ᵉ g₁)`ᵉ ofᵉ typeᵉ `pointed-Πᵉ Aᵉ B`ᵉ consistsᵉ ofᵉ anᵉ
unpointedᵉ [homotopy](foundation-core.homotopies.mdᵉ) `H₀ᵉ : f₀ᵉ ~ᵉ g₀`ᵉ andᵉ anᵉ
[identification](foundation-core.identity-types.mdᵉ) `H₁ᵉ : f₁ᵉ ＝ᵉ (H₀ᵉ *ᵉ) ∙ᵉ g₁`ᵉ
witnessingᵉ thatᵉ theᵉ triangleᵉ ofᵉ identificationsᵉ

```text
        H₀ᵉ *ᵉ
  f₀ᵉ *ᵉ ------>ᵉ g₀ᵉ *ᵉ
      \ᵉ       /ᵉ
    f₁ᵉ \ᵉ     /ᵉ g₁ᵉ
        \ᵉ   /ᵉ
         ∨ᵉ ∨ᵉ
          *ᵉ
```

[commutes](foundation.commuting-triangles-of-identifications.md).ᵉ Thisᵉ
identificationᵉ isᵉ calledᵉ theᵉ
{{#conceptᵉ "baseᵉ pointᵉ coherence"ᵉ Disambiguation="pointedᵉ homotopy"ᵉ Agda=coherence-point-unpointed-htpy-pointed-Πᵉ}}
ofᵉ theᵉ pointedᵉ homotopyᵉ `Hᵉ :=ᵉ (H₀ᵉ ,ᵉ H₁)`.ᵉ

Anᵉ equivalentᵉ wayᵉ ofᵉ definingᵉ pointedᵉ homotopiesᵉ occursᵉ whenᵉ weᵉ considerᵉ theᵉ
typeᵉ familyᵉ `xᵉ ↦ᵉ f₀ᵉ xᵉ ＝ᵉ g₀ᵉ x`ᵉ overᵉ theᵉ baseᵉ typeᵉ `A`.ᵉ Thisᵉ isᵉ aᵉ
[pointedᵉ typeᵉ family](structured-types.pointed-families-of-types.md),ᵉ where theᵉ
baseᵉ pointᵉ isᵉ theᵉ identificationᵉ

```text
  f₁ᵉ ∙ᵉ invᵉ g₁ᵉ : f₀ᵉ *ᵉ ＝ᵉ g₀ᵉ *.ᵉ
```

Aᵉ pointedᵉ homotopyᵉ `fᵉ ~∗ᵉ g`ᵉ isᵉ thereforeᵉ equivalentlyᵉ definedᵉ asᵉ aᵉ pointedᵉ
dependentᵉ functionᵉ ofᵉ theᵉ pointedᵉ typeᵉ familyᵉ `xᵉ ↦ᵉ f₀ᵉ xᵉ ＝ᵉ g₀ᵉ x`.ᵉ Suchᵉ aᵉ pointedᵉ
dependentᵉ functionᵉ consistsᵉ ofᵉ anᵉ unpointedᵉ homotopyᵉ `H₀ᵉ : f₀ᵉ ~ᵉ g₀`ᵉ betweenᵉ theᵉ
underlyingᵉ dependentᵉ functionsᵉ andᵉ anᵉ identificationᵉ witnessingᵉ thatᵉ theᵉ
triangleᵉ ofᵉ identificationsᵉ

```text
        H₀ᵉ *ᵉ
  f₀ᵉ *ᵉ ------>ᵉ g₀ᵉ *ᵉ
      \ᵉ       ∧ᵉ
    f₁ᵉ \ᵉ     /ᵉ invᵉ g₁ᵉ
        \ᵉ   /ᵉ
         ∨ᵉ /ᵉ
          *ᵉ
```

[commutes](foundation.commuting-triangles-of-identifications.md).ᵉ Noticeᵉ thatᵉ
theᵉ identificationᵉ onᵉ theᵉ rightᵉ in thisᵉ triangleᵉ goesᵉ up,ᵉ in theᵉ inverseᵉ
directionᵉ ofᵉ theᵉ identificationᵉ `g₁`.ᵉ

Noteᵉ thatᵉ in thisᵉ secondᵉ definitionᵉ ofᵉ pointedᵉ homotopiesᵉ weᵉ definedᵉ pointedᵉ
homotopiesᵉ betweenᵉ pointedᵉ dependentᵉ functionsᵉ to beᵉ certainᵉ pointedᵉ dependentᵉ
functions.ᵉ Thisᵉ impliesᵉ thatᵉ theᵉ secondᵉ definitionᵉ isᵉ aᵉ uniformᵉ definitionᵉ thatᵉ
canᵉ easilyᵉ beᵉ iteratedᵉ in orderᵉ to considerᵉ pointedᵉ higherᵉ homotopies.ᵉ Forᵉ thisᵉ
reason,ᵉ weᵉ callᵉ theᵉ secondᵉ definitionᵉ ofᵉ pointedᵉ homotopiesᵉ
[uniformᵉ pointedᵉ homotopies](structured-types.uniform-pointed-homotopies.md).ᵉ

Noteᵉ thatᵉ theᵉ differenceᵉ betweenᵉ ourᵉ mainᵉ definitionᵉ ofᵉ pointedᵉ homotopiesᵉ andᵉ
theᵉ uniformᵉ definitionᵉ ofᵉ pointedᵉ homotopiesᵉ isᵉ theᵉ directionᵉ ofᵉ theᵉ
identificationᵉ onᵉ theᵉ rightᵉ in theᵉ commutingᵉ triangleᵉ

```text
        H₀ᵉ *ᵉ
  f₀ᵉ *ᵉ ------>ᵉ g₀ᵉ *ᵉ
      \ᵉ       /ᵉ
    f₁ᵉ \ᵉ     /ᵉ g₁ᵉ
        \ᵉ   /ᵉ
         ∨ᵉ ∨ᵉ
          *.ᵉ
```

Inᵉ theᵉ definitionᵉ ofᵉ uniformᵉ pointedᵉ homotopiesᵉ itᵉ goesᵉ in theᵉ reverseᵉ
direction.ᵉ Thisᵉ makesᵉ itᵉ slightlyᵉ moreᵉ complicatedᵉ to constructᵉ anᵉ
identificationᵉ witnessingᵉ thatᵉ theᵉ triangleᵉ commutesᵉ in theᵉ caseᵉ ofᵉ uniformᵉ
pointedᵉ homotopies.ᵉ Furthermore,ᵉ thisᵉ complicationᵉ becomesᵉ moreᵉ significantᵉ andᵉ
bothersomeᵉ whenᵉ weᵉ areᵉ tryingᵉ to constructᵉ aᵉ
[pointedᵉ `2`-homotopy](structured-types.pointed-2-homotopies.md).ᵉ Forᵉ thisᵉ
reason,ᵉ ourᵉ firstᵉ definitionᵉ where pointedᵉ homotopiesᵉ areᵉ definedᵉ to consistᵉ ofᵉ
unpointedᵉ homotopiesᵉ andᵉ aᵉ baseᵉ pointᵉ coherence,ᵉ isᵉ takenᵉ to beᵉ ourᵉ mainᵉ
definitionᵉ ofᵉ pointedᵉ homotopy.ᵉ Theᵉ onlyᵉ disadvantageᵉ ofᵉ theᵉ nonuniformᵉ
definitionᵉ ofᵉ pointedᵉ homotopiesᵉ isᵉ thatᵉ itᵉ doesᵉ notᵉ easilyᵉ iterate.ᵉ

Weᵉ willᵉ writeᵉ `fᵉ ~∗ᵉ g`ᵉ forᵉ theᵉ typeᵉ ofᵉ (nonuniformᵉ) pointedᵉ homotopies,ᵉ andᵉ weᵉ
willᵉ writeᵉ `Hᵉ ~²∗ᵉ K`ᵉ forᵉ theᵉ nonuniformᵉ definitionᵉ ofᵉ pointedᵉ `2`-homotopies.ᵉ

## Definitions

### Unpointed homotopies between pointed dependent functions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  (fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ)
  where

  unpointed-htpy-pointed-Πᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  unpointed-htpy-pointed-Πᵉ = function-pointed-Πᵉ fᵉ ~ᵉ function-pointed-Πᵉ gᵉ
```

### Unpointed homotopies between pointed maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  (fᵉ gᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  unpointed-htpy-pointed-mapᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  unpointed-htpy-pointed-mapᵉ = map-pointed-mapᵉ fᵉ ~ᵉ map-pointed-mapᵉ gᵉ
```

### The base point coherence of unpointed homotopies between pointed maps

Theᵉ baseᵉ pointᵉ coherenceᵉ ofᵉ pointedᵉ homotopiesᵉ assertsᵉ thatᵉ itsᵉ underlyingᵉ
homotopyᵉ preservesᵉ theᵉ baseᵉ point,ᵉ in theᵉ senseᵉ thatᵉ theᵉ triangleᵉ ofᵉ
identificationsᵉ

```text
                      Hᵉ *ᵉ
                fᵉ *ᵉ ------>ᵉ gᵉ *ᵉ
                   \ᵉ       /ᵉ
  preserves-pointᵉ fᵉ \ᵉ     /ᵉ preserves-pointᵉ gᵉ
                     \ᵉ   /ᵉ
                      ∨ᵉ ∨ᵉ
                       *ᵉ
```

commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  (fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ) (Gᵉ : unpointed-htpy-pointed-Πᵉ fᵉ gᵉ)
  where

  coherence-point-unpointed-htpy-pointed-Πᵉ : UUᵉ l2ᵉ
  coherence-point-unpointed-htpy-pointed-Πᵉ =
    coherence-triangle-identificationsᵉ
      ( preserves-point-function-pointed-Πᵉ fᵉ)
      ( preserves-point-function-pointed-Πᵉ gᵉ)
      ( Gᵉ (point-Pointed-Typeᵉ Aᵉ))
```

### Pointed homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  (fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ)
  where

  pointed-htpyᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  pointed-htpyᵉ =
    Σᵉ ( function-pointed-Πᵉ fᵉ ~ᵉ function-pointed-Πᵉ gᵉ)
      ( coherence-point-unpointed-htpy-pointed-Πᵉ fᵉ gᵉ)

  infix 6 _~∗ᵉ_

  _~∗ᵉ_ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  _~∗ᵉ_ = pointed-htpyᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ} (Hᵉ : fᵉ ~∗ᵉ gᵉ)
  where

  htpy-pointed-htpyᵉ : function-pointed-Πᵉ fᵉ ~ᵉ function-pointed-Πᵉ gᵉ
  htpy-pointed-htpyᵉ = pr1ᵉ Hᵉ

  coherence-point-pointed-htpyᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ fᵉ gᵉ htpy-pointed-htpyᵉ
  coherence-point-pointed-htpyᵉ = pr2ᵉ Hᵉ
```

### The reflexive pointed homotopy

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  (fᵉ : pointed-Πᵉ Aᵉ Bᵉ)
  where

  refl-pointed-htpyᵉ : pointed-htpyᵉ fᵉ fᵉ
  pr1ᵉ refl-pointed-htpyᵉ = refl-htpyᵉ
  pr2ᵉ refl-pointed-htpyᵉ = reflᵉ
```

### Concatenation of pointed homotopies

Considerᵉ threeᵉ pointedᵉ dependentᵉ functionsᵉ `fᵉ :=ᵉ (f₀ᵉ ,ᵉ f₁)`,ᵉ `gᵉ :=ᵉ (g₀ᵉ ,ᵉ g₁)`,ᵉ
andᵉ `hᵉ :=ᵉ (h₀ᵉ ,ᵉ h₁)`,ᵉ andᵉ pointedᵉ homotopiesᵉ `Gᵉ :=ᵉ (G₀ᵉ ,ᵉ G₁)`ᵉ andᵉ
`Hᵉ :=ᵉ (H₀ᵉ ,ᵉ H₁)`ᵉ betweenᵉ themᵉ asᵉ indicatedᵉ in theᵉ diagramᵉ

```text
      Gᵉ        Hᵉ
  fᵉ ----->ᵉ gᵉ ----->ᵉ hᵉ
```

Theᵉ concatenationᵉ `(Gᵉ ∙hᵉ H)`ᵉ ofᵉ `G`ᵉ andᵉ `H`ᵉ hasᵉ underlyingᵉ unpointedᵉ homotopyᵉ

```text
  (Gᵉ ∙hᵉ H)₀ᵉ :=ᵉ G₀ᵉ ∙hᵉ H₀.ᵉ
```

Theᵉ baseᵉ pointᵉ coherenceᵉ `(Gᵉ ∙hᵉ H)₁`ᵉ ofᵉ `(Gᵉ ∙hᵉ H)`ᵉ isᵉ obtainedᵉ byᵉ horizontallyᵉ
pastingᵉ theᵉ commutingᵉ trianglesᵉ ofᵉ identificationsᵉ

```text
      G₀ᵉ *ᵉ      H₀ᵉ *ᵉ
  f₀ᵉ *ᵉ -->ᵉ g₀ᵉ *ᵉ --->ᵉ h₀ᵉ *ᵉ
      \ᵉ      |      /ᵉ
       \ᵉ     | g₁ᵉ  /ᵉ
     f₁ᵉ \ᵉ    |    /ᵉ h₁ᵉ
         \ᵉ   |   /ᵉ
          \ᵉ  |  /ᵉ
           ∨ᵉ ∨ᵉ ∨ᵉ
             *.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ hᵉ : pointed-Πᵉ Aᵉ Bᵉ} (Gᵉ : fᵉ ~∗ᵉ gᵉ) (Hᵉ : gᵉ ~∗ᵉ hᵉ)
  where

  htpy-concat-pointed-htpyᵉ : unpointed-htpy-pointed-Πᵉ fᵉ hᵉ
  htpy-concat-pointed-htpyᵉ = htpy-pointed-htpyᵉ Gᵉ ∙hᵉ htpy-pointed-htpyᵉ Hᵉ

  coherence-point-concat-pointed-htpyᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ fᵉ hᵉ htpy-concat-pointed-htpyᵉ
  coherence-point-concat-pointed-htpyᵉ =
    horizontal-pasting-coherence-triangle-identificationsᵉ
      ( preserves-point-function-pointed-Πᵉ fᵉ)
      ( preserves-point-function-pointed-Πᵉ gᵉ)
      ( preserves-point-function-pointed-Πᵉ hᵉ)
      ( htpy-pointed-htpyᵉ Gᵉ (point-Pointed-Typeᵉ Aᵉ))
      ( htpy-pointed-htpyᵉ Hᵉ (point-Pointed-Typeᵉ Aᵉ))
      ( coherence-point-pointed-htpyᵉ Gᵉ)
      ( coherence-point-pointed-htpyᵉ Hᵉ)

  concat-pointed-htpyᵉ : fᵉ ~∗ᵉ hᵉ
  pr1ᵉ concat-pointed-htpyᵉ = htpy-concat-pointed-htpyᵉ
  pr2ᵉ concat-pointed-htpyᵉ = coherence-point-concat-pointed-htpyᵉ
```

### Inverses of pointed homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ} (Hᵉ : fᵉ ~∗ᵉ gᵉ)
  where

  htpy-inv-pointed-htpyᵉ : unpointed-htpy-pointed-Πᵉ gᵉ fᵉ
  htpy-inv-pointed-htpyᵉ = inv-htpyᵉ (htpy-pointed-htpyᵉ Hᵉ)

  coherence-point-inv-pointed-htpyᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ gᵉ fᵉ htpy-inv-pointed-htpyᵉ
  coherence-point-inv-pointed-htpyᵉ =
    transpose-top-coherence-triangle-identificationsᵉ
      ( preserves-point-function-pointed-Πᵉ gᵉ)
      ( preserves-point-function-pointed-Πᵉ fᵉ)
      ( htpy-pointed-htpyᵉ Hᵉ (point-Pointed-Typeᵉ Aᵉ))
      ( reflᵉ)
      ( coherence-point-pointed-htpyᵉ Hᵉ)

  inv-pointed-htpyᵉ : gᵉ ~∗ᵉ fᵉ
  pr1ᵉ inv-pointed-htpyᵉ = htpy-inv-pointed-htpyᵉ
  pr2ᵉ inv-pointed-htpyᵉ = coherence-point-inv-pointed-htpyᵉ
```

## Properties

### Extensionality of pointed dependent function types by pointed homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  (fᵉ : pointed-Πᵉ Aᵉ Bᵉ)
  where

  abstract
    is-torsorial-pointed-htpyᵉ :
      is-torsorialᵉ (pointed-htpyᵉ fᵉ)
    is-torsorial-pointed-htpyᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpyᵉ _)
        ( function-pointed-Πᵉ fᵉ ,ᵉ refl-htpyᵉ)
        ( is-torsorial-Idᵉ _)

  pointed-htpy-eqᵉ :
    (gᵉ : pointed-Πᵉ Aᵉ Bᵉ) → fᵉ ＝ᵉ gᵉ → fᵉ ~∗ᵉ gᵉ
  pointed-htpy-eqᵉ .fᵉ reflᵉ = refl-pointed-htpyᵉ fᵉ

  abstract
    is-equiv-pointed-htpy-eqᵉ :
      (gᵉ : pointed-Πᵉ Aᵉ Bᵉ) → is-equivᵉ (pointed-htpy-eqᵉ gᵉ)
    is-equiv-pointed-htpy-eqᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-pointed-htpyᵉ)
        ( pointed-htpy-eqᵉ)

  extensionality-pointed-Πᵉ :
    (gᵉ : pointed-Πᵉ Aᵉ Bᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ (fᵉ ~∗ᵉ gᵉ)
  pr1ᵉ (extensionality-pointed-Πᵉ gᵉ) = pointed-htpy-eqᵉ gᵉ
  pr2ᵉ (extensionality-pointed-Πᵉ gᵉ) = is-equiv-pointed-htpy-eqᵉ gᵉ

  eq-pointed-htpyᵉ :
    (gᵉ : pointed-Πᵉ Aᵉ Bᵉ) → fᵉ ~∗ᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-pointed-htpyᵉ gᵉ = map-inv-equivᵉ (extensionality-pointed-Πᵉ gᵉ)
```

### Extensionality of pointed maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  extensionality-pointed-mapᵉ :
    (gᵉ : Aᵉ →∗ᵉ Bᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ (fᵉ ~∗ᵉ gᵉ)
  extensionality-pointed-mapᵉ = extensionality-pointed-Πᵉ fᵉ
```

### Associativity of composition of pointed maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {Cᵉ : Pointed-Typeᵉ l3ᵉ} {Dᵉ : Pointed-Typeᵉ l4ᵉ}
  (hᵉ : Cᵉ →∗ᵉ Dᵉ) (gᵉ : Bᵉ →∗ᵉ Cᵉ) (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  htpy-inv-associative-comp-pointed-mapᵉ :
    unpointed-htpy-pointed-Πᵉ (hᵉ ∘∗ᵉ (gᵉ ∘∗ᵉ fᵉ)) ((hᵉ ∘∗ᵉ gᵉ) ∘∗ᵉ fᵉ)
  htpy-inv-associative-comp-pointed-mapᵉ = refl-htpyᵉ

  coherence-point-inv-associative-comp-pointed-mapᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ
      ( hᵉ ∘∗ᵉ (gᵉ ∘∗ᵉ fᵉ))
      ( (hᵉ ∘∗ᵉ gᵉ) ∘∗ᵉ fᵉ)
      ( htpy-inv-associative-comp-pointed-mapᵉ)
  coherence-point-inv-associative-comp-pointed-mapᵉ =
    right-whisker-concat-coherence-triangle-identificationsᵉ
      ( apᵉ
        ( map-pointed-mapᵉ hᵉ)
        ( ( apᵉ
            ( map-pointed-mapᵉ gᵉ)
            ( preserves-point-pointed-mapᵉ fᵉ)) ∙ᵉ
          ( preserves-point-pointed-mapᵉ gᵉ)))
      ( apᵉ (map-pointed-mapᵉ hᵉ) _)
      ( apᵉ (map-comp-pointed-mapᵉ hᵉ gᵉ) (preserves-point-pointed-mapᵉ fᵉ))
      ( preserves-point-pointed-mapᵉ hᵉ)
      ( ( ap-concatᵉ
          ( map-pointed-mapᵉ hᵉ)
          ( apᵉ (map-pointed-mapᵉ gᵉ) (preserves-point-pointed-mapᵉ fᵉ))
          ( preserves-point-pointed-mapᵉ gᵉ)) ∙ᵉ
        ( invᵉ
          ( right-whisker-concatᵉ
            ( ap-compᵉ
              ( map-pointed-mapᵉ hᵉ)
              ( map-pointed-mapᵉ gᵉ)
              ( preserves-point-pointed-mapᵉ fᵉ))
            ( apᵉ (map-pointed-mapᵉ hᵉ) (preserves-point-pointed-mapᵉ gᵉ)))))

  inv-associative-comp-pointed-mapᵉ :
    hᵉ ∘∗ᵉ (gᵉ ∘∗ᵉ fᵉ) ~∗ᵉ (hᵉ ∘∗ᵉ gᵉ) ∘∗ᵉ fᵉ
  pr1ᵉ inv-associative-comp-pointed-mapᵉ =
    htpy-inv-associative-comp-pointed-mapᵉ
  pr2ᵉ inv-associative-comp-pointed-mapᵉ =
    coherence-point-inv-associative-comp-pointed-mapᵉ

  htpy-associative-comp-pointed-mapᵉ :
    unpointed-htpy-pointed-Πᵉ ((hᵉ ∘∗ᵉ gᵉ) ∘∗ᵉ fᵉ) (hᵉ ∘∗ᵉ (gᵉ ∘∗ᵉ fᵉ))
  htpy-associative-comp-pointed-mapᵉ = refl-htpyᵉ

  coherence-associative-comp-pointed-mapᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ
      ( (hᵉ ∘∗ᵉ gᵉ) ∘∗ᵉ fᵉ)
      ( hᵉ ∘∗ᵉ (gᵉ ∘∗ᵉ fᵉ))
      ( htpy-associative-comp-pointed-mapᵉ)
  coherence-associative-comp-pointed-mapᵉ =
    invᵉ coherence-point-inv-associative-comp-pointed-mapᵉ

  associative-comp-pointed-mapᵉ :
    (hᵉ ∘∗ᵉ gᵉ) ∘∗ᵉ fᵉ ~∗ᵉ hᵉ ∘∗ᵉ (gᵉ ∘∗ᵉ fᵉ)
  pr1ᵉ associative-comp-pointed-mapᵉ =
    htpy-associative-comp-pointed-mapᵉ
  pr2ᵉ associative-comp-pointed-mapᵉ =
    coherence-associative-comp-pointed-mapᵉ
```

### The left unit law for composition of pointed maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  htpy-left-unit-law-comp-pointed-mapᵉ :
    idᵉ ∘ᵉ map-pointed-mapᵉ fᵉ ~ᵉ map-pointed-mapᵉ fᵉ
  htpy-left-unit-law-comp-pointed-mapᵉ = refl-htpyᵉ

  coherence-left-unit-law-comp-pointed-mapᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ
      ( id-pointed-mapᵉ ∘∗ᵉ fᵉ)
      ( fᵉ)
      ( htpy-left-unit-law-comp-pointed-mapᵉ)
  coherence-left-unit-law-comp-pointed-mapᵉ =
    right-unitᵉ ∙ᵉ ap-idᵉ (preserves-point-pointed-mapᵉ fᵉ)

  left-unit-law-comp-pointed-mapᵉ : id-pointed-mapᵉ ∘∗ᵉ fᵉ ~∗ᵉ fᵉ
  pr1ᵉ left-unit-law-comp-pointed-mapᵉ = htpy-left-unit-law-comp-pointed-mapᵉ
  pr2ᵉ left-unit-law-comp-pointed-mapᵉ = coherence-left-unit-law-comp-pointed-mapᵉ

  htpy-inv-left-unit-law-comp-pointed-mapᵉ :
    map-pointed-mapᵉ fᵉ ~ᵉ idᵉ ∘ᵉ map-pointed-mapᵉ fᵉ
  htpy-inv-left-unit-law-comp-pointed-mapᵉ = refl-htpyᵉ

  coherence-point-inv-left-unit-law-comp-pointed-mapᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ
      ( fᵉ)
      ( id-pointed-mapᵉ ∘∗ᵉ fᵉ)
      ( htpy-inv-left-unit-law-comp-pointed-mapᵉ)
  coherence-point-inv-left-unit-law-comp-pointed-mapᵉ =
    invᵉ coherence-left-unit-law-comp-pointed-mapᵉ

  inv-left-unit-law-comp-pointed-mapᵉ : fᵉ ~∗ᵉ id-pointed-mapᵉ ∘∗ᵉ fᵉ
  pr1ᵉ inv-left-unit-law-comp-pointed-mapᵉ =
    htpy-inv-left-unit-law-comp-pointed-mapᵉ
  pr2ᵉ inv-left-unit-law-comp-pointed-mapᵉ =
    coherence-point-inv-left-unit-law-comp-pointed-mapᵉ
```

### The right unit law for composition of pointed maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  htpy-right-unit-law-comp-pointed-mapᵉ :
    map-pointed-mapᵉ fᵉ ∘ᵉ idᵉ ~ᵉ map-pointed-mapᵉ fᵉ
  htpy-right-unit-law-comp-pointed-mapᵉ = refl-htpyᵉ

  coherence-right-unit-law-comp-pointed-mapᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ
      ( fᵉ ∘∗ᵉ id-pointed-mapᵉ)
      ( fᵉ)
      ( htpy-right-unit-law-comp-pointed-mapᵉ)
  coherence-right-unit-law-comp-pointed-mapᵉ = reflᵉ

  right-unit-law-comp-pointed-mapᵉ : fᵉ ∘∗ᵉ id-pointed-mapᵉ ~∗ᵉ fᵉ
  pr1ᵉ right-unit-law-comp-pointed-mapᵉ =
    htpy-right-unit-law-comp-pointed-mapᵉ
  pr2ᵉ right-unit-law-comp-pointed-mapᵉ =
    coherence-right-unit-law-comp-pointed-mapᵉ
```

### Concatenation of pointed homotopies is a binary equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ hᵉ : pointed-Πᵉ Aᵉ Bᵉ}
  where

  abstract
    is-equiv-concat-pointed-htpyᵉ :
      (Gᵉ : fᵉ ~∗ᵉ gᵉ) → is-equivᵉ (λ (Hᵉ : gᵉ ~∗ᵉ hᵉ) → concat-pointed-htpyᵉ Gᵉ Hᵉ)
    is-equiv-concat-pointed-htpyᵉ Gᵉ =
      is-equiv-map-Σᵉ _
        ( is-equiv-concat-htpyᵉ (htpy-pointed-htpyᵉ Gᵉ) _)
        ( λ Hᵉ →
          is-equiv-horizontal-pasting-coherence-triangle-identificationsᵉ
            ( preserves-point-function-pointed-Πᵉ fᵉ)
            ( preserves-point-function-pointed-Πᵉ gᵉ)
            ( preserves-point-function-pointed-Πᵉ hᵉ)
            ( htpy-pointed-htpyᵉ Gᵉ _)
            ( Hᵉ _)
            ( coherence-point-pointed-htpyᵉ Gᵉ))

  equiv-concat-pointed-htpyᵉ : fᵉ ~∗ᵉ gᵉ → (gᵉ ~∗ᵉ hᵉ) ≃ᵉ (fᵉ ~∗ᵉ hᵉ)
  pr1ᵉ (equiv-concat-pointed-htpyᵉ Gᵉ) = concat-pointed-htpyᵉ Gᵉ
  pr2ᵉ (equiv-concat-pointed-htpyᵉ Gᵉ) = is-equiv-concat-pointed-htpyᵉ Gᵉ

  abstract
    is-equiv-concat-pointed-htpy'ᵉ :
      (Hᵉ : gᵉ ~∗ᵉ hᵉ) → is-equivᵉ (λ (Gᵉ : fᵉ ~∗ᵉ gᵉ) → concat-pointed-htpyᵉ Gᵉ Hᵉ)
    is-equiv-concat-pointed-htpy'ᵉ Hᵉ =
      is-equiv-map-Σᵉ _
        ( is-equiv-concat-htpy'ᵉ _ (htpy-pointed-htpyᵉ Hᵉ))
        ( λ Gᵉ →
          is-equiv-horizontal-pasting-coherence-triangle-identifications'ᵉ
            ( preserves-point-function-pointed-Πᵉ fᵉ)
            ( preserves-point-function-pointed-Πᵉ gᵉ)
            ( preserves-point-function-pointed-Πᵉ hᵉ)
            ( Gᵉ _)
            ( htpy-pointed-htpyᵉ Hᵉ _)
            ( coherence-point-pointed-htpyᵉ Hᵉ))

  equiv-concat-pointed-htpy'ᵉ : gᵉ ~∗ᵉ hᵉ → (fᵉ ~∗ᵉ gᵉ) ≃ᵉ (fᵉ ~∗ᵉ hᵉ)
  pr1ᵉ (equiv-concat-pointed-htpy'ᵉ Hᵉ) Gᵉ = concat-pointed-htpyᵉ Gᵉ Hᵉ
  pr2ᵉ (equiv-concat-pointed-htpy'ᵉ Hᵉ) = is-equiv-concat-pointed-htpy'ᵉ Hᵉ

  is-binary-equiv-concat-pointed-htpyᵉ :
    is-binary-equivᵉ (λ (Gᵉ : fᵉ ~∗ᵉ gᵉ) (Hᵉ : gᵉ ~∗ᵉ hᵉ) → concat-pointed-htpyᵉ Gᵉ Hᵉ)
  pr1ᵉ is-binary-equiv-concat-pointed-htpyᵉ = is-equiv-concat-pointed-htpy'ᵉ
  pr2ᵉ is-binary-equiv-concat-pointed-htpyᵉ = is-equiv-concat-pointed-htpyᵉ
```

## See also

-ᵉ [Pointedᵉ 2-homotopies](structured-types.pointed-2-homotopies.mdᵉ)
-ᵉ [Uniformᵉ pointedᵉ homotopies](structured-types.uniform-pointed-homotopies.mdᵉ)