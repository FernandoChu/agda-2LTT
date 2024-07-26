# Pointed `2`-homotopies

```agda
module structured-types.pointed-2-homotopiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.commuting-triangles-of-identificationsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.path-algebraᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import structured-types.pointed-dependent-functionsᵉ
open import structured-types.pointed-families-of-typesᵉ
open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.uniform-pointed-homotopiesᵉ
```

</details>

## Idea

Considerᵉ twoᵉ [pointedᵉ homotopies](structured-types.pointed-homotopies.mdᵉ)
`Hᵉ :=ᵉ (H₀ᵉ ,ᵉ H₁)`ᵉ andᵉ `Kᵉ :=ᵉ (K₀ᵉ ,ᵉ K₁)`ᵉ betweenᵉ twoᵉ
[pointedᵉ dependentᵉ functions](structured-types.pointed-dependent-functions.mdᵉ)
`fᵉ :=ᵉ (f₀ᵉ ,ᵉ f₁)`ᵉ andᵉ `gᵉ :=ᵉ (g₀ᵉ ,ᵉ g₁)`ᵉ with baseᵉ pointᵉ coherencesᵉ

```text
        H₀ᵉ *ᵉ                        H₀ᵉ *ᵉ
  f₀ᵉ *ᵉ ------>ᵉ g₀ᵉ *ᵉ           f₀ᵉ *ᵉ ------>ᵉ g₀ᵉ *ᵉ
      \ᵉ       /ᵉ                   \ᵉ       ∧ᵉ
    f₁ᵉ \ᵉ  H₁ᵉ /ᵉ g₁ᵉ      andᵉ      f₁ᵉ \ᵉ  H̃₁ᵉ /ᵉ invᵉ g₁ᵉ
        \ᵉ   /ᵉ                       \ᵉ   /ᵉ
         ∨ᵉ ∨ᵉ                         ∨ᵉ /ᵉ
          *ᵉ                           *ᵉ
```

andᵉ

```text
        K₀ᵉ *ᵉ                        K₀ᵉ *ᵉ
  f₀ᵉ *ᵉ ------>ᵉ g₀ᵉ *ᵉ           f₀ᵉ *ᵉ ------>ᵉ g₀ᵉ *ᵉ
      \ᵉ       /ᵉ                   \ᵉ       ∧ᵉ
    f₁ᵉ \ᵉ  K₁ᵉ /ᵉ g₁ᵉ      andᵉ      f₁ᵉ \ᵉ  K̃₁ᵉ /ᵉ invᵉ g₁ᵉ
        \ᵉ   /ᵉ                       \ᵉ   /ᵉ
         ∨ᵉ ∨ᵉ                         ∨ᵉ /ᵉ
          *ᵉ                           *,ᵉ
```

where

```text
  H̃₁ᵉ :=ᵉ coherence-triangle-inv-rightᵉ f₁ᵉ g₁ᵉ (H₀ᵉ *ᵉ) H₁ᵉ
  K̃₁ᵉ :=ᵉ coherence-triangle-inv-rightᵉ f₁ᵉ g₁ᵉ (K₀ᵉ *ᵉ) K₁ᵉ
```

Aᵉ {{#conceptᵉ "pointedᵉ `2`-homotopy"ᵉ Agda=_~²∗ᵉ_}} `Hᵉ ~²∗ᵉ K`ᵉ thenᵉ consistsᵉ ofᵉ anᵉ
unpointedᵉ [homotopy](foundation-core.homotopies.mdᵉ) `α₀ᵉ : H₀ᵉ ~ᵉ K₀`ᵉ andᵉ anᵉ
[identification](foundation-core.identity-types.mdᵉ) witnessingᵉ thatᵉ theᵉ triangleᵉ

```text
        H₁ᵉ
  f₁ᵉ ------>ᵉ (H₀ᵉ *ᵉ) ∙ᵉ g₁ᵉ
    \ᵉ       /ᵉ
  K₁ᵉ \ᵉ     /ᵉ right-whisker-concatᵉ (α₀ᵉ *ᵉ) g₁ᵉ
      \ᵉ   /ᵉ
       ∨ᵉ ∨ᵉ
   (K₀ᵉ *ᵉ) ∙ᵉ g₁ᵉ
```

[commutes](foundation.commuting-triangles-of-identifications.md).ᵉ Equivalently,ᵉ
followingᵉ theᵉ [equivalence](foundation-core.equivalences.mdᵉ) ofᵉ pointedᵉ
homotopiesᵉ andᵉ
[uniformᵉ pointedᵉ homotopies](structured-types.uniform-pointed-homotopies.md),ᵉ aᵉ
uniformᵉ pointedᵉ `2`-homotopyᵉ consistsᵉ ofᵉ anᵉ unpointedᵉ homotopyᵉ `α₀ᵉ : H₀ᵉ ~ᵉ K₀`ᵉ
andᵉ anᵉ identificationᵉ witnessingᵉ thatᵉ `α₀`ᵉ preservesᵉ theᵉ baseᵉ point,ᵉ i.e.,ᵉ
witnessingᵉ thatᵉ theᵉ triangleᵉ

```text
        α₀ᵉ *ᵉ
  H₀ᵉ *ᵉ ------>ᵉ K₀ᵉ *ᵉ
      \ᵉ       ∧ᵉ
    H̃₁ᵉ \ᵉ     /ᵉ invᵉ K̃₁ᵉ
        \ᵉ   /ᵉ
         ∨ᵉ /ᵉ
       f₁ᵉ ∙ᵉ invᵉ g₁ᵉ
```

commutes.ᵉ Noteᵉ thatᵉ suchᵉ identificationsᵉ areᵉ oftenᵉ muchᵉ harderᵉ to construct.ᵉ Ourᵉ
preferredᵉ definitionᵉ ofᵉ pointedᵉ `2`-homotopiesᵉ isᵉ thereforeᵉ theᵉ non-uniformᵉ
definitionᵉ describedᵉ first.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ} (Hᵉ Kᵉ : pointed-htpyᵉ fᵉ gᵉ)
  where

  unpointed-htpy-pointed-htpyᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  unpointed-htpy-pointed-htpyᵉ =
    htpy-pointed-htpyᵉ Hᵉ ~ᵉ htpy-pointed-htpyᵉ Kᵉ

  coherence-point-unpointed-htpy-pointed-htpyᵉ :
    unpointed-htpy-pointed-htpyᵉ → UUᵉ l2ᵉ
  coherence-point-unpointed-htpy-pointed-htpyᵉ αᵉ =
    coherence-triangle-identificationsᵉ
      ( coherence-point-pointed-htpyᵉ Kᵉ)
      ( right-whisker-concatᵉ
        ( αᵉ (point-Pointed-Typeᵉ Aᵉ))
        ( preserves-point-function-pointed-Πᵉ gᵉ))
      ( coherence-point-pointed-htpyᵉ Hᵉ)

  pointed-2-htpyᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  pointed-2-htpyᵉ =
    Σᵉ unpointed-htpy-pointed-htpyᵉ coherence-point-unpointed-htpy-pointed-htpyᵉ

  infix 6 _~²∗ᵉ_

  _~²∗ᵉ_ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  _~²∗ᵉ_ = pointed-2-htpyᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ} {Hᵉ Kᵉ : pointed-htpyᵉ fᵉ gᵉ}
  (αᵉ : pointed-2-htpyᵉ Hᵉ Kᵉ)
  where

  htpy-pointed-2-htpyᵉ : unpointed-htpy-pointed-htpyᵉ Hᵉ Kᵉ
  htpy-pointed-2-htpyᵉ = pr1ᵉ αᵉ

  coherence-point-pointed-2-htpyᵉ :
    coherence-point-unpointed-htpy-pointed-htpyᵉ Hᵉ Kᵉ htpy-pointed-2-htpyᵉ
  coherence-point-pointed-2-htpyᵉ = pr2ᵉ αᵉ

  preserves-point-pointed-2-htpyᵉ :
    preserves-point-unpointed-htpy-pointed-Πᵉ
      ( make-uniform-pointed-htpyᵉ
        ( htpy-pointed-htpyᵉ Hᵉ)
        ( coherence-point-pointed-htpyᵉ Hᵉ))
      ( make-uniform-pointed-htpyᵉ
        ( htpy-pointed-htpyᵉ Kᵉ)
        ( coherence-point-pointed-htpyᵉ Kᵉ))
      ( htpy-pointed-2-htpyᵉ)
  preserves-point-pointed-2-htpyᵉ =
    transpose-right-coherence-triangle-identificationsᵉ
      ( htpy-pointed-2-htpyᵉ (point-Pointed-Typeᵉ Aᵉ))
      ( preserves-point-pointed-htpyᵉ Kᵉ)
      ( preserves-point-pointed-htpyᵉ Hᵉ)
      ( reflᵉ)
      ( higher-transpose-right-coherence-triangle-identificationsᵉ
        ( htpy-pointed-htpyᵉ Hᵉ (point-Pointed-Typeᵉ Aᵉ))
        ( preserves-point-function-pointed-Πᵉ gᵉ)
        ( preserves-point-function-pointed-Πᵉ fᵉ)
        ( htpy-pointed-2-htpyᵉ (point-Pointed-Typeᵉ Aᵉ))
        ( reflᵉ)
        ( coherence-point-pointed-htpyᵉ Hᵉ)
        ( coherence-point-pointed-htpyᵉ Kᵉ)
        ( coherence-point-pointed-2-htpyᵉ))

  uniform-pointed-htpy-pointed-2-htpyᵉ :
    uniform-pointed-htpyᵉ
      ( uniform-pointed-htpy-pointed-htpyᵉ Hᵉ)
      ( uniform-pointed-htpy-pointed-htpyᵉ Kᵉ)
  pr1ᵉ uniform-pointed-htpy-pointed-2-htpyᵉ =
    htpy-pointed-2-htpyᵉ
  pr2ᵉ uniform-pointed-htpy-pointed-2-htpyᵉ =
    preserves-point-pointed-2-htpyᵉ
```

### The reflexive pointed `2`-homotopy

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ} (Hᵉ : fᵉ ~∗ᵉ gᵉ)
  where

  htpy-refl-pointed-2-htpyᵉ : unpointed-htpy-pointed-htpyᵉ Hᵉ Hᵉ
  htpy-refl-pointed-2-htpyᵉ = refl-htpyᵉ

  coherence-point-refl-pointed-2-htpyᵉ :
    coherence-point-unpointed-htpy-pointed-htpyᵉ Hᵉ Hᵉ
      ( htpy-refl-pointed-2-htpyᵉ)
  coherence-point-refl-pointed-2-htpyᵉ = invᵉ right-unitᵉ

  refl-pointed-2-htpyᵉ : Hᵉ ~²∗ᵉ Hᵉ
  pr1ᵉ refl-pointed-2-htpyᵉ = htpy-refl-pointed-2-htpyᵉ
  pr2ᵉ refl-pointed-2-htpyᵉ = coherence-point-refl-pointed-2-htpyᵉ
```

### Concatenation of pointed `2`-homotopies

Considerᵉ twoᵉ pointedᵉ dependentᵉ functionsᵉ `fᵉ :=ᵉ (f₀ᵉ ,ᵉ f₁)`ᵉ andᵉ `gᵉ :=ᵉ (g₀ᵉ ,ᵉ g₁)`ᵉ
andᵉ threeᵉ pointedᵉ homotopiesᵉ `Hᵉ :=ᵉ (H₀ᵉ ,ᵉ H₁)`,ᵉ `Kᵉ :=ᵉ (K₀ᵉ ,ᵉ K₁)`,ᵉ andᵉ
`Lᵉ :=ᵉ (L₀ᵉ ,ᵉ L₁)`ᵉ betweenᵉ them.ᵉ Furthermore,ᵉ considerᵉ twoᵉ pointedᵉ `2`-homotopiesᵉ
`αᵉ :=ᵉ (α₀ᵉ ,ᵉ α₁ᵉ) : Hᵉ ~²∗ᵉ K`ᵉ andᵉ `βᵉ :=ᵉ (β₀ᵉ ,ᵉ β₁ᵉ) : Kᵉ ~²∗ᵉ L`.ᵉ Theᵉ underlyingᵉ
homotopyᵉ ofᵉ theᵉ concatenationᵉ `αᵉ ∙hᵉ β`ᵉ isᵉ simplyᵉ theᵉ concatenationᵉ ofᵉ homotopiesᵉ

```text
  (αᵉ ∙hᵉ β)₀ᵉ :=ᵉ α₀ᵉ ∙hᵉ β₀.ᵉ
```

Theᵉ baseᵉ pointᵉ coherenceᵉ `(αᵉ ∙hᵉ β)₁`ᵉ isᵉ anᵉ identificationᵉ witnessingᵉ thatᵉ theᵉ
triangleᵉ

```text
        H₁ᵉ
  f₁ᵉ ------>ᵉ (H₀ᵉ *ᵉ) ∙ᵉ h₁ᵉ
    \ᵉ       /ᵉ
  L₁ᵉ \ᵉ     /ᵉ right-whisker-concatᵉ ((α₀ᵉ *ᵉ) ∙hᵉ (β₀ᵉ *ᵉ)) g₁ᵉ
      \ᵉ   /ᵉ
       ∨ᵉ ∨ᵉ
   (L₀ᵉ *ᵉ) ∙ᵉ h₁ᵉ
```

commutes.ᵉ Noteᵉ thatᵉ rightᵉ whiskeringᵉ ofᵉ identificationsᵉ with respectᵉ to
concatenationᵉ distributesᵉ overᵉ concatenation.ᵉ Theᵉ identificationᵉ witnessingᵉ theᵉ
commutativityᵉ ofᵉ theᵉ aboveᵉ triangleᵉ canᵉ thereforeᵉ beᵉ constructedᵉ byᵉ constructingᵉ
anᵉ identificationᵉ witnessingᵉ thatᵉ theᵉ triangleᵉ

```text
           H₁ᵉ
  f₁ᵉ ---------->ᵉ (H₀ᵉ *ᵉ) ∙ᵉ h₁ᵉ
    \ᵉ             /ᵉ
     \ᵉ           /ᵉ right-whisker-concatᵉ (α₀ᵉ *ᵉ) g₁ᵉ
      \ᵉ         ∨ᵉ
    L₁ᵉ \ᵉ    (K₀ᵉ *ᵉ) ∙ᵉ h₁ᵉ
        \ᵉ     /ᵉ
         \ᵉ   /ᵉ right-whisker-concatᵉ (β₀ᵉ *ᵉ) g₁ᵉ
          ∨ᵉ ∨ᵉ
      (L₀ᵉ *ᵉ) ∙ᵉ h₁ᵉ
```

commutes.ᵉ Thisᵉ triangleᵉ commutesᵉ byᵉ rightᵉ pastingᵉ ofᵉ commutingᵉ trianglesᵉ ofᵉ
identifications.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ} {Hᵉ Kᵉ Lᵉ : fᵉ ~∗ᵉ gᵉ} (αᵉ : Hᵉ ~²∗ᵉ Kᵉ) (βᵉ : Kᵉ ~²∗ᵉ Lᵉ)
  where

  htpy-concat-pointed-2-htpyᵉ :
    unpointed-htpy-pointed-htpyᵉ Hᵉ Lᵉ
  htpy-concat-pointed-2-htpyᵉ =
    htpy-pointed-2-htpyᵉ αᵉ ∙hᵉ htpy-pointed-2-htpyᵉ βᵉ

  coherence-point-concat-pointed-2-htpyᵉ :
    coherence-point-unpointed-htpy-pointed-htpyᵉ Hᵉ Lᵉ htpy-concat-pointed-2-htpyᵉ
  coherence-point-concat-pointed-2-htpyᵉ =
    ( right-pasting-coherence-triangle-identificationsᵉ _ _ _ _
      ( coherence-point-pointed-htpyᵉ Hᵉ)
      ( coherence-point-pointed-2-htpyᵉ βᵉ)
      ( coherence-point-pointed-2-htpyᵉ αᵉ)) ∙ᵉ
    ( invᵉ
      ( left-whisker-concatᵉ
        ( coherence-point-pointed-htpyᵉ Hᵉ)
        ( distributive-right-whisker-concat-concatᵉ
          ( htpy-pointed-2-htpyᵉ αᵉ _)
          ( htpy-pointed-2-htpyᵉ βᵉ _)
          ( preserves-point-function-pointed-Πᵉ gᵉ))))

  concat-pointed-2-htpyᵉ : Hᵉ ~²∗ᵉ Lᵉ
  pr1ᵉ concat-pointed-2-htpyᵉ = htpy-concat-pointed-2-htpyᵉ
  pr2ᵉ concat-pointed-2-htpyᵉ = coherence-point-concat-pointed-2-htpyᵉ
```

### Inverses of pointed `2`-homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ} {Hᵉ Kᵉ : fᵉ ~∗ᵉ gᵉ} (αᵉ : Hᵉ ~²∗ᵉ Kᵉ)
  where

  htpy-inv-pointed-2-htpyᵉ :
    unpointed-htpy-pointed-htpyᵉ Kᵉ Hᵉ
  htpy-inv-pointed-2-htpyᵉ = inv-htpyᵉ (htpy-pointed-2-htpyᵉ αᵉ)

  coherence-point-inv-pointed-2-htpyᵉ :
    coherence-point-unpointed-htpy-pointed-htpyᵉ Kᵉ Hᵉ htpy-inv-pointed-2-htpyᵉ
  coherence-point-inv-pointed-2-htpyᵉ =
    transpose-right-coherence-triangle-identificationsᵉ
      ( coherence-point-pointed-htpyᵉ Hᵉ)
      ( right-whisker-concatᵉ (htpy-pointed-2-htpyᵉ αᵉ _) _)
      ( coherence-point-pointed-htpyᵉ Kᵉ)
      ( invᵉ (ap-invᵉ _ (htpy-pointed-2-htpyᵉ αᵉ _)))
      ( coherence-point-pointed-2-htpyᵉ αᵉ)

  inv-pointed-2-htpyᵉ : Kᵉ ~²∗ᵉ Hᵉ
  pr1ᵉ inv-pointed-2-htpyᵉ = htpy-inv-pointed-2-htpyᵉ
  pr2ᵉ inv-pointed-2-htpyᵉ = coherence-point-inv-pointed-2-htpyᵉ
```

## Properties

### Extensionality of pointed homotopies

Pointedᵉ `2`-homotopiesᵉ characterizeᵉ identificationsᵉ ofᵉ pointedᵉ homotopies.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ} (Hᵉ : fᵉ ~∗ᵉ gᵉ)
  where

  is-torsorial-pointed-2-htpyᵉ :
    is-torsorialᵉ (pointed-2-htpyᵉ Hᵉ)
  is-torsorial-pointed-2-htpyᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ _)
      ( htpy-pointed-htpyᵉ Hᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-Id'ᵉ _)

  pointed-2-htpy-eqᵉ : (Kᵉ : fᵉ ~∗ᵉ gᵉ) → Hᵉ ＝ᵉ Kᵉ → Hᵉ ~²∗ᵉ Kᵉ
  pointed-2-htpy-eqᵉ .Hᵉ reflᵉ = refl-pointed-2-htpyᵉ Hᵉ

  is-equiv-pointed-2-htpy-eqᵉ :
    (Kᵉ : fᵉ ~∗ᵉ gᵉ) → is-equivᵉ (pointed-2-htpy-eqᵉ Kᵉ)
  is-equiv-pointed-2-htpy-eqᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-pointed-2-htpyᵉ)
      ( pointed-2-htpy-eqᵉ)

  extensionality-pointed-htpyᵉ :
    (Kᵉ : fᵉ ~∗ᵉ gᵉ) → (Hᵉ ＝ᵉ Kᵉ) ≃ᵉ (Hᵉ ~²∗ᵉ Kᵉ)
  pr1ᵉ (extensionality-pointed-htpyᵉ Kᵉ) = pointed-2-htpy-eqᵉ Kᵉ
  pr2ᵉ (extensionality-pointed-htpyᵉ Kᵉ) = is-equiv-pointed-2-htpy-eqᵉ Kᵉ

  eq-pointed-2-htpyᵉ :
    (Kᵉ : fᵉ ~∗ᵉ gᵉ) → Hᵉ ~²∗ᵉ Kᵉ → Hᵉ ＝ᵉ Kᵉ
  eq-pointed-2-htpyᵉ Kᵉ = map-inv-equivᵉ (extensionality-pointed-htpyᵉ Kᵉ)
```

### Concatenation of pointed `2`-homotopies is a binary equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ} {Hᵉ Kᵉ Lᵉ : fᵉ ~∗ᵉ gᵉ}
  where

  abstract
    is-equiv-concat-pointed-2-htpyᵉ :
      (αᵉ : Hᵉ ~²∗ᵉ Kᵉ) → is-equivᵉ (λ (βᵉ : Kᵉ ~²∗ᵉ Lᵉ) → concat-pointed-2-htpyᵉ αᵉ βᵉ)
    is-equiv-concat-pointed-2-htpyᵉ αᵉ =
      is-equiv-map-Σᵉ _
        ( is-equiv-concat-htpyᵉ (htpy-pointed-2-htpyᵉ αᵉ) _)
        ( λ βᵉ →
          is-equiv-compᵉ _ _
            ( is-equiv-right-pasting-coherence-triangle-identifications'ᵉ
              ( coherence-point-pointed-htpyᵉ Lᵉ)
              ( right-whisker-concatᵉ
                ( htpy-pointed-2-htpyᵉ αᵉ _)
                ( preserves-point-function-pointed-Πᵉ gᵉ))
              ( right-whisker-concatᵉ
                ( βᵉ _)
                ( preserves-point-function-pointed-Πᵉ gᵉ))
              ( coherence-point-pointed-htpyᵉ Kᵉ)
              ( coherence-point-pointed-htpyᵉ Hᵉ)
              ( coherence-point-pointed-2-htpyᵉ αᵉ))
            ( is-equiv-concat'ᵉ _
              ( invᵉ
                ( left-whisker-concatᵉ
                  ( coherence-point-pointed-htpyᵉ Hᵉ)
                  ( distributive-right-whisker-concat-concatᵉ
                    ( htpy-pointed-2-htpyᵉ αᵉ _)
                    ( βᵉ _)
                    ( preserves-point-function-pointed-Πᵉ gᵉ))))))

  equiv-concat-pointed-2-htpyᵉ : Hᵉ ~²∗ᵉ Kᵉ → (Kᵉ ~²∗ᵉ Lᵉ) ≃ᵉ (Hᵉ ~²∗ᵉ Lᵉ)
  pr1ᵉ (equiv-concat-pointed-2-htpyᵉ αᵉ) = concat-pointed-2-htpyᵉ αᵉ
  pr2ᵉ (equiv-concat-pointed-2-htpyᵉ αᵉ) = is-equiv-concat-pointed-2-htpyᵉ αᵉ

  abstract
    is-equiv-concat-pointed-2-htpy'ᵉ :
      (βᵉ : Kᵉ ~²∗ᵉ Lᵉ) → is-equivᵉ (λ (αᵉ : Hᵉ ~²∗ᵉ Kᵉ) → concat-pointed-2-htpyᵉ αᵉ βᵉ)
    is-equiv-concat-pointed-2-htpy'ᵉ βᵉ =
      is-equiv-map-Σᵉ _
        ( is-equiv-concat-htpy'ᵉ _ (htpy-pointed-2-htpyᵉ βᵉ))
        ( λ αᵉ →
          is-equiv-compᵉ _ _
            ( is-equiv-right-pasting-coherence-triangle-identificationsᵉ
              ( coherence-point-pointed-htpyᵉ Lᵉ)
              ( right-whisker-concatᵉ
                ( αᵉ _)
                ( preserves-point-function-pointed-Πᵉ gᵉ))
              ( right-whisker-concatᵉ
                ( htpy-pointed-2-htpyᵉ βᵉ _)
                ( preserves-point-function-pointed-Πᵉ gᵉ))
              ( coherence-point-pointed-htpyᵉ Kᵉ)
              ( coherence-point-pointed-htpyᵉ Hᵉ)
              ( coherence-point-pointed-2-htpyᵉ βᵉ))
            ( is-equiv-concat'ᵉ _
              ( invᵉ
                ( left-whisker-concatᵉ
                  ( coherence-point-pointed-htpyᵉ Hᵉ)
                  ( distributive-right-whisker-concat-concatᵉ
                    ( αᵉ _)
                    ( htpy-pointed-2-htpyᵉ βᵉ _)
                    ( preserves-point-function-pointed-Πᵉ gᵉ))))))

  equiv-concat-pointed-2-htpy'ᵉ :
    Kᵉ ~²∗ᵉ Lᵉ → (Hᵉ ~²∗ᵉ Kᵉ) ≃ᵉ (Hᵉ ~²∗ᵉ Lᵉ)
  pr1ᵉ (equiv-concat-pointed-2-htpy'ᵉ βᵉ) αᵉ = concat-pointed-2-htpyᵉ αᵉ βᵉ
  pr2ᵉ (equiv-concat-pointed-2-htpy'ᵉ βᵉ) = is-equiv-concat-pointed-2-htpy'ᵉ βᵉ

  is-binary-equiv-concat-pointed-2-htpyᵉ :
    is-binary-equivᵉ (λ (αᵉ : Hᵉ ~²∗ᵉ Kᵉ) (βᵉ : Kᵉ ~²∗ᵉ Lᵉ) → concat-pointed-2-htpyᵉ αᵉ βᵉ)
  pr1ᵉ is-binary-equiv-concat-pointed-2-htpyᵉ = is-equiv-concat-pointed-2-htpy'ᵉ
  pr2ᵉ is-binary-equiv-concat-pointed-2-htpyᵉ = is-equiv-concat-pointed-2-htpyᵉ
```

### Associativity of concatenation of pointed homotopies

Associativityᵉ ofᵉ concatenationᵉ ofᵉ threeᵉ pointedᵉ homotopiesᵉ `G`,ᵉ `H`,ᵉ andᵉ `K`ᵉ isᵉ
aᵉ pointedᵉ `2`-homotopyᵉ

```text
  (Gᵉ ∙hᵉ Hᵉ) ∙hᵉ Kᵉ ~²∗ᵉ Gᵉ ∙hᵉ (Hᵉ ∙hᵉ K).ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ hᵉ kᵉ : pointed-Πᵉ Aᵉ Bᵉ} (Gᵉ : fᵉ ~∗ᵉ gᵉ) (Hᵉ : gᵉ ~∗ᵉ hᵉ) (Kᵉ : hᵉ ~∗ᵉ kᵉ)
  where

  htpy-associative-concat-pointed-htpyᵉ :
    htpy-pointed-htpyᵉ
      ( concat-pointed-htpyᵉ (concat-pointed-htpyᵉ Gᵉ Hᵉ) Kᵉ) ~ᵉ
    htpy-pointed-htpyᵉ
      ( concat-pointed-htpyᵉ Gᵉ (concat-pointed-htpyᵉ Hᵉ Kᵉ))
  htpy-associative-concat-pointed-htpyᵉ =
    assoc-htpyᵉ
      ( htpy-pointed-htpyᵉ Gᵉ)
      ( htpy-pointed-htpyᵉ Hᵉ)
      ( htpy-pointed-htpyᵉ Kᵉ)

  coherence-associative-concat-pointed-htpyᵉ :
    coherence-point-unpointed-htpy-pointed-htpyᵉ
      ( concat-pointed-htpyᵉ (concat-pointed-htpyᵉ Gᵉ Hᵉ) Kᵉ)
      ( concat-pointed-htpyᵉ Gᵉ (concat-pointed-htpyᵉ Hᵉ Kᵉ))
      ( htpy-associative-concat-pointed-htpyᵉ)
  coherence-associative-concat-pointed-htpyᵉ =
    associative-horizontal-pasting-coherence-triangle-identificationsᵉ
      ( preserves-point-function-pointed-Πᵉ fᵉ)
      ( preserves-point-function-pointed-Πᵉ gᵉ)
      ( preserves-point-function-pointed-Πᵉ hᵉ)
      ( preserves-point-function-pointed-Πᵉ kᵉ)
      ( htpy-pointed-htpyᵉ Gᵉ _)
      ( htpy-pointed-htpyᵉ Hᵉ _)
      ( htpy-pointed-htpyᵉ Kᵉ _)
      ( coherence-point-pointed-htpyᵉ Gᵉ)
      ( coherence-point-pointed-htpyᵉ Hᵉ)
      ( coherence-point-pointed-htpyᵉ Kᵉ)

  associative-concat-pointed-htpyᵉ :
    concat-pointed-htpyᵉ (concat-pointed-htpyᵉ Gᵉ Hᵉ) Kᵉ ~²∗ᵉ
    concat-pointed-htpyᵉ Gᵉ (concat-pointed-htpyᵉ Hᵉ Kᵉ)
  pr1ᵉ associative-concat-pointed-htpyᵉ =
    htpy-associative-concat-pointed-htpyᵉ
  pr2ᵉ associative-concat-pointed-htpyᵉ =
    coherence-associative-concat-pointed-htpyᵉ
```

### The left unit law of concatenation of pointed homotopies

Considerᵉ aᵉ pointedᵉ homotopyᵉ `Hᵉ :=ᵉ (H₀ᵉ ,ᵉ H₁)`ᵉ betweenᵉ pointedᵉ dependentᵉ functionsᵉ
`fᵉ :=ᵉ (f₀ᵉ ,ᵉ f₁)`ᵉ andᵉ `gᵉ :=ᵉ (g₀ᵉ ,ᵉ g₁)`.ᵉ Thenᵉ thereᵉ isᵉ aᵉ pointedᵉ `2`-homotopyᵉ ofᵉ
typeᵉ

```text
  refl-pointed-htpyᵉ ∙hᵉ Hᵉ ~²∗ᵉ H.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ} (Hᵉ : fᵉ ~∗ᵉ gᵉ)
  where

  htpy-left-unit-law-concat-pointed-htpyᵉ :
    unpointed-htpy-pointed-htpyᵉ
      ( concat-pointed-htpyᵉ (refl-pointed-htpyᵉ fᵉ) Hᵉ)
      ( Hᵉ)
  htpy-left-unit-law-concat-pointed-htpyᵉ = refl-htpyᵉ

  coherence-point-left-unit-law-concat-pointed-htpyᵉ :
    coherence-point-unpointed-htpy-pointed-htpyᵉ
      ( concat-pointed-htpyᵉ (refl-pointed-htpyᵉ fᵉ) Hᵉ)
      ( Hᵉ)
      ( htpy-left-unit-law-concat-pointed-htpyᵉ)
  coherence-point-left-unit-law-concat-pointed-htpyᵉ =
    invᵉ (right-unitᵉ ∙ᵉ right-unitᵉ ∙ᵉ ap-idᵉ (coherence-point-pointed-htpyᵉ Hᵉ))

  left-unit-law-concat-pointed-htpyᵉ :
    concat-pointed-htpyᵉ (refl-pointed-htpyᵉ fᵉ) Hᵉ ~²∗ᵉ Hᵉ
  pr1ᵉ left-unit-law-concat-pointed-htpyᵉ =
    htpy-left-unit-law-concat-pointed-htpyᵉ
  pr2ᵉ left-unit-law-concat-pointed-htpyᵉ =
    coherence-point-left-unit-law-concat-pointed-htpyᵉ
```

### The right unit law of concatenation of pointed homotopies

Considerᵉ aᵉ pointedᵉ homotopyᵉ `Hᵉ :=ᵉ (H₀ᵉ ,ᵉ H₁)`ᵉ betweenᵉ pointedᵉ dependentᵉ functionsᵉ
`fᵉ :=ᵉ (f₀ᵉ ,ᵉ f₁)`ᵉ andᵉ `gᵉ :=ᵉ (g₀ᵉ ,ᵉ g₁)`.ᵉ Thenᵉ thereᵉ isᵉ aᵉ pointedᵉ `2`-homotopyᵉ

```text
  Hᵉ ∙hᵉ refl-pointed-htpyᵉ ~²∗ᵉ H.ᵉ
```

Theᵉ underlyingᵉ homotopyᵉ ofᵉ thisᵉ pointedᵉ `2`-homotopyᵉ isᵉ theᵉ homotopyᵉ
`right-unit-htpy`.ᵉ Theᵉ baseᵉ pointᵉ coherenceᵉ ofᵉ thisᵉ homotopyᵉ isᵉ anᵉ
identificationᵉ witnessingᵉ thatᵉ theᵉ triangleᵉ

```text
     (Hᵉ ∙hᵉ refl)₁ᵉ
  f₁ᵉ ------------>ᵉ (H₀ᵉ *ᵉ ∙ᵉ reflᵉ) ∙ᵉ g₁ᵉ
    \ᵉ             /ᵉ
  H₁ᵉ \ᵉ           /ᵉ right-whisker-concatᵉ right-unitᵉ g₁ᵉ
      \ᵉ         /ᵉ
       ∨ᵉ       ∨ᵉ
      (H₀ᵉ *ᵉ) ∙ᵉ g₁ᵉ
```

commutes.ᵉ Here,ᵉ theᵉ identificationᵉ `(Hᵉ ∙hᵉ refl)₁`ᵉ isᵉ theᵉ horizontalᵉ pastingᵉ ofᵉ
commutingᵉ trianglesᵉ ofᵉ identificationsᵉ

```text
      H₀ᵉ *ᵉ      reflᵉ
  f₀ᵉ *ᵉ -->ᵉ g₀ᵉ *ᵉ --->ᵉ g₀ᵉ *ᵉ
      \ᵉ      |      /ᵉ
       \ᵉ     | g₁ᵉ  /ᵉ
     f₁ᵉ \ᵉ    |    /ᵉ g₁ᵉ
         \ᵉ   |   /ᵉ
          \ᵉ  |  /ᵉ
           ∨ᵉ ∨ᵉ ∨ᵉ
             *.ᵉ
```

Theᵉ upperᵉ triangleᵉ thereforeᵉ commutesᵉ byᵉ theᵉ rightᵉ unitᵉ lawᵉ ofᵉ horizontalᵉ
pastingᵉ ofᵉ commutingᵉ trianglesᵉ ofᵉ identifications.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  {fᵉ gᵉ : pointed-Πᵉ Aᵉ Bᵉ} (Hᵉ : fᵉ ~∗ᵉ gᵉ)
  where

  htpy-right-unit-law-concat-pointed-htpyᵉ :
    unpointed-htpy-pointed-htpyᵉ
      ( concat-pointed-htpyᵉ Hᵉ (refl-pointed-htpyᵉ gᵉ))
      ( Hᵉ)
  htpy-right-unit-law-concat-pointed-htpyᵉ = right-unit-htpyᵉ

  coherence-point-right-unit-law-concat-pointed-htpyᵉ :
    coherence-point-unpointed-htpy-pointed-htpyᵉ
      ( concat-pointed-htpyᵉ Hᵉ (refl-pointed-htpyᵉ gᵉ))
      ( Hᵉ)
      ( htpy-right-unit-law-concat-pointed-htpyᵉ)
  coherence-point-right-unit-law-concat-pointed-htpyᵉ =
    right-unit-law-horizontal-pasting-coherence-triangle-identificationsᵉ
      ( preserves-point-function-pointed-Πᵉ fᵉ)
      ( preserves-point-function-pointed-Πᵉ gᵉ)
      ( htpy-pointed-htpyᵉ Hᵉ _)
      ( coherence-point-pointed-htpyᵉ Hᵉ)

  right-unit-law-concat-pointed-htpyᵉ :
    concat-pointed-htpyᵉ Hᵉ (refl-pointed-htpyᵉ gᵉ) ~²∗ᵉ Hᵉ
  pr1ᵉ right-unit-law-concat-pointed-htpyᵉ =
    htpy-right-unit-law-concat-pointed-htpyᵉ
  pr2ᵉ right-unit-law-concat-pointed-htpyᵉ =
    coherence-point-right-unit-law-concat-pointed-htpyᵉ
```