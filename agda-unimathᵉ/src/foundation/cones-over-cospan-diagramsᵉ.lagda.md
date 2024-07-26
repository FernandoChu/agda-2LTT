# Cones over cospan diagrams

```agda
module foundation.cones-over-cospan-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.multivariable-homotopiesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.transport-along-identificationsᵉ
open import foundation-core.whiskering-identifications-concatenationᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "cone"ᵉ Disambiguation="cospanᵉ diagram"ᵉ Agda=coneᵉ}} overᵉ aᵉ
[cospanᵉ diagram](foundation.cospans.mdᵉ) `Aᵉ -f->ᵉ Xᵉ <-g-ᵉ B`ᵉ with domainᵉ `C`ᵉ isᵉ aᵉ
tripleᵉ `(p,ᵉ q,ᵉ H)`ᵉ consistingᵉ ofᵉ aᵉ mapᵉ `pᵉ : Cᵉ → A`,ᵉ aᵉ mapᵉ `qᵉ : Cᵉ → B`,ᵉ andᵉ aᵉ
[homotopy](foundation-core.homotopies.mdᵉ) `H`ᵉ witnessingᵉ thatᵉ theᵉ squareᵉ

```text
        qᵉ
    Cᵉ ----->ᵉ Bᵉ
    |        |
  pᵉ |        | gᵉ
    ∨ᵉ        ∨ᵉ
    Aᵉ ----->ᵉ Xᵉ
        fᵉ
```

[commutes](foundation-core.commuting-squares-of-maps.md).ᵉ

## Definitions

### Cones over cospans

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  coneᵉ : {l4ᵉ : Level} → UUᵉ l4ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  coneᵉ Cᵉ = Σᵉ (Cᵉ → Aᵉ) (λ pᵉ → Σᵉ (Cᵉ → Bᵉ) (λ qᵉ → coherence-square-mapsᵉ qᵉ pᵉ gᵉ fᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ)
  where

  vertical-map-coneᵉ : Cᵉ → Aᵉ
  vertical-map-coneᵉ = pr1ᵉ cᵉ

  horizontal-map-coneᵉ : Cᵉ → Bᵉ
  horizontal-map-coneᵉ = pr1ᵉ (pr2ᵉ cᵉ)

  coherence-square-coneᵉ :
    coherence-square-mapsᵉ horizontal-map-coneᵉ vertical-map-coneᵉ gᵉ fᵉ
  coherence-square-coneᵉ = pr2ᵉ (pr2ᵉ cᵉ)
```

### Dependent cones over cospan diagrams

```agda
cone-familyᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level}
  {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (PXᵉ : Xᵉ → UUᵉ l5ᵉ) {PAᵉ : Aᵉ → UUᵉ l6ᵉ} {PBᵉ : Bᵉ → UUᵉ l7ᵉ}
  {fᵉ : Aᵉ → Xᵉ} {gᵉ : Bᵉ → Xᵉ} →
  (f'ᵉ : (aᵉ : Aᵉ) → PAᵉ aᵉ → PXᵉ (fᵉ aᵉ)) (g'ᵉ : (bᵉ : Bᵉ) → PBᵉ bᵉ → PXᵉ (gᵉ bᵉ)) →
  coneᵉ fᵉ gᵉ Cᵉ → (Cᵉ → UUᵉ l8ᵉ) → UUᵉ (l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ)
cone-familyᵉ {Cᵉ = Cᵉ} PXᵉ {fᵉ = fᵉ} {gᵉ} f'ᵉ g'ᵉ cᵉ PCᵉ =
  (xᵉ : Cᵉ) →
  coneᵉ
    ( ( trᵉ PXᵉ (coherence-square-coneᵉ fᵉ gᵉ cᵉ xᵉ)) ∘ᵉ
      ( f'ᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ)))
    ( g'ᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ xᵉ))
    ( PCᵉ xᵉ)
```

### Characterizing identifications of cones over cospan diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) {Cᵉ : UUᵉ l4ᵉ}
  where

  coherence-htpy-coneᵉ :
    (cᵉ c'ᵉ : coneᵉ fᵉ gᵉ Cᵉ)
    (Kᵉ : vertical-map-coneᵉ fᵉ gᵉ cᵉ ~ᵉ vertical-map-coneᵉ fᵉ gᵉ c'ᵉ)
    (Lᵉ : horizontal-map-coneᵉ fᵉ gᵉ cᵉ ~ᵉ horizontal-map-coneᵉ fᵉ gᵉ c'ᵉ) → UUᵉ (l4ᵉ ⊔ l3ᵉ)
  coherence-htpy-coneᵉ cᵉ c'ᵉ Kᵉ Lᵉ =
    ( coherence-square-coneᵉ fᵉ gᵉ cᵉ ∙hᵉ (gᵉ ·lᵉ Lᵉ)) ~ᵉ
    ( (fᵉ ·lᵉ Kᵉ) ∙hᵉ coherence-square-coneᵉ fᵉ gᵉ c'ᵉ)

  htpy-coneᵉ : coneᵉ fᵉ gᵉ Cᵉ → coneᵉ fᵉ gᵉ Cᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-coneᵉ cᵉ c'ᵉ =
    Σᵉ ( vertical-map-coneᵉ fᵉ gᵉ cᵉ ~ᵉ vertical-map-coneᵉ fᵉ gᵉ c'ᵉ)
      ( λ Kᵉ →
        Σᵉ ( horizontal-map-coneᵉ fᵉ gᵉ cᵉ ~ᵉ horizontal-map-coneᵉ fᵉ gᵉ c'ᵉ)
          ( coherence-htpy-coneᵉ cᵉ c'ᵉ Kᵉ))

  htpy-vertical-map-htpy-coneᵉ :
    (cᵉ c'ᵉ : coneᵉ fᵉ gᵉ Cᵉ) (Hᵉ : htpy-coneᵉ cᵉ c'ᵉ) →
    vertical-map-coneᵉ fᵉ gᵉ cᵉ ~ᵉ vertical-map-coneᵉ fᵉ gᵉ c'ᵉ
  htpy-vertical-map-htpy-coneᵉ cᵉ c'ᵉ Hᵉ = pr1ᵉ Hᵉ

  htpy-horizontal-map-htpy-coneᵉ :
    (cᵉ c'ᵉ : coneᵉ fᵉ gᵉ Cᵉ) (Hᵉ : htpy-coneᵉ cᵉ c'ᵉ) →
    horizontal-map-coneᵉ fᵉ gᵉ cᵉ ~ᵉ horizontal-map-coneᵉ fᵉ gᵉ c'ᵉ
  htpy-horizontal-map-htpy-coneᵉ cᵉ c'ᵉ Hᵉ = pr1ᵉ (pr2ᵉ Hᵉ)

  coh-htpy-coneᵉ :
    (cᵉ c'ᵉ : coneᵉ fᵉ gᵉ Cᵉ) (Hᵉ : htpy-coneᵉ cᵉ c'ᵉ) →
    coherence-htpy-coneᵉ cᵉ c'ᵉ
      ( htpy-vertical-map-htpy-coneᵉ cᵉ c'ᵉ Hᵉ)
      ( htpy-horizontal-map-htpy-coneᵉ cᵉ c'ᵉ Hᵉ)
  coh-htpy-coneᵉ cᵉ c'ᵉ Hᵉ = pr2ᵉ (pr2ᵉ Hᵉ)

  refl-htpy-coneᵉ : (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) → htpy-coneᵉ cᵉ cᵉ
  pr1ᵉ (refl-htpy-coneᵉ cᵉ) = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ (refl-htpy-coneᵉ cᵉ)) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ (refl-htpy-coneᵉ cᵉ)) = right-unit-htpyᵉ

  htpy-eq-coneᵉ : (cᵉ c'ᵉ : coneᵉ fᵉ gᵉ Cᵉ) → cᵉ ＝ᵉ c'ᵉ → htpy-coneᵉ cᵉ c'ᵉ
  htpy-eq-coneᵉ cᵉ .cᵉ reflᵉ = refl-htpy-coneᵉ cᵉ

  is-torsorial-htpy-coneᵉ :
    (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) → is-torsorialᵉ (htpy-coneᵉ cᵉ)
  is-torsorial-htpy-coneᵉ cᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ))
      ( vertical-map-coneᵉ fᵉ gᵉ cᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpyᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ))
        ( horizontal-map-coneᵉ fᵉ gᵉ cᵉ ,ᵉ refl-htpyᵉ)
        ( is-torsorial-htpyᵉ (coherence-square-coneᵉ fᵉ gᵉ cᵉ ∙hᵉ refl-htpyᵉ)))

  is-equiv-htpy-eq-coneᵉ : (cᵉ c'ᵉ : coneᵉ fᵉ gᵉ Cᵉ) → is-equivᵉ (htpy-eq-coneᵉ cᵉ c'ᵉ)
  is-equiv-htpy-eq-coneᵉ cᵉ =
    fundamental-theorem-idᵉ (is-torsorial-htpy-coneᵉ cᵉ) (htpy-eq-coneᵉ cᵉ)

  extensionality-coneᵉ : (cᵉ c'ᵉ : coneᵉ fᵉ gᵉ Cᵉ) → (cᵉ ＝ᵉ c'ᵉ) ≃ᵉ htpy-coneᵉ cᵉ c'ᵉ
  pr1ᵉ (extensionality-coneᵉ cᵉ c'ᵉ) = htpy-eq-coneᵉ cᵉ c'ᵉ
  pr2ᵉ (extensionality-coneᵉ cᵉ c'ᵉ) = is-equiv-htpy-eq-coneᵉ cᵉ c'ᵉ

  eq-htpy-coneᵉ : (cᵉ c'ᵉ : coneᵉ fᵉ gᵉ Cᵉ) → htpy-coneᵉ cᵉ c'ᵉ → cᵉ ＝ᵉ c'ᵉ
  eq-htpy-coneᵉ cᵉ c'ᵉ = map-inv-equivᵉ (extensionality-coneᵉ cᵉ c'ᵉ)
```

### Precomposing cones over cospan diagrams with a map

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  cone-mapᵉ :
    {Cᵉ : UUᵉ l4ᵉ} → coneᵉ fᵉ gᵉ Cᵉ → {C'ᵉ : UUᵉ l5ᵉ} → (C'ᵉ → Cᵉ) → coneᵉ fᵉ gᵉ C'ᵉ
  pr1ᵉ (cone-mapᵉ cᵉ hᵉ) = vertical-map-coneᵉ fᵉ gᵉ cᵉ ∘ᵉ hᵉ
  pr1ᵉ (pr2ᵉ (cone-mapᵉ cᵉ hᵉ)) = horizontal-map-coneᵉ fᵉ gᵉ cᵉ ∘ᵉ hᵉ
  pr2ᵉ (pr2ᵉ (cone-mapᵉ cᵉ hᵉ)) = coherence-square-coneᵉ fᵉ gᵉ cᵉ ·rᵉ hᵉ
```

### Pasting cones horizontally

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  (iᵉ : Xᵉ → Yᵉ) (jᵉ : Yᵉ → Zᵉ) (hᵉ : Cᵉ → Zᵉ)
  where

  pasting-horizontal-coneᵉ :
    (cᵉ : coneᵉ jᵉ hᵉ Bᵉ) → coneᵉ iᵉ (vertical-map-coneᵉ jᵉ hᵉ cᵉ) Aᵉ → coneᵉ (jᵉ ∘ᵉ iᵉ) hᵉ Aᵉ
  pr1ᵉ (pasting-horizontal-coneᵉ cᵉ (fᵉ ,ᵉ pᵉ ,ᵉ Hᵉ)) = fᵉ
  pr1ᵉ (pr2ᵉ (pasting-horizontal-coneᵉ cᵉ (fᵉ ,ᵉ pᵉ ,ᵉ Hᵉ))) =
    (horizontal-map-coneᵉ jᵉ hᵉ cᵉ) ∘ᵉ pᵉ
  pr2ᵉ (pr2ᵉ (pasting-horizontal-coneᵉ cᵉ (fᵉ ,ᵉ pᵉ ,ᵉ Hᵉ))) =
    pasting-horizontal-coherence-square-mapsᵉ pᵉ
      ( horizontal-map-coneᵉ jᵉ hᵉ cᵉ)
      ( fᵉ)
      ( vertical-map-coneᵉ jᵉ hᵉ cᵉ)
      ( hᵉ)
      ( iᵉ)
      ( jᵉ)
      ( Hᵉ)
      ( coherence-square-coneᵉ jᵉ hᵉ cᵉ)
```

### Vertical composition of cones

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  (fᵉ : Cᵉ → Zᵉ) (gᵉ : Yᵉ → Zᵉ) (hᵉ : Xᵉ → Yᵉ)
  where

  pasting-vertical-coneᵉ :
    (cᵉ : coneᵉ fᵉ gᵉ Bᵉ) → coneᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) hᵉ Aᵉ → coneᵉ fᵉ (gᵉ ∘ᵉ hᵉ) Aᵉ
  pr1ᵉ (pasting-vertical-coneᵉ cᵉ (p'ᵉ ,ᵉ q'ᵉ ,ᵉ H'ᵉ)) =
    ( vertical-map-coneᵉ fᵉ gᵉ cᵉ) ∘ᵉ p'ᵉ
  pr1ᵉ (pr2ᵉ (pasting-vertical-coneᵉ cᵉ (p'ᵉ ,ᵉ q'ᵉ ,ᵉ H'ᵉ))) = q'ᵉ
  pr2ᵉ (pr2ᵉ (pasting-vertical-coneᵉ cᵉ (p'ᵉ ,ᵉ q'ᵉ ,ᵉ H'ᵉ))) =
    pasting-vertical-coherence-square-mapsᵉ q'ᵉ p'ᵉ hᵉ
      ( horizontal-map-coneᵉ fᵉ gᵉ cᵉ)
      ( vertical-map-coneᵉ fᵉ gᵉ cᵉ)
      ( gᵉ)
      ( fᵉ)
      ( H'ᵉ)
      ( coherence-square-coneᵉ fᵉ gᵉ cᵉ)
```

### The swapping function on cones over cospans

```agda
swap-coneᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) → coneᵉ fᵉ gᵉ Cᵉ → coneᵉ gᵉ fᵉ Cᵉ
pr1ᵉ (swap-coneᵉ fᵉ gᵉ cᵉ) = horizontal-map-coneᵉ fᵉ gᵉ cᵉ
pr1ᵉ (pr2ᵉ (swap-coneᵉ fᵉ gᵉ cᵉ)) = vertical-map-coneᵉ fᵉ gᵉ cᵉ
pr2ᵉ (pr2ᵉ (swap-coneᵉ fᵉ gᵉ cᵉ)) = inv-htpyᵉ (coherence-square-coneᵉ fᵉ gᵉ cᵉ)
```

### Parallel cones over parallel cospan diagrams

Twoᵉ conesᵉ with theᵉ sameᵉ domainᵉ overᵉ parallelᵉ cospansᵉ areᵉ consideredᵉ
{{#conceptᵉ "parallel"ᵉ Disambiguation="conesᵉ overᵉ parallelᵉ cospanᵉ diagrams"ᵉ}} ifᵉ
theyᵉ areᵉ partᵉ ofᵉ aᵉ fullyᵉ coherentᵉ diagramᵉ: thereᵉ isᵉ aᵉ fullyᵉ coherentᵉ cubeᵉ where
allᵉ theᵉ verticalᵉ mapsᵉ areᵉ identities,ᵉ theᵉ topᵉ faceᵉ isᵉ givenᵉ byᵉ oneᵉ cone,ᵉ andᵉ theᵉ
bottomᵉ faceᵉ isᵉ givenᵉ byᵉ theᵉ other.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  {fᵉ f'ᵉ : Aᵉ → Xᵉ} (Hfᵉ : fᵉ ~ᵉ f'ᵉ) {gᵉ g'ᵉ : Bᵉ → Xᵉ} (Hgᵉ : gᵉ ~ᵉ g'ᵉ)
  where

  coherence-htpy-parallel-coneᵉ :
    {l4ᵉ : Level} {Cᵉ : UUᵉ l4ᵉ} (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ f'ᵉ g'ᵉ Cᵉ)
    (Hpᵉ : vertical-map-coneᵉ fᵉ gᵉ cᵉ ~ᵉ vertical-map-coneᵉ f'ᵉ g'ᵉ c'ᵉ)
    (Hqᵉ : horizontal-map-coneᵉ fᵉ gᵉ cᵉ ~ᵉ horizontal-map-coneᵉ f'ᵉ g'ᵉ c'ᵉ) →
    UUᵉ (l3ᵉ ⊔ l4ᵉ)
  coherence-htpy-parallel-coneᵉ cᵉ c'ᵉ Hpᵉ Hqᵉ =
    ( ( coherence-square-coneᵉ fᵉ gᵉ cᵉ) ∙hᵉ
      ( (gᵉ ·lᵉ Hqᵉ) ∙hᵉ (Hgᵉ ·rᵉ horizontal-map-coneᵉ f'ᵉ g'ᵉ c'ᵉ))) ~ᵉ
    ( ( (fᵉ ·lᵉ Hpᵉ) ∙hᵉ (Hfᵉ ·rᵉ (vertical-map-coneᵉ f'ᵉ g'ᵉ c'ᵉ))) ∙hᵉ
      ( coherence-square-coneᵉ f'ᵉ g'ᵉ c'ᵉ))

  fam-htpy-parallel-coneᵉ :
    {l4ᵉ : Level} {Cᵉ : UUᵉ l4ᵉ} (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) → (c'ᵉ : coneᵉ f'ᵉ g'ᵉ Cᵉ) →
    (vertical-map-coneᵉ fᵉ gᵉ cᵉ ~ᵉ vertical-map-coneᵉ f'ᵉ g'ᵉ c'ᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  fam-htpy-parallel-coneᵉ cᵉ c'ᵉ Hpᵉ =
    Σᵉ ( horizontal-map-coneᵉ fᵉ gᵉ cᵉ ~ᵉ horizontal-map-coneᵉ f'ᵉ g'ᵉ c'ᵉ)
      ( coherence-htpy-parallel-coneᵉ cᵉ c'ᵉ Hpᵉ)

  htpy-parallel-coneᵉ :
    {l4ᵉ : Level} {Cᵉ : UUᵉ l4ᵉ} →
    coneᵉ fᵉ gᵉ Cᵉ → coneᵉ f'ᵉ g'ᵉ Cᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-parallel-coneᵉ cᵉ c'ᵉ =
    Σᵉ ( vertical-map-coneᵉ fᵉ gᵉ cᵉ ~ᵉ vertical-map-coneᵉ f'ᵉ g'ᵉ c'ᵉ)
      ( fam-htpy-parallel-coneᵉ cᵉ c'ᵉ)
```

### The identity cone over the identity cospan

```agda
id-coneᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → coneᵉ (idᵉ {Aᵉ = Aᵉ}) (idᵉ {Aᵉ = Aᵉ}) Aᵉ
id-coneᵉ Aᵉ = (idᵉ ,ᵉ idᵉ ,ᵉ refl-htpyᵉ)
```

## Properties

### Relating `htpy-parallel-cone` to the identity type of cones

Inᵉ theᵉ followingᵉ partᵉ weᵉ relateᵉ theᵉ typeᵉ `htpy-parallel-cone`ᵉ to theᵉ identityᵉ
typeᵉ ofᵉ cones.ᵉ Weᵉ showᵉ thatᵉ `htpy-parallel-cone`ᵉ characterizesᵉ
[dependentᵉ identifications](foundation.dependent-identifications.mdᵉ) ofᵉ conesᵉ onᵉ
theᵉ sameᵉ domainᵉ overᵉ parallelᵉ cospans.ᵉ

**Note.**ᵉ Theᵉ characterizationᵉ reliesᵉ heavilyᵉ onᵉ
[functionᵉ extensionality](foundation.function-extensionality.md).ᵉ

#### The type family of homotopies of parallel cones is torsorial

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  {fᵉ : Aᵉ → Xᵉ} {gᵉ : Bᵉ → Xᵉ}
  where

  refl-htpy-parallel-coneᵉ :
    (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
    htpy-parallel-coneᵉ (refl-htpy'ᵉ fᵉ) (refl-htpy'ᵉ gᵉ) cᵉ cᵉ
  pr1ᵉ (refl-htpy-parallel-coneᵉ cᵉ) = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ (refl-htpy-parallel-coneᵉ cᵉ)) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ (refl-htpy-parallel-coneᵉ cᵉ)) = right-unit-htpyᵉ

  htpy-eq-degenerate-parallel-coneᵉ :
    (cᵉ c'ᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
    cᵉ ＝ᵉ c'ᵉ →
    htpy-parallel-coneᵉ (refl-htpy'ᵉ fᵉ) (refl-htpy'ᵉ gᵉ) cᵉ c'ᵉ
  htpy-eq-degenerate-parallel-coneᵉ cᵉ .cᵉ reflᵉ = refl-htpy-parallel-coneᵉ cᵉ

  htpy-parallel-cone-refl-htpy-htpy-coneᵉ :
    (cᵉ c'ᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
    htpy-coneᵉ fᵉ gᵉ cᵉ c'ᵉ →
    htpy-parallel-coneᵉ (refl-htpy'ᵉ fᵉ) (refl-htpy'ᵉ gᵉ) cᵉ c'ᵉ
  htpy-parallel-cone-refl-htpy-htpy-coneᵉ (pᵉ ,ᵉ qᵉ ,ᵉ Hᵉ) (p'ᵉ ,ᵉ q'ᵉ ,ᵉ H'ᵉ) =
    totᵉ
      ( λ Kᵉ →
        totᵉ
          ( λ Lᵉ Mᵉ →
            ( ap-concat-htpyᵉ Hᵉ right-unit-htpyᵉ) ∙hᵉ
            ( Mᵉ ∙hᵉ ap-concat-htpy'ᵉ H'ᵉ inv-htpy-right-unit-htpyᵉ)))

  abstract
    is-equiv-htpy-parallel-cone-refl-htpy-htpy-coneᵉ :
      (cᵉ c'ᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
      is-equivᵉ (htpy-parallel-cone-refl-htpy-htpy-coneᵉ cᵉ c'ᵉ)
    is-equiv-htpy-parallel-cone-refl-htpy-htpy-coneᵉ (pᵉ ,ᵉ qᵉ ,ᵉ Hᵉ) (p'ᵉ ,ᵉ q'ᵉ ,ᵉ H'ᵉ) =
      is-equiv-tot-is-fiberwise-equivᵉ
        ( λ Kᵉ →
          is-equiv-tot-is-fiberwise-equivᵉ
            ( λ Lᵉ →
              is-equiv-compᵉ
                ( concat-htpyᵉ
                  ( ap-concat-htpyᵉ Hᵉ right-unit-htpyᵉ)
                  ( (fᵉ ·lᵉ Kᵉ) ∙hᵉ refl-htpyᵉ ∙hᵉ H'ᵉ))
                ( concat-htpy'ᵉ
                  ( Hᵉ ∙hᵉ (gᵉ ·lᵉ Lᵉ))
                  ( ap-concat-htpy'ᵉ H'ᵉ inv-htpy-right-unit-htpyᵉ))
                ( is-equiv-concat-htpy'ᵉ
                  ( Hᵉ ∙hᵉ (gᵉ ·lᵉ Lᵉ))
                  ( λ xᵉ → right-whisker-concatᵉ (invᵉ right-unitᵉ) (H'ᵉ xᵉ)))
                ( is-equiv-concat-htpyᵉ
                  ( λ xᵉ → left-whisker-concatᵉ (Hᵉ xᵉ) right-unitᵉ)
                  ( (fᵉ ·lᵉ Kᵉ) ∙hᵉ refl-htpyᵉ ∙hᵉ H'ᵉ))))

  abstract
    is-torsorial-htpy-parallel-cone-refl-htpy-refl-htpyᵉ :
      (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
      is-torsorialᵉ (htpy-parallel-coneᵉ (refl-htpy'ᵉ fᵉ) (refl-htpy'ᵉ gᵉ) cᵉ)
    is-torsorial-htpy-parallel-cone-refl-htpy-refl-htpyᵉ cᵉ =
      is-contr-is-equiv'ᵉ
        ( Σᵉ (coneᵉ fᵉ gᵉ Cᵉ) (htpy-coneᵉ fᵉ gᵉ cᵉ))
        ( totᵉ (htpy-parallel-cone-refl-htpy-htpy-coneᵉ cᵉ))
        ( is-equiv-tot-is-fiberwise-equivᵉ
          ( is-equiv-htpy-parallel-cone-refl-htpy-htpy-coneᵉ cᵉ))
        ( is-torsorial-htpy-coneᵉ fᵉ gᵉ cᵉ)

  abstract
    is-torsorial-htpy-parallel-cone-refl-htpyᵉ :
      {g'ᵉ : Bᵉ → Xᵉ} (Hgᵉ : gᵉ ~ᵉ g'ᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
      is-torsorialᵉ (htpy-parallel-coneᵉ (refl-htpy'ᵉ fᵉ) Hgᵉ cᵉ)
    is-torsorial-htpy-parallel-cone-refl-htpyᵉ =
      ind-htpyᵉ
        ( gᵉ)
        ( λ g''ᵉ Hg'ᵉ →
          (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
          is-torsorialᵉ (htpy-parallel-coneᵉ (refl-htpy'ᵉ fᵉ) Hg'ᵉ cᵉ))
        ( is-torsorial-htpy-parallel-cone-refl-htpy-refl-htpyᵉ)

  abstract
    is-torsorial-htpy-parallel-coneᵉ :
      {f'ᵉ : Aᵉ → Xᵉ} (Hfᵉ : fᵉ ~ᵉ f'ᵉ) {g'ᵉ : Bᵉ → Xᵉ} (Hgᵉ : gᵉ ~ᵉ g'ᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
      is-torsorialᵉ (htpy-parallel-coneᵉ Hfᵉ Hgᵉ cᵉ)
    is-torsorial-htpy-parallel-coneᵉ Hfᵉ {g'ᵉ} =
      ind-htpyᵉ
        ( fᵉ)
        ( λ f''ᵉ Hf'ᵉ →
          (g'ᵉ : Bᵉ → Xᵉ) (Hgᵉ : gᵉ ~ᵉ g'ᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
          is-contrᵉ (Σᵉ (coneᵉ f''ᵉ g'ᵉ Cᵉ) (htpy-parallel-coneᵉ Hf'ᵉ Hgᵉ cᵉ)))
        ( λ g'ᵉ Hgᵉ → is-torsorial-htpy-parallel-cone-refl-htpyᵉ Hgᵉ)
        ( Hfᵉ)
        ( g'ᵉ)
```

#### The type family of homotopies of parallel cones characterizes dependent identifications of cones on the same domain over parallel cospans

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  {fᵉ : Aᵉ → Xᵉ} {gᵉ : Bᵉ → Xᵉ}
  where

  tr-right-tr-left-cone-eq-htpyᵉ :
    {f'ᵉ : Aᵉ → Xᵉ} → fᵉ ~ᵉ f'ᵉ → {g'ᵉ : Bᵉ → Xᵉ} → gᵉ ~ᵉ g'ᵉ → coneᵉ fᵉ gᵉ Cᵉ → coneᵉ f'ᵉ g'ᵉ Cᵉ
  tr-right-tr-left-cone-eq-htpyᵉ {f'ᵉ} Hfᵉ Hgᵉ cᵉ =
    trᵉ
      ( λ yᵉ → coneᵉ f'ᵉ yᵉ Cᵉ)
      ( eq-htpyᵉ Hgᵉ)
      ( trᵉ (λ xᵉ → coneᵉ xᵉ gᵉ Cᵉ) (eq-htpyᵉ Hfᵉ) cᵉ)

  compute-tr-right-tr-left-cone-eq-htpy-refl-htpyᵉ :
    (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
    tr-right-tr-left-cone-eq-htpyᵉ refl-htpyᵉ refl-htpyᵉ cᵉ ＝ᵉ cᵉ
  compute-tr-right-tr-left-cone-eq-htpy-refl-htpyᵉ cᵉ =
    ( apᵉ
      ( λ tᵉ →
        trᵉ
          ( λ g''ᵉ → coneᵉ fᵉ g''ᵉ Cᵉ)
          ( tᵉ)
          ( trᵉ (λ xᵉ → coneᵉ xᵉ gᵉ Cᵉ) (eq-htpyᵉ (refl-htpy'ᵉ fᵉ)) cᵉ))
      ( eq-htpy-refl-htpyᵉ gᵉ)) ∙ᵉ
    ( apᵉ (λ tᵉ → trᵉ (λ f'''ᵉ → coneᵉ f'''ᵉ gᵉ Cᵉ) tᵉ cᵉ) (eq-htpy-refl-htpyᵉ fᵉ))

  htpy-eq-parallel-cone-refl-htpyᵉ :
    (cᵉ c'ᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
    tr-right-tr-left-cone-eq-htpyᵉ refl-htpyᵉ refl-htpyᵉ cᵉ ＝ᵉ c'ᵉ →
    htpy-parallel-coneᵉ (refl-htpy'ᵉ fᵉ) (refl-htpy'ᵉ gᵉ) cᵉ c'ᵉ
  htpy-eq-parallel-cone-refl-htpyᵉ cᵉ c'ᵉ =
    map-inv-is-equiv-precomp-Π-is-equivᵉ
      ( is-equiv-concatᵉ (compute-tr-right-tr-left-cone-eq-htpy-refl-htpyᵉ cᵉ) c'ᵉ)
      ( λ pᵉ → htpy-parallel-coneᵉ (refl-htpy'ᵉ fᵉ) (refl-htpy'ᵉ gᵉ) cᵉ c'ᵉ)
      ( htpy-eq-degenerate-parallel-coneᵉ cᵉ c'ᵉ)

  left-map-triangle-eq-parallel-cone-refl-htpyᵉ :
    (cᵉ c'ᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
    ( ( htpy-eq-parallel-cone-refl-htpyᵉ cᵉ c'ᵉ) ∘ᵉ
      ( concatᵉ (compute-tr-right-tr-left-cone-eq-htpy-refl-htpyᵉ cᵉ) c'ᵉ)) ~ᵉ
    ( htpy-eq-degenerate-parallel-coneᵉ cᵉ c'ᵉ)
  left-map-triangle-eq-parallel-cone-refl-htpyᵉ cᵉ c'ᵉ =
    is-section-map-inv-is-equiv-precomp-Π-is-equivᵉ
      ( is-equiv-concatᵉ (compute-tr-right-tr-left-cone-eq-htpy-refl-htpyᵉ cᵉ) c'ᵉ)
      ( λ pᵉ → htpy-parallel-coneᵉ (refl-htpy'ᵉ fᵉ) (refl-htpy'ᵉ gᵉ) cᵉ c'ᵉ)
      ( htpy-eq-degenerate-parallel-coneᵉ cᵉ c'ᵉ)

  abstract
    htpy-parallel-cone-dependent-eq'ᵉ :
      {g'ᵉ : Bᵉ → Xᵉ} (Hgᵉ : gᵉ ~ᵉ g'ᵉ) →
      (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ fᵉ g'ᵉ Cᵉ) →
      tr-right-tr-left-cone-eq-htpyᵉ refl-htpyᵉ Hgᵉ cᵉ ＝ᵉ c'ᵉ →
      htpy-parallel-coneᵉ (refl-htpy'ᵉ fᵉ) Hgᵉ cᵉ c'ᵉ
    htpy-parallel-cone-dependent-eq'ᵉ =
      ind-htpyᵉ gᵉ
        ( λ g''ᵉ Hg'ᵉ →
          ( cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ fᵉ g''ᵉ Cᵉ) →
          tr-right-tr-left-cone-eq-htpyᵉ refl-htpyᵉ Hg'ᵉ cᵉ ＝ᵉ c'ᵉ →
          htpy-parallel-coneᵉ refl-htpyᵉ Hg'ᵉ cᵉ c'ᵉ)
        ( htpy-eq-parallel-cone-refl-htpyᵉ)

    left-map-triangle-parallel-cone-eq'ᵉ :
      (cᵉ c'ᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
      ( ( htpy-parallel-cone-dependent-eq'ᵉ refl-htpyᵉ cᵉ c'ᵉ) ∘ᵉ
        ( concatᵉ (compute-tr-right-tr-left-cone-eq-htpy-refl-htpyᵉ cᵉ) c'ᵉ)) ~ᵉ
      ( htpy-eq-degenerate-parallel-coneᵉ cᵉ c'ᵉ)
    left-map-triangle-parallel-cone-eq'ᵉ cᵉ c'ᵉ =
      ( right-whisker-compᵉ
        ( multivariable-htpy-eqᵉ 3ᵉ
          ( compute-ind-htpyᵉ gᵉ
            ( λ g''ᵉ Hg'ᵉ →
              ( cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ fᵉ g''ᵉ Cᵉ) →
              tr-right-tr-left-cone-eq-htpyᵉ refl-htpyᵉ Hg'ᵉ cᵉ ＝ᵉ c'ᵉ →
              htpy-parallel-coneᵉ refl-htpyᵉ Hg'ᵉ cᵉ c'ᵉ)
            ( htpy-eq-parallel-cone-refl-htpyᵉ))
          ( cᵉ)
          ( c'ᵉ))
        ( concatᵉ (compute-tr-right-tr-left-cone-eq-htpy-refl-htpyᵉ cᵉ) c'ᵉ)) ∙hᵉ
      ( left-map-triangle-eq-parallel-cone-refl-htpyᵉ cᵉ c'ᵉ)

  abstract
    htpy-parallel-cone-dependent-eqᵉ :
      {f'ᵉ : Aᵉ → Xᵉ} (Hfᵉ : fᵉ ~ᵉ f'ᵉ) {g'ᵉ : Bᵉ → Xᵉ} (Hgᵉ : gᵉ ~ᵉ g'ᵉ) →
      (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ f'ᵉ g'ᵉ Cᵉ) →
      tr-right-tr-left-cone-eq-htpyᵉ Hfᵉ Hgᵉ cᵉ ＝ᵉ c'ᵉ →
      htpy-parallel-coneᵉ Hfᵉ Hgᵉ cᵉ c'ᵉ
    htpy-parallel-cone-dependent-eqᵉ {f'ᵉ} Hfᵉ {g'ᵉ} Hgᵉ cᵉ c'ᵉ pᵉ =
      ind-htpyᵉ fᵉ
        ( λ f''ᵉ Hf'ᵉ →
          ( g'ᵉ : Bᵉ → Xᵉ) (Hgᵉ : gᵉ ~ᵉ g'ᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ f''ᵉ g'ᵉ Cᵉ) →
          ( tr-right-tr-left-cone-eq-htpyᵉ Hf'ᵉ Hgᵉ cᵉ ＝ᵉ c'ᵉ) →
          htpy-parallel-coneᵉ Hf'ᵉ Hgᵉ cᵉ c'ᵉ)
        ( λ g'ᵉ → htpy-parallel-cone-dependent-eq'ᵉ {g'ᵉ = g'ᵉ})
        Hfᵉ g'ᵉ Hgᵉ cᵉ c'ᵉ pᵉ

    left-map-triangle-parallel-cone-eqᵉ :
      (cᵉ c'ᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
      ( ( htpy-parallel-cone-dependent-eqᵉ refl-htpyᵉ refl-htpyᵉ cᵉ c'ᵉ) ∘ᵉ
        ( concatᵉ (compute-tr-right-tr-left-cone-eq-htpy-refl-htpyᵉ cᵉ) c'ᵉ)) ~ᵉ
      ( htpy-eq-degenerate-parallel-coneᵉ cᵉ c'ᵉ)
    left-map-triangle-parallel-cone-eqᵉ cᵉ c'ᵉ =
      ( right-whisker-compᵉ
        ( multivariable-htpy-eqᵉ 5ᵉ
          ( compute-ind-htpyᵉ fᵉ
            ( λ f''ᵉ Hf'ᵉ →
              ( g'ᵉ : Bᵉ → Xᵉ) (Hgᵉ : gᵉ ~ᵉ g'ᵉ)
              (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ f''ᵉ g'ᵉ Cᵉ) →
              ( tr-right-tr-left-cone-eq-htpyᵉ Hf'ᵉ Hgᵉ cᵉ ＝ᵉ c'ᵉ) →
              htpy-parallel-coneᵉ Hf'ᵉ Hgᵉ cᵉ c'ᵉ)
            ( λ g'ᵉ → htpy-parallel-cone-dependent-eq'ᵉ {g'ᵉ = g'ᵉ}))
          ( gᵉ)
          ( refl-htpyᵉ)
          ( cᵉ)
          ( c'ᵉ))
        ( concatᵉ (compute-tr-right-tr-left-cone-eq-htpy-refl-htpyᵉ cᵉ) c'ᵉ)) ∙hᵉ
      ( left-map-triangle-parallel-cone-eq'ᵉ cᵉ c'ᵉ)

  abstract
    is-fiberwise-equiv-htpy-parallel-cone-dependent-eqᵉ :
      {f'ᵉ : Aᵉ → Xᵉ} (Hfᵉ : fᵉ ~ᵉ f'ᵉ) {g'ᵉ : Bᵉ → Xᵉ} (Hgᵉ : gᵉ ~ᵉ g'ᵉ) →
      (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ f'ᵉ g'ᵉ Cᵉ) →
      is-equivᵉ (htpy-parallel-cone-dependent-eqᵉ Hfᵉ Hgᵉ cᵉ c'ᵉ)
    is-fiberwise-equiv-htpy-parallel-cone-dependent-eqᵉ {f'ᵉ} Hfᵉ {g'ᵉ} Hgᵉ cᵉ c'ᵉ =
      ind-htpyᵉ fᵉ
        ( λ f'ᵉ Hfᵉ →
          ( g'ᵉ : Bᵉ → Xᵉ) (Hgᵉ : gᵉ ~ᵉ g'ᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ f'ᵉ g'ᵉ Cᵉ) →
            is-equivᵉ (htpy-parallel-cone-dependent-eqᵉ Hfᵉ Hgᵉ cᵉ c'ᵉ))
        ( λ g'ᵉ Hgᵉ cᵉ c'ᵉ →
          ind-htpyᵉ gᵉ
            ( λ g'ᵉ Hgᵉ →
              ( cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ fᵉ g'ᵉ Cᵉ) →
                is-equivᵉ (htpy-parallel-cone-dependent-eqᵉ refl-htpyᵉ Hgᵉ cᵉ c'ᵉ))
            ( λ cᵉ c'ᵉ →
              is-equiv-right-map-triangleᵉ
                ( htpy-eq-degenerate-parallel-coneᵉ cᵉ c'ᵉ)
                ( htpy-parallel-cone-dependent-eqᵉ refl-htpyᵉ refl-htpyᵉ cᵉ c'ᵉ)
                ( concatᵉ (compute-tr-right-tr-left-cone-eq-htpy-refl-htpyᵉ cᵉ) c'ᵉ)
                ( inv-htpyᵉ (left-map-triangle-parallel-cone-eqᵉ cᵉ c'ᵉ))
                ( fundamental-theorem-idᵉ
                  ( is-torsorial-htpy-parallel-coneᵉ
                    ( refl-htpy'ᵉ fᵉ)
                    ( refl-htpy'ᵉ gᵉ)
                    ( cᵉ))
                  ( htpy-eq-degenerate-parallel-coneᵉ cᵉ) c'ᵉ)
                ( is-equiv-concatᵉ
                  ( compute-tr-right-tr-left-cone-eq-htpy-refl-htpyᵉ cᵉ)
                  ( c'ᵉ)))
            ( Hgᵉ)
            ( cᵉ)
            ( c'ᵉ))
        ( Hfᵉ)
        ( g'ᵉ)
        ( Hgᵉ)
        ( cᵉ)
        ( c'ᵉ)

  dependent-eq-htpy-parallel-coneᵉ :
    {f'ᵉ : Aᵉ → Xᵉ} (Hfᵉ : fᵉ ~ᵉ f'ᵉ) {g'ᵉ : Bᵉ → Xᵉ} (Hgᵉ : gᵉ ~ᵉ g'ᵉ) →
    (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ f'ᵉ g'ᵉ Cᵉ) →
    htpy-parallel-coneᵉ Hfᵉ Hgᵉ cᵉ c'ᵉ →
    tr-right-tr-left-cone-eq-htpyᵉ Hfᵉ Hgᵉ cᵉ ＝ᵉ c'ᵉ
  dependent-eq-htpy-parallel-coneᵉ Hfᵉ Hgᵉ cᵉ c'ᵉ =
    map-inv-is-equivᵉ
      ( is-fiberwise-equiv-htpy-parallel-cone-dependent-eqᵉ Hfᵉ Hgᵉ cᵉ c'ᵉ)
```

## Table of files about pullbacks

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ pullbacksᵉ asᵉ aᵉ generalᵉ concept.ᵉ

{{#includeᵉ tables/pullbacks.mdᵉ}}
