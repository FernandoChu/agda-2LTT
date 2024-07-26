# Morphisms of pointed arrows

```agda
module structured-types.morphisms-pointed-arrowsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-homotopiesᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.commuting-triangles-of-identificationsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.path-algebraᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ

open import structured-types.commuting-squares-of-pointed-homotopiesᵉ
open import structured-types.commuting-squares-of-pointed-mapsᵉ
open import structured-types.pointed-2-homotopiesᵉ
open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.whiskering-pointed-2-homotopies-concatenationᵉ
open import structured-types.whiskering-pointed-homotopies-compositionᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "morphismᵉ ofᵉ pointedᵉ arrows"ᵉ Agda=hom-pointed-arrowᵉ}} fromᵉ aᵉ
[pointedᵉ map](structured-types.pointed-maps.mdᵉ) `fᵉ : Aᵉ →∗ᵉ B`ᵉ to aᵉ pointedᵉ mapᵉ
`gᵉ : Xᵉ →∗ᵉ Y`ᵉ isᵉ aᵉ [triple](foundation.dependent-pair-types.mdᵉ) `(iᵉ ,ᵉ jᵉ ,ᵉ H)`ᵉ
consistingᵉ ofᵉ pointedᵉ mapsᵉ `iᵉ : Aᵉ →∗ᵉ X`ᵉ andᵉ `jᵉ : Bᵉ →∗ᵉ Y`ᵉ andᵉ aᵉ
[pointedᵉ homotopy](structured-types.pointed-homotopies.mdᵉ)
`Hᵉ : jᵉ ∘∗ᵉ fᵉ ~∗ᵉ gᵉ ∘∗ᵉ i`ᵉ witnessingᵉ thatᵉ theᵉ squareᵉ

```text
        iᵉ
    Aᵉ ----->ᵉ Xᵉ
    |        |
  fᵉ |        | gᵉ
    ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ
        jᵉ
```

[commutes](structured-types.commuting-squares-of-pointed-maps.md).ᵉ Morphismsᵉ ofᵉ
pointedᵉ arrowsᵉ canᵉ beᵉ composedᵉ horizontallyᵉ orᵉ verticallyᵉ byᵉ pastingᵉ ofᵉ squares.ᵉ

## Definitions

### Morphisms of pointed arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {Xᵉ : Pointed-Typeᵉ l3ᵉ} {Yᵉ : Pointed-Typeᵉ l4ᵉ}
  (fᵉ : Aᵉ →∗ᵉ Bᵉ) (gᵉ : Xᵉ →∗ᵉ Yᵉ)
  where

  coherence-hom-pointed-arrowᵉ :
    (Aᵉ →∗ᵉ Xᵉ) → (Bᵉ →∗ᵉ Yᵉ) → UUᵉ (l1ᵉ ⊔ l4ᵉ)
  coherence-hom-pointed-arrowᵉ iᵉ = coherence-square-pointed-mapsᵉ iᵉ fᵉ gᵉ

  hom-pointed-arrowᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-pointed-arrowᵉ =
    Σᵉ (Aᵉ →∗ᵉ Xᵉ) (λ iᵉ → Σᵉ (Bᵉ →∗ᵉ Yᵉ) (coherence-hom-pointed-arrowᵉ iᵉ))

  pointed-map-domain-hom-pointed-arrowᵉ :
    hom-pointed-arrowᵉ → Aᵉ →∗ᵉ Xᵉ
  pointed-map-domain-hom-pointed-arrowᵉ = pr1ᵉ

  map-domain-hom-pointed-arrowᵉ :
    hom-pointed-arrowᵉ → type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ Xᵉ
  map-domain-hom-pointed-arrowᵉ hᵉ =
    map-pointed-mapᵉ (pointed-map-domain-hom-pointed-arrowᵉ hᵉ)

  preserves-point-map-domain-hom-pointed-arrowᵉ :
    (hᵉ : hom-pointed-arrowᵉ) →
    map-domain-hom-pointed-arrowᵉ hᵉ (point-Pointed-Typeᵉ Aᵉ) ＝ᵉ
    point-Pointed-Typeᵉ Xᵉ
  preserves-point-map-domain-hom-pointed-arrowᵉ hᵉ =
    preserves-point-pointed-mapᵉ (pointed-map-domain-hom-pointed-arrowᵉ hᵉ)

  pointed-map-codomain-hom-pointed-arrowᵉ :
    hom-pointed-arrowᵉ → Bᵉ →∗ᵉ Yᵉ
  pointed-map-codomain-hom-pointed-arrowᵉ = pr1ᵉ ∘ᵉ pr2ᵉ

  map-codomain-hom-pointed-arrowᵉ :
    hom-pointed-arrowᵉ → type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ Yᵉ
  map-codomain-hom-pointed-arrowᵉ hᵉ =
    map-pointed-mapᵉ (pointed-map-codomain-hom-pointed-arrowᵉ hᵉ)

  preserves-point-map-codomain-hom-pointed-arrowᵉ :
    (hᵉ : hom-pointed-arrowᵉ) →
    map-codomain-hom-pointed-arrowᵉ hᵉ (point-Pointed-Typeᵉ Bᵉ) ＝ᵉ
    point-Pointed-Typeᵉ Yᵉ
  preserves-point-map-codomain-hom-pointed-arrowᵉ hᵉ =
    preserves-point-pointed-mapᵉ (pointed-map-codomain-hom-pointed-arrowᵉ hᵉ)

  coh-hom-pointed-arrowᵉ :
    (hᵉ : hom-pointed-arrowᵉ) →
    coherence-hom-pointed-arrowᵉ
      ( pointed-map-domain-hom-pointed-arrowᵉ hᵉ)
      ( pointed-map-codomain-hom-pointed-arrowᵉ hᵉ)
  coh-hom-pointed-arrowᵉ = pr2ᵉ ∘ᵉ pr2ᵉ

  htpy-coh-hom-pointed-arrowᵉ :
    (hᵉ : hom-pointed-arrowᵉ) →
    coherence-hom-arrowᵉ
      ( map-pointed-mapᵉ fᵉ)
      ( map-pointed-mapᵉ gᵉ)
      ( map-domain-hom-pointed-arrowᵉ hᵉ)
      ( map-codomain-hom-pointed-arrowᵉ hᵉ)
  htpy-coh-hom-pointed-arrowᵉ hᵉ =
    htpy-pointed-htpyᵉ
      ( coh-hom-pointed-arrowᵉ hᵉ)
```

### Transposing morphisms of pointed arrows

Theᵉ
{{#conceptᵉ "transposition"ᵉ Disambiguation="morphismᵉ ofᵉ pointedᵉ arrows"ᵉ Agda=transpose-hom-pointed-arrowᵉ}}
ofᵉ aᵉ morphismᵉ ofᵉ pointedᵉ arrowsᵉ

```text
        iᵉ
    Aᵉ ----->ᵉ Xᵉ
    |        |
  fᵉ |        | gᵉ
    ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ
        jᵉ
```

isᵉ theᵉ morphismᵉ ofᵉ pointedᵉ arrowsᵉ

```text
        fᵉ
    Aᵉ ----->ᵉ Bᵉ
    |        |
  iᵉ |        | jᵉ
    ∨ᵉ        ∨ᵉ
    Xᵉ ----->ᵉ Y.ᵉ
        gᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {Xᵉ : Pointed-Typeᵉ l3ᵉ} {Yᵉ : Pointed-Typeᵉ l4ᵉ}
  (fᵉ : Aᵉ →∗ᵉ Bᵉ) (gᵉ : Xᵉ →∗ᵉ Yᵉ) (αᵉ : hom-pointed-arrowᵉ fᵉ gᵉ)
  where

  pointed-map-domain-transpose-hom-pointed-arrowᵉ : Aᵉ →∗ᵉ Bᵉ
  pointed-map-domain-transpose-hom-pointed-arrowᵉ = fᵉ

  pointed-map-codomain-transpose-hom-pointed-arrowᵉ : Xᵉ →∗ᵉ Yᵉ
  pointed-map-codomain-transpose-hom-pointed-arrowᵉ = gᵉ

  coh-transpose-hom-pointed-arrowᵉ :
    coherence-hom-pointed-arrowᵉ
      ( pointed-map-domain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ)
      ( pointed-map-codomain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ)
      ( pointed-map-domain-transpose-hom-pointed-arrowᵉ)
      ( pointed-map-codomain-transpose-hom-pointed-arrowᵉ)
  coh-transpose-hom-pointed-arrowᵉ =
    inv-pointed-htpyᵉ
      ( coh-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ)

  transpose-hom-pointed-arrowᵉ :
    hom-pointed-arrowᵉ
      ( pointed-map-domain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ)
      ( pointed-map-codomain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ)
  pr1ᵉ transpose-hom-pointed-arrowᵉ =
    pointed-map-domain-transpose-hom-pointed-arrowᵉ
  pr1ᵉ (pr2ᵉ transpose-hom-pointed-arrowᵉ) =
    pointed-map-codomain-transpose-hom-pointed-arrowᵉ
  pr2ᵉ (pr2ᵉ transpose-hom-pointed-arrowᵉ) = coh-transpose-hom-pointed-arrowᵉ
```

### The identity morphism of pointed arrows

Theᵉ identityᵉ morphismᵉ ofᵉ pointedᵉ arrowsᵉ isᵉ definedᵉ asᵉ

```text
        idᵉ
    Aᵉ ----->ᵉ Aᵉ
    |        |
  fᵉ |        | fᵉ
    ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Bᵉ
        idᵉ
```

where theᵉ pointedᵉ homotopyᵉ `idᵉ ∘∗ᵉ fᵉ ~∗ᵉ fᵉ ∘∗ᵉ id`ᵉ isᵉ theᵉ concatenationᵉ ofᵉ theᵉ leftᵉ
unitᵉ lawᵉ pointedᵉ homotopyᵉ andᵉ theᵉ inverseᵉ pointedᵉ homotopyᵉ ofᵉ theᵉ rightᵉ unitᵉ lawᵉ
pointedᵉ homotopy.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} {fᵉ : Aᵉ →∗ᵉ Bᵉ}
  where

  id-hom-pointed-arrowᵉ : hom-pointed-arrowᵉ fᵉ fᵉ
  pr1ᵉ id-hom-pointed-arrowᵉ = id-pointed-mapᵉ
  pr1ᵉ (pr2ᵉ id-hom-pointed-arrowᵉ) = id-pointed-mapᵉ
  pr2ᵉ (pr2ᵉ id-hom-pointed-arrowᵉ) =
    concat-pointed-htpyᵉ
      ( left-unit-law-comp-pointed-mapᵉ fᵉ)
      ( inv-pointed-htpyᵉ (right-unit-law-comp-pointed-mapᵉ fᵉ))
```

### Composition of morphisms of pointed arrows

Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ theᵉ formᵉ

```text
        α₀ᵉ       β₀ᵉ
    Aᵉ ----->ᵉ Xᵉ ----->ᵉ Uᵉ
    |        |        |
  fᵉ |   αᵉ  gᵉ |   βᵉ    | hᵉ
    ∨ᵉ        ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ ----->ᵉ V.ᵉ
        α₁ᵉ       β₁ᵉ
```

Thenᵉ theᵉ outerᵉ rectangleᵉ commutesᵉ byᵉ horizontalᵉ pastingᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ
pointedᵉ maps.ᵉ Theᵉ
{{#conceptᵉ "composition"ᵉ Disambiguation="morphismᵉ ofᵉ pointedᵉ arrows"ᵉ Agda=comp-hom-pointed-arrowᵉ}}
ofᵉ `βᵉ : gᵉ → h`ᵉ with `αᵉ : fᵉ → g`ᵉ isᵉ thereforeᵉ definedᵉ to beᵉ

```text
        β₀ᵉ ∘ᵉ α₀ᵉ
    Aᵉ ---------->ᵉ Uᵉ
    |             |
  fᵉ |    αᵉ □ᵉ βᵉ    | hᵉ
    ∨ᵉ             ∨ᵉ
    Bᵉ ---------->ᵉ V.ᵉ
        β₁ᵉ ∘ᵉ α₁ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {Xᵉ : Pointed-Typeᵉ l3ᵉ} {Yᵉ : Pointed-Typeᵉ l4ᵉ}
  {Uᵉ : Pointed-Typeᵉ l5ᵉ} {Vᵉ : Pointed-Typeᵉ l6ᵉ}
  (fᵉ : Aᵉ →∗ᵉ Bᵉ) (gᵉ : Xᵉ →∗ᵉ Yᵉ) (hᵉ : Uᵉ →∗ᵉ Vᵉ) (bᵉ : hom-pointed-arrowᵉ gᵉ hᵉ)
  (aᵉ : hom-pointed-arrowᵉ fᵉ gᵉ)
  where

  pointed-map-domain-comp-hom-pointed-arrowᵉ : Aᵉ →∗ᵉ Uᵉ
  pointed-map-domain-comp-hom-pointed-arrowᵉ =
    pointed-map-domain-hom-pointed-arrowᵉ gᵉ hᵉ bᵉ ∘∗ᵉ
    pointed-map-domain-hom-pointed-arrowᵉ fᵉ gᵉ aᵉ

  map-domain-comp-hom-pointed-arrowᵉ :
    type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ Uᵉ
  map-domain-comp-hom-pointed-arrowᵉ =
    map-pointed-mapᵉ pointed-map-domain-comp-hom-pointed-arrowᵉ

  preserves-point-map-domain-comp-hom-pointed-arrowᵉ :
    map-domain-comp-hom-pointed-arrowᵉ (point-Pointed-Typeᵉ Aᵉ) ＝ᵉ
    point-Pointed-Typeᵉ Uᵉ
  preserves-point-map-domain-comp-hom-pointed-arrowᵉ =
    preserves-point-pointed-mapᵉ pointed-map-domain-comp-hom-pointed-arrowᵉ

  pointed-map-codomain-comp-hom-pointed-arrowᵉ : Bᵉ →∗ᵉ Vᵉ
  pointed-map-codomain-comp-hom-pointed-arrowᵉ =
    pointed-map-codomain-hom-pointed-arrowᵉ gᵉ hᵉ bᵉ ∘∗ᵉ
    pointed-map-codomain-hom-pointed-arrowᵉ fᵉ gᵉ aᵉ

  map-codomain-comp-hom-pointed-arrowᵉ :
    type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ Vᵉ
  map-codomain-comp-hom-pointed-arrowᵉ =
    map-pointed-mapᵉ pointed-map-codomain-comp-hom-pointed-arrowᵉ

  preserves-point-map-codomain-comp-hom-pointed-arrowᵉ :
    map-codomain-comp-hom-pointed-arrowᵉ (point-Pointed-Typeᵉ Bᵉ) ＝ᵉ
    point-Pointed-Typeᵉ Vᵉ
  preserves-point-map-codomain-comp-hom-pointed-arrowᵉ =
    preserves-point-pointed-mapᵉ pointed-map-codomain-comp-hom-pointed-arrowᵉ

  coh-comp-hom-pointed-arrowᵉ :
    coherence-hom-pointed-arrowᵉ fᵉ hᵉ
      ( pointed-map-domain-comp-hom-pointed-arrowᵉ)
      ( pointed-map-codomain-comp-hom-pointed-arrowᵉ)
  coh-comp-hom-pointed-arrowᵉ =
    horizontal-pasting-coherence-square-pointed-mapsᵉ
      ( pointed-map-domain-hom-pointed-arrowᵉ fᵉ gᵉ aᵉ)
      ( pointed-map-domain-hom-pointed-arrowᵉ gᵉ hᵉ bᵉ)
      ( fᵉ)
      ( gᵉ)
      ( hᵉ)
      ( pointed-map-codomain-hom-pointed-arrowᵉ fᵉ gᵉ aᵉ)
      ( pointed-map-codomain-hom-pointed-arrowᵉ gᵉ hᵉ bᵉ)
      ( coh-hom-pointed-arrowᵉ fᵉ gᵉ aᵉ)
      ( coh-hom-pointed-arrowᵉ gᵉ hᵉ bᵉ)

  comp-hom-pointed-arrowᵉ : hom-pointed-arrowᵉ fᵉ hᵉ
  pr1ᵉ comp-hom-pointed-arrowᵉ = pointed-map-domain-comp-hom-pointed-arrowᵉ
  pr1ᵉ (pr2ᵉ comp-hom-pointed-arrowᵉ) = pointed-map-codomain-comp-hom-pointed-arrowᵉ
  pr2ᵉ (pr2ᵉ comp-hom-pointed-arrowᵉ) = coh-comp-hom-pointed-arrowᵉ
```

### Homotopies of morphisms of pointed arrows

Aᵉ
{{#conceptᵉ "homotopyᵉ ofᵉ morphismsᵉ ofᵉ pointedᵉ arrows"ᵉ Agda=htpy-hom-pointed-arrowᵉ}}
fromᵉ `(iᵉ ,ᵉ jᵉ ,ᵉ H)`ᵉ to `(i'ᵉ ,ᵉ j'ᵉ ,ᵉ H')`ᵉ isᵉ aᵉ tripleᵉ `(Iᵉ ,ᵉ Jᵉ ,ᵉ K)`ᵉ consistingᵉ ofᵉ
pointedᵉ homotopiesᵉ `Iᵉ : iᵉ ~∗ᵉ i'`ᵉ andᵉ `Jᵉ : jᵉ ~∗ᵉ j'`ᵉ andᵉ aᵉ pointedᵉ `2`-homotopyᵉ
`K`ᵉ witnessingᵉ thatᵉ theᵉ
[squareᵉ ofᵉ pointedᵉ homotopies](structured-types.commuting-squares-of-pointed-homotopies.mdᵉ)

```text
            Jᵉ ·rᵉ fᵉ
  (jᵉ ∘∗ᵉ fᵉ) -------->ᵉ (j'ᵉ ∘∗ᵉ fᵉ)
     |                   |
   Hᵉ |                   | H'ᵉ
     ∨ᵉ                   ∨ᵉ
  (gᵉ ∘∗ᵉ iᵉ) --------->ᵉ (gᵉ ∘∗ᵉ i'ᵉ)
             gᵉ ·lᵉ Iᵉ
```

commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {Xᵉ : Pointed-Typeᵉ l3ᵉ} {Yᵉ : Pointed-Typeᵉ l4ᵉ}
  (fᵉ : Aᵉ →∗ᵉ Bᵉ) (gᵉ : Xᵉ →∗ᵉ Yᵉ) (αᵉ : hom-pointed-arrowᵉ fᵉ gᵉ)
  where

  coherence-htpy-hom-pointed-arrowᵉ :
    (βᵉ : hom-pointed-arrowᵉ fᵉ gᵉ)
    (Iᵉ :
      pointed-map-domain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ ~∗ᵉ
      pointed-map-domain-hom-pointed-arrowᵉ fᵉ gᵉ βᵉ)
    (Jᵉ :
      pointed-map-codomain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ ~∗ᵉ
      pointed-map-codomain-hom-pointed-arrowᵉ fᵉ gᵉ βᵉ) →
    UUᵉ (l1ᵉ ⊔ l4ᵉ)
  coherence-htpy-hom-pointed-arrowᵉ βᵉ Iᵉ Jᵉ =
    coherence-square-pointed-homotopiesᵉ
      ( right-whisker-comp-pointed-htpyᵉ _ _ Jᵉ fᵉ)
      ( coh-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ)
      ( coh-hom-pointed-arrowᵉ fᵉ gᵉ βᵉ)
      ( left-whisker-comp-pointed-htpyᵉ gᵉ _ _ Iᵉ)

  htpy-hom-pointed-arrowᵉ :
    (βᵉ : hom-pointed-arrowᵉ fᵉ gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-hom-pointed-arrowᵉ βᵉ =
    Σᵉ ( pointed-map-domain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ ~∗ᵉ
        pointed-map-domain-hom-pointed-arrowᵉ fᵉ gᵉ βᵉ)
      ( λ Iᵉ →
        Σᵉ ( pointed-map-codomain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ ~∗ᵉ
            pointed-map-codomain-hom-pointed-arrowᵉ fᵉ gᵉ βᵉ)
          ( coherence-htpy-hom-pointed-arrowᵉ βᵉ Iᵉ))

  module _
    (βᵉ : hom-pointed-arrowᵉ fᵉ gᵉ) (ηᵉ : htpy-hom-pointed-arrowᵉ βᵉ)
    where

    pointed-htpy-domain-htpy-hom-pointed-arrowᵉ :
      pointed-map-domain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ ~∗ᵉ
      pointed-map-domain-hom-pointed-arrowᵉ fᵉ gᵉ βᵉ
    pointed-htpy-domain-htpy-hom-pointed-arrowᵉ = pr1ᵉ ηᵉ

    pointed-htpy-codomain-htpy-hom-pointed-arrowᵉ :
      pointed-map-codomain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ ~∗ᵉ
      pointed-map-codomain-hom-pointed-arrowᵉ fᵉ gᵉ βᵉ
    pointed-htpy-codomain-htpy-hom-pointed-arrowᵉ = pr1ᵉ (pr2ᵉ ηᵉ)

    coh-htpy-hom-pointed-arrowᵉ :
      coherence-htpy-hom-pointed-arrowᵉ βᵉ
        ( pointed-htpy-domain-htpy-hom-pointed-arrowᵉ)
        ( pointed-htpy-codomain-htpy-hom-pointed-arrowᵉ)
    coh-htpy-hom-pointed-arrowᵉ = pr2ᵉ (pr2ᵉ ηᵉ)
```

### The reflexive homotopy of pointed arrows

Considerᵉ aᵉ morphismᵉ ofᵉ pointedᵉ arrowsᵉ

```text
                α₀ᵉ
            Aᵉ ----->ᵉ Xᵉ
            |        |
  (f₀ᵉ ,ᵉ f₁ᵉ) |   α₂ᵉ   | (g₀ᵉ ,ᵉ g₁ᵉ)
            ∨ᵉ        ∨ᵉ
            Bᵉ ----->ᵉ Yᵉ
                α₁ᵉ
```

fromᵉ `fᵉ : Aᵉ →∗ᵉ B`ᵉ to `gᵉ : Xᵉ →∗ᵉ Y`.ᵉ Theᵉ reflexiveᵉ homotopyᵉ ofᵉ morphismsᵉ ofᵉ arrowsᵉ
`rᵉ :=ᵉ (r₀ᵉ ,ᵉ r₁ᵉ ,ᵉ r₂)`ᵉ onᵉ `αᵉ :=ᵉ (α₀ᵉ ,ᵉ α₁ᵉ ,ᵉ α₂)`ᵉ isᵉ givenᵉ byᵉ

```text
  r₀ᵉ :=ᵉ refl-pointed-htpyᵉ : α₀ᵉ ~∗ᵉ α₀ᵉ
  r₁ᵉ :=ᵉ refl-pointed-htpyᵉ : α₁ᵉ ~∗ᵉ α₁ᵉ
```

andᵉ aᵉ pointedᵉ `2`-homotopyᵉ `r₂`ᵉ witnessingᵉ thatᵉ theᵉ squareᵉ ofᵉ pointedᵉ homotopiesᵉ

```text
            r₁ᵉ ·rᵉ fᵉ
  (α₁ᵉ ∘ᵉ fᵉ) -------->ᵉ (α₁ᵉ ∘ᵉ fᵉ)
      |                  |
   α₂ᵉ |                  | α₂ᵉ
      ∨ᵉ                  ∨ᵉ
   (gᵉ ∘ᵉ α₀ᵉ) -------->ᵉ (gᵉ ∘ᵉ α₀ᵉ)
             gᵉ ·lᵉ r₀ᵉ
```

commutes.ᵉ Noteᵉ thatᵉ `r₁ᵉ ·rᵉ fᵉ ~∗ᵉ refl-pointed-htpy`ᵉ andᵉ
`gᵉ ·lᵉ r₀ᵉ ≐ᵉ refl-pointed-htpy`.ᵉ Byᵉ
[whiskeringᵉ ofᵉ pointedᵉ `2`-homotopies](structured-types.whiskering-pointed-2-homotopies-concatenation.mdᵉ)
with respectᵉ to concatenationᵉ itᵉ followsᵉ thatᵉ

```text
  (r₁ᵉ ·rᵉ fᵉ) ∙hᵉ α₂ᵉ ~∗ᵉ refl-pointed-htpyᵉ ∙hᵉ α₂ᵉ ~∗ᵉ α₂.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {Xᵉ : Pointed-Typeᵉ l3ᵉ} {Yᵉ : Pointed-Typeᵉ l4ᵉ}
  (fᵉ : Aᵉ →∗ᵉ Bᵉ) (gᵉ : Xᵉ →∗ᵉ Yᵉ) (αᵉ : hom-pointed-arrowᵉ fᵉ gᵉ)
  where

  pointed-htpy-domain-refl-htpy-hom-pointed-arrowᵉ :
    pointed-map-domain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ ~∗ᵉ
    pointed-map-domain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ
  pointed-htpy-domain-refl-htpy-hom-pointed-arrowᵉ = refl-pointed-htpyᵉ _

  pointed-htpy-codomain-refl-htpy-hom-pointed-arrowᵉ :
    pointed-map-codomain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ ~∗ᵉ
    pointed-map-codomain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ
  pointed-htpy-codomain-refl-htpy-hom-pointed-arrowᵉ = refl-pointed-htpyᵉ _

  coh-refl-htpy-hom-pointed-arrowᵉ :
    coherence-htpy-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ αᵉ
      ( pointed-htpy-domain-refl-htpy-hom-pointed-arrowᵉ)
      ( pointed-htpy-codomain-refl-htpy-hom-pointed-arrowᵉ)
  coh-refl-htpy-hom-pointed-arrowᵉ =
    concat-pointed-2-htpyᵉ
      ( right-unit-law-concat-pointed-htpyᵉ (coh-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ))
      ( inv-pointed-2-htpyᵉ
        ( concat-pointed-2-htpyᵉ
          ( right-whisker-concat-pointed-2-htpyᵉ
            ( right-whisker-comp-pointed-htpyᵉ
              ( pointed-map-codomain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ)
              ( pointed-map-codomain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ)
              ( pointed-htpy-codomain-refl-htpy-hom-pointed-arrowᵉ)
              ( fᵉ))
            ( refl-pointed-htpyᵉ _)
            ( compute-refl-right-whisker-comp-pointed-htpyᵉ
              ( pointed-map-codomain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ)
              ( fᵉ))
            ( coh-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ))
          ( left-unit-law-concat-pointed-htpyᵉ (coh-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ))))

  refl-htpy-hom-pointed-arrowᵉ : htpy-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ αᵉ
  pr1ᵉ refl-htpy-hom-pointed-arrowᵉ =
    pointed-htpy-domain-refl-htpy-hom-pointed-arrowᵉ
  pr1ᵉ (pr2ᵉ refl-htpy-hom-pointed-arrowᵉ) =
    pointed-htpy-codomain-refl-htpy-hom-pointed-arrowᵉ
  pr2ᵉ (pr2ᵉ refl-htpy-hom-pointed-arrowᵉ) =
    coh-refl-htpy-hom-pointed-arrowᵉ
```

### Characterization of the identity types of morphisms of pointed arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {Xᵉ : Pointed-Typeᵉ l3ᵉ} {Yᵉ : Pointed-Typeᵉ l4ᵉ}
  (fᵉ : Aᵉ →∗ᵉ Bᵉ) (gᵉ : Xᵉ →∗ᵉ Yᵉ) (αᵉ : hom-pointed-arrowᵉ fᵉ gᵉ)
  where

  is-torsorial-htpy-hom-pointed-arrowᵉ :
    is-torsorialᵉ (htpy-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ)
  is-torsorial-htpy-hom-pointed-arrowᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-pointed-htpyᵉ _)
      ( pointed-map-domain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ ,ᵉ refl-pointed-htpyᵉ _)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-pointed-htpyᵉ _)
        ( pointed-map-codomain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ ,ᵉ refl-pointed-htpyᵉ _)
        ( is-contr-equiv'ᵉ _
          ( equiv-totᵉ
            ( λ Hᵉ →
              equiv-concat-pointed-2-htpy'ᵉ
                ( inv-pointed-2-htpyᵉ
                  ( concat-pointed-2-htpyᵉ
                    ( right-whisker-concat-pointed-2-htpyᵉ _ _
                      ( compute-refl-right-whisker-comp-pointed-htpyᵉ
                        ( pointed-map-codomain-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ)
                        ( fᵉ))
                      ( Hᵉ))
                    ( left-unit-law-concat-pointed-htpyᵉ Hᵉ)))))
          ( is-torsorial-pointed-2-htpyᵉ
            ( concat-pointed-htpyᵉ
              ( coh-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ)
              ( refl-pointed-htpyᵉ _)))))

  htpy-eq-hom-pointed-arrowᵉ :
    (βᵉ : hom-pointed-arrowᵉ fᵉ gᵉ) → αᵉ ＝ᵉ βᵉ → htpy-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ βᵉ
  htpy-eq-hom-pointed-arrowᵉ βᵉ reflᵉ = refl-htpy-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ

  is-equiv-htpy-eq-hom-pointed-arrowᵉ :
    (βᵉ : hom-pointed-arrowᵉ fᵉ gᵉ) → is-equivᵉ (htpy-eq-hom-pointed-arrowᵉ βᵉ)
  is-equiv-htpy-eq-hom-pointed-arrowᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-hom-pointed-arrowᵉ)
      ( htpy-eq-hom-pointed-arrowᵉ)

  extensionality-hom-pointed-arrowᵉ :
    (βᵉ : hom-pointed-arrowᵉ fᵉ gᵉ) → (αᵉ ＝ᵉ βᵉ) ≃ᵉ htpy-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ βᵉ
  pr1ᵉ (extensionality-hom-pointed-arrowᵉ βᵉ) =
    htpy-eq-hom-pointed-arrowᵉ βᵉ
  pr2ᵉ (extensionality-hom-pointed-arrowᵉ βᵉ) =
    is-equiv-htpy-eq-hom-pointed-arrowᵉ βᵉ

  eq-htpy-hom-pointed-arrowᵉ :
    (βᵉ : hom-pointed-arrowᵉ fᵉ gᵉ) → htpy-hom-pointed-arrowᵉ fᵉ gᵉ αᵉ βᵉ → αᵉ ＝ᵉ βᵉ
  eq-htpy-hom-pointed-arrowᵉ βᵉ =
    map-inv-equivᵉ (extensionality-hom-pointed-arrowᵉ βᵉ)
```

## See also

-ᵉ [Equivalencesᵉ ofᵉ pointedᵉ arrows](structured-types.equivalences-pointed-arrows.mdᵉ)
-ᵉ [Morphismsᵉ ofᵉ twistedᵉ pointedᵉ arrows](structured-types.morphisms-twisted-pointed-arrows.mdᵉ)