# Morphisms of types equipped with endomorphisms

```agda
module structured-types.morphisms-types-equipped-with-endomorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import structured-types.types-equipped-with-endomorphismsᵉ
```

</details>

## Idea

Considerᵉ twoᵉ
[typesᵉ equippedᵉ with anᵉ endomorphism](structured-types.types-equipped-with-endomorphisms.mdᵉ)
`(X,f)`ᵉ andᵉ `(Y,g)`.ᵉ Aᵉ **morphism**ᵉ fromᵉ `(X,f)`ᵉ to `(Y,g)`ᵉ consistsᵉ ofᵉ aᵉ mapᵉ
`hᵉ : Xᵉ → Y`ᵉ equippedᵉ with aᵉ [homotopy](foundation-core.homotopies.mdᵉ) witnessingᵉ
thatᵉ theᵉ squareᵉ

```text
      hᵉ
  Xᵉ ----->ᵉ Yᵉ
  |        |
 f|ᵉ        |gᵉ
  ∨ᵉ        ∨ᵉ
  Xᵉ ----->ᵉ Yᵉ
      hᵉ
```

[commutes](foundation.commuting-squares-of-maps.md).ᵉ

## Definition

### Morphisms of types equipped with endomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Xᵉ : Type-With-Endomorphismᵉ l1ᵉ) (Yᵉ : Type-With-Endomorphismᵉ l2ᵉ)
  where

  hom-Type-With-Endomorphismᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Type-With-Endomorphismᵉ =
    Σᵉ ( type-Type-With-Endomorphismᵉ Xᵉ → type-Type-With-Endomorphismᵉ Yᵉ)
      ( λ fᵉ →
        coherence-square-mapsᵉ
          ( fᵉ)
          ( endomorphism-Type-With-Endomorphismᵉ Xᵉ)
          ( endomorphism-Type-With-Endomorphismᵉ Yᵉ)
          ( fᵉ))

  map-hom-Type-With-Endomorphismᵉ :
    hom-Type-With-Endomorphismᵉ →
    type-Type-With-Endomorphismᵉ Xᵉ → type-Type-With-Endomorphismᵉ Yᵉ
  map-hom-Type-With-Endomorphismᵉ = pr1ᵉ

  coherence-square-hom-Type-With-Endomorphismᵉ :
    (fᵉ : hom-Type-With-Endomorphismᵉ) →
    coherence-square-mapsᵉ
      ( map-hom-Type-With-Endomorphismᵉ fᵉ)
      ( endomorphism-Type-With-Endomorphismᵉ Xᵉ)
      ( endomorphism-Type-With-Endomorphismᵉ Yᵉ)
      ( map-hom-Type-With-Endomorphismᵉ fᵉ)
  coherence-square-hom-Type-With-Endomorphismᵉ = pr2ᵉ
```

### Homotopies of morphisms of types equipped with endomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Xᵉ : Type-With-Endomorphismᵉ l1ᵉ) (Yᵉ : Type-With-Endomorphismᵉ l2ᵉ)
  where

  htpy-hom-Type-With-Endomorphismᵉ :
    (fᵉ gᵉ : hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-hom-Type-With-Endomorphismᵉ fᵉ gᵉ =
    Σᵉ ( map-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ fᵉ ~ᵉ
        map-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ gᵉ)
      ( λ Hᵉ →
        ( ( Hᵉ ·rᵉ endomorphism-Type-With-Endomorphismᵉ Xᵉ) ∙hᵉ
          ( coherence-square-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ gᵉ)) ~ᵉ
        ( ( coherence-square-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ fᵉ) ∙hᵉ
          ( endomorphism-Type-With-Endomorphismᵉ Yᵉ ·lᵉ Hᵉ)))

  refl-htpy-hom-Type-With-Endomorphismᵉ :
    (fᵉ : hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ) → htpy-hom-Type-With-Endomorphismᵉ fᵉ fᵉ
  pr1ᵉ (refl-htpy-hom-Type-With-Endomorphismᵉ fᵉ) = refl-htpyᵉ
  pr2ᵉ (refl-htpy-hom-Type-With-Endomorphismᵉ fᵉ) = inv-htpy-right-unit-htpyᵉ

  htpy-eq-hom-Type-With-Endomorphismᵉ :
    (fᵉ gᵉ : hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ) →
    fᵉ ＝ᵉ gᵉ → htpy-hom-Type-With-Endomorphismᵉ fᵉ gᵉ
  htpy-eq-hom-Type-With-Endomorphismᵉ fᵉ .fᵉ reflᵉ =
    refl-htpy-hom-Type-With-Endomorphismᵉ fᵉ

  is-torsorial-htpy-hom-Type-With-Endomorphismᵉ :
    (fᵉ : hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ) →
    is-torsorialᵉ (htpy-hom-Type-With-Endomorphismᵉ fᵉ)
  is-torsorial-htpy-hom-Type-With-Endomorphismᵉ fᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (map-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ fᵉ))
      ( map-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ fᵉ ,ᵉ refl-htpyᵉ)
      ( is-contr-equivᵉ
        ( Σᵉ ( coherence-square-mapsᵉ
              ( map-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ fᵉ)
              ( endomorphism-Type-With-Endomorphismᵉ Xᵉ)
              ( endomorphism-Type-With-Endomorphismᵉ Yᵉ)
              ( map-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ fᵉ))
            ( λ Hᵉ → Hᵉ ~ᵉ coherence-square-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ fᵉ))
        ( equiv-totᵉ (λ Hᵉ → equiv-concat-htpy'ᵉ Hᵉ right-unit-htpyᵉ))
        ( is-torsorial-htpy'ᵉ
          ( coherence-square-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ fᵉ)))

  is-equiv-htpy-eq-hom-Type-With-Endomorphismᵉ :
    (fᵉ gᵉ : hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ) →
    is-equivᵉ (htpy-eq-hom-Type-With-Endomorphismᵉ fᵉ gᵉ)
  is-equiv-htpy-eq-hom-Type-With-Endomorphismᵉ fᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-hom-Type-With-Endomorphismᵉ fᵉ)
      ( htpy-eq-hom-Type-With-Endomorphismᵉ fᵉ)

  extensionality-hom-Type-With-Endomorphismᵉ :
    (fᵉ gᵉ : hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-Type-With-Endomorphismᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-hom-Type-With-Endomorphismᵉ fᵉ gᵉ) =
    htpy-eq-hom-Type-With-Endomorphismᵉ fᵉ gᵉ
  pr2ᵉ (extensionality-hom-Type-With-Endomorphismᵉ fᵉ gᵉ) =
    is-equiv-htpy-eq-hom-Type-With-Endomorphismᵉ fᵉ gᵉ

  eq-htpy-hom-Type-With-Endomorphismᵉ :
    ( fᵉ gᵉ : hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ) →
    htpy-hom-Type-With-Endomorphismᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-Type-With-Endomorphismᵉ fᵉ gᵉ =
    map-inv-equivᵉ (extensionality-hom-Type-With-Endomorphismᵉ fᵉ gᵉ)
```