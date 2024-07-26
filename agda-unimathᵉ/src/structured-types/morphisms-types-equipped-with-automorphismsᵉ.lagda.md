# Morphisms of types equipped with automorphisms

```agda
module structured-types.morphisms-types-equipped-with-automorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.morphisms-types-equipped-with-endomorphismsᵉ
open import structured-types.types-equipped-with-automorphismsᵉ
```

</details>

## Idea

Considerᵉ twoᵉ
[typesᵉ equippedᵉ with anᵉ automorphism](structured-types.types-equipped-with-automorphisms.mdᵉ)
`(X,e)`ᵉ andᵉ `(Y,f)`.ᵉ Aᵉ **morphism**ᵉ fromᵉ `(X,e)`ᵉ to `(Y,f)`ᵉ consistsᵉ ofᵉ aᵉ mapᵉ
`hᵉ : Xᵉ → Y`ᵉ equippedᵉ with aᵉ [homotopy](foundation-core.homotopies.mdᵉ) witnessingᵉ
thatᵉ theᵉ squareᵉ

```text
      hᵉ
  Xᵉ ----->ᵉ Yᵉ
  |        |
 e|ᵉ        |fᵉ
  ∨ᵉ        ∨ᵉ
  Xᵉ ----->ᵉ Yᵉ
      hᵉ
```

[commutes](foundation.commuting-squares-of-maps.md).ᵉ

## Definition

### Morphisms of types equipped with automorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Xᵉ : Type-With-Automorphismᵉ l1ᵉ) (Yᵉ : Type-With-Automorphismᵉ l2ᵉ)
  where

  hom-Type-With-Automorphismᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Type-With-Automorphismᵉ =
    hom-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  map-hom-Type-With-Automorphismᵉ :
    hom-Type-With-Automorphismᵉ →
    type-Type-With-Automorphismᵉ Xᵉ → type-Type-With-Automorphismᵉ Yᵉ
  map-hom-Type-With-Automorphismᵉ =
    map-hom-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  coherence-square-hom-Type-With-Automorphismᵉ :
    (fᵉ : hom-Type-With-Automorphismᵉ) →
    coherence-square-mapsᵉ
      ( map-hom-Type-With-Automorphismᵉ fᵉ)
      ( map-Type-With-Automorphismᵉ Xᵉ)
      ( map-Type-With-Automorphismᵉ Yᵉ)
      ( map-hom-Type-With-Automorphismᵉ fᵉ)
  coherence-square-hom-Type-With-Automorphismᵉ =
    coherence-square-hom-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)
```

### Homotopies of morphisms of types equipped with automorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Xᵉ : Type-With-Automorphismᵉ l1ᵉ) (Yᵉ : Type-With-Automorphismᵉ l2ᵉ)
  where

  htpy-hom-Type-With-Automorphismᵉ :
    (fᵉ gᵉ : hom-Type-With-Automorphismᵉ Xᵉ Yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-hom-Type-With-Automorphismᵉ =
    htpy-hom-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  refl-htpy-hom-Type-With-Automorphismᵉ :
    (fᵉ : hom-Type-With-Automorphismᵉ Xᵉ Yᵉ) → htpy-hom-Type-With-Automorphismᵉ fᵉ fᵉ
  refl-htpy-hom-Type-With-Automorphismᵉ =
    refl-htpy-hom-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  htpy-eq-hom-Type-With-Automorphismᵉ :
    (fᵉ gᵉ : hom-Type-With-Automorphismᵉ Xᵉ Yᵉ) →
    fᵉ ＝ᵉ gᵉ → htpy-hom-Type-With-Automorphismᵉ fᵉ gᵉ
  htpy-eq-hom-Type-With-Automorphismᵉ =
    htpy-eq-hom-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  is-torsorial-htpy-hom-Type-With-Automorphismᵉ :
    (fᵉ : hom-Type-With-Automorphismᵉ Xᵉ Yᵉ) →
    is-torsorialᵉ (htpy-hom-Type-With-Automorphismᵉ fᵉ)
  is-torsorial-htpy-hom-Type-With-Automorphismᵉ =
    is-torsorial-htpy-hom-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  is-equiv-htpy-eq-hom-Type-With-Automorphismᵉ :
    (fᵉ gᵉ : hom-Type-With-Automorphismᵉ Xᵉ Yᵉ) →
    is-equivᵉ (htpy-eq-hom-Type-With-Automorphismᵉ fᵉ gᵉ)
  is-equiv-htpy-eq-hom-Type-With-Automorphismᵉ =
    is-equiv-htpy-eq-hom-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  extensionality-hom-Type-With-Automorphismᵉ :
    (fᵉ gᵉ : hom-Type-With-Automorphismᵉ Xᵉ Yᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-Type-With-Automorphismᵉ fᵉ gᵉ
  extensionality-hom-Type-With-Automorphismᵉ =
    extensionality-hom-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  eq-htpy-hom-Type-With-Automorphismᵉ :
    ( fᵉ gᵉ : hom-Type-With-Automorphismᵉ Xᵉ Yᵉ) →
    htpy-hom-Type-With-Automorphismᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-Type-With-Automorphismᵉ =
    eq-htpy-hom-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)
```