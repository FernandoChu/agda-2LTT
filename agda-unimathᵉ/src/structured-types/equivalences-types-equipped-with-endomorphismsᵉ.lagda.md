# Equivalences of types equipped with endomorphisms

```agda
module structured-types.equivalences-types-equipped-with-endomorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import structured-types.morphisms-types-equipped-with-endomorphismsᵉ
open import structured-types.types-equipped-with-endomorphismsᵉ
```

</details>

## Definition

### The predicate of being an equivalence of types equipped with endomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Xᵉ : Type-With-Endomorphismᵉ l1ᵉ)
  (Yᵉ : Type-With-Endomorphismᵉ l2ᵉ)
  where

  is-equiv-hom-Type-With-Endomorphismᵉ :
    hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-equiv-hom-Type-With-Endomorphismᵉ hᵉ =
    is-equivᵉ (map-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ hᵉ)
```

### Equivalences of types equipped with endomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Xᵉ : Type-With-Endomorphismᵉ l1ᵉ)
  (Yᵉ : Type-With-Endomorphismᵉ l2ᵉ)
  where

  equiv-Type-With-Endomorphismᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equiv-Type-With-Endomorphismᵉ =
    Σᵉ ( type-Type-With-Endomorphismᵉ Xᵉ ≃ᵉ type-Type-With-Endomorphismᵉ Yᵉ)
      ( λ eᵉ →
        coherence-square-mapsᵉ
          ( map-equivᵉ eᵉ)
          ( endomorphism-Type-With-Endomorphismᵉ Xᵉ)
          ( endomorphism-Type-With-Endomorphismᵉ Yᵉ)
          ( map-equivᵉ eᵉ))

  equiv-Type-With-Endomorphism'ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equiv-Type-With-Endomorphism'ᵉ =
    Σᵉ (hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ) (is-equiv-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ)

  compute-equiv-Type-With-Endomorphismᵉ :
    equiv-Type-With-Endomorphism'ᵉ ≃ᵉ equiv-Type-With-Endomorphismᵉ
  compute-equiv-Type-With-Endomorphismᵉ =
    equiv-right-swap-Σᵉ

  equiv-equiv-Type-With-Endomorphismᵉ :
    equiv-Type-With-Endomorphismᵉ →
    type-Type-With-Endomorphismᵉ Xᵉ ≃ᵉ type-Type-With-Endomorphismᵉ Yᵉ
  equiv-equiv-Type-With-Endomorphismᵉ eᵉ = pr1ᵉ eᵉ

  map-equiv-Type-With-Endomorphismᵉ :
    equiv-Type-With-Endomorphismᵉ →
    type-Type-With-Endomorphismᵉ Xᵉ → type-Type-With-Endomorphismᵉ Yᵉ
  map-equiv-Type-With-Endomorphismᵉ eᵉ =
    map-equivᵉ (equiv-equiv-Type-With-Endomorphismᵉ eᵉ)

  coherence-square-equiv-Type-With-Endomorphismᵉ :
    (eᵉ : equiv-Type-With-Endomorphismᵉ) →
    coherence-square-mapsᵉ
      ( map-equiv-Type-With-Endomorphismᵉ eᵉ)
      ( endomorphism-Type-With-Endomorphismᵉ Xᵉ)
      ( endomorphism-Type-With-Endomorphismᵉ Yᵉ)
      ( map-equiv-Type-With-Endomorphismᵉ eᵉ)
  coherence-square-equiv-Type-With-Endomorphismᵉ eᵉ = pr2ᵉ eᵉ

  hom-equiv-Type-With-Endomorphismᵉ :
    equiv-Type-With-Endomorphismᵉ → hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ
  pr1ᵉ (hom-equiv-Type-With-Endomorphismᵉ eᵉ) =
    map-equiv-Type-With-Endomorphismᵉ eᵉ
  pr2ᵉ (hom-equiv-Type-With-Endomorphismᵉ eᵉ) =
    coherence-square-equiv-Type-With-Endomorphismᵉ eᵉ

  is-equiv-equiv-Type-With-Endomorphismᵉ :
    (eᵉ : equiv-Type-With-Endomorphismᵉ) →
    is-equiv-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ (hom-equiv-Type-With-Endomorphismᵉ eᵉ)
  is-equiv-equiv-Type-With-Endomorphismᵉ eᵉ =
    is-equiv-map-equivᵉ (equiv-equiv-Type-With-Endomorphismᵉ eᵉ)
```

### The identity equivalence

```agda
module _
  {l1ᵉ : Level} (Xᵉ : Type-With-Endomorphismᵉ l1ᵉ)
  where

  id-equiv-Type-With-Endomorphismᵉ : equiv-Type-With-Endomorphismᵉ Xᵉ Xᵉ
  pr1ᵉ id-equiv-Type-With-Endomorphismᵉ = id-equivᵉ
  pr2ᵉ id-equiv-Type-With-Endomorphismᵉ = refl-htpyᵉ
```

### Composition for equivalences of types equipped with endomorphisms

```agda
comp-equiv-Type-With-Endomorphismᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Xᵉ : Type-With-Endomorphismᵉ l1ᵉ)
  (Yᵉ : Type-With-Endomorphismᵉ l2ᵉ)
  (Zᵉ : Type-With-Endomorphismᵉ l3ᵉ) →
  equiv-Type-With-Endomorphismᵉ Yᵉ Zᵉ →
  equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ →
  equiv-Type-With-Endomorphismᵉ Xᵉ Zᵉ
pr1ᵉ (comp-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ Zᵉ fᵉ eᵉ) = pr1ᵉ fᵉ ∘eᵉ pr1ᵉ eᵉ
pr2ᵉ (comp-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ Zᵉ fᵉ eᵉ) =
  pasting-horizontal-coherence-square-mapsᵉ
    ( map-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ eᵉ)
    ( map-equiv-Type-With-Endomorphismᵉ Yᵉ Zᵉ fᵉ)
    ( endomorphism-Type-With-Endomorphismᵉ Xᵉ)
    ( endomorphism-Type-With-Endomorphismᵉ Yᵉ)
    ( endomorphism-Type-With-Endomorphismᵉ Zᵉ)
    ( map-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ eᵉ)
    ( map-equiv-Type-With-Endomorphismᵉ Yᵉ Zᵉ fᵉ)
    ( coherence-square-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ eᵉ)
    ( coherence-square-equiv-Type-With-Endomorphismᵉ Yᵉ Zᵉ fᵉ)
```

### Inverses of equivalences of types equipped with endomorphisms

```agda
inv-equiv-Type-With-Endomorphismᵉ :
  {l1ᵉ l2ᵉ : Level}
  (Xᵉ : Type-With-Endomorphismᵉ l1ᵉ)
  (Yᵉ : Type-With-Endomorphismᵉ l2ᵉ) →
  equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ → equiv-Type-With-Endomorphismᵉ Yᵉ Xᵉ
pr1ᵉ (inv-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ eᵉ) =
  inv-equivᵉ (equiv-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ eᵉ)
pr2ᵉ (inv-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ eᵉ) =
  horizontal-inv-equiv-coherence-square-mapsᵉ
    ( equiv-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ eᵉ)
    ( endomorphism-Type-With-Endomorphismᵉ Xᵉ)
    ( endomorphism-Type-With-Endomorphismᵉ Yᵉ)
    ( equiv-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ eᵉ)
    ( coherence-square-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ eᵉ)
```

### Homotopies of equivalences of types equipped with endomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Xᵉ : Type-With-Endomorphismᵉ l1ᵉ)
  (Yᵉ : Type-With-Endomorphismᵉ l2ᵉ)
  where

  htpy-equiv-Type-With-Endomorphismᵉ :
    (eᵉ fᵉ : equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-equiv-Type-With-Endomorphismᵉ eᵉ fᵉ =
    htpy-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ
      ( hom-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ eᵉ)
      ( hom-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ fᵉ)

  refl-htpy-equiv-Type-With-Endomorphismᵉ :
    ( eᵉ : equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ) →
    htpy-equiv-Type-With-Endomorphismᵉ eᵉ eᵉ
  refl-htpy-equiv-Type-With-Endomorphismᵉ eᵉ =
    refl-htpy-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ
      ( hom-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ eᵉ)

  htpy-eq-equiv-Type-With-Endomorphismᵉ :
    (eᵉ fᵉ : equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ) →
    eᵉ ＝ᵉ fᵉ → htpy-equiv-Type-With-Endomorphismᵉ eᵉ fᵉ
  htpy-eq-equiv-Type-With-Endomorphismᵉ eᵉ .eᵉ reflᵉ =
    refl-htpy-equiv-Type-With-Endomorphismᵉ eᵉ

  is-torsorial-htpy-equiv-Type-With-Endomorphismᵉ :
    (eᵉ : equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ) →
    is-torsorialᵉ (htpy-equiv-Type-With-Endomorphismᵉ eᵉ)
  is-torsorial-htpy-equiv-Type-With-Endomorphismᵉ eᵉ =
    is-contr-equivᵉ
      ( Σᵉ ( Σᵉ ( hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ)
              ( λ fᵉ → is-equivᵉ (map-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ fᵉ)))
          ( λ fᵉ →
            htpy-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ
              ( hom-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ eᵉ)
              ( pr1ᵉ fᵉ)))
      ( equiv-Σᵉ
        ( λ fᵉ →
          htpy-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ
            ( hom-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ eᵉ)
            ( pr1ᵉ fᵉ))
        ( equiv-right-swap-Σᵉ)
        ( λ fᵉ → id-equivᵉ))
      ( is-torsorial-Eq-subtypeᵉ
        ( is-torsorial-htpy-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ
          ( hom-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ eᵉ))
        ( λ fᵉ → is-property-is-equivᵉ (pr1ᵉ fᵉ))
        ( hom-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ eᵉ)
        ( refl-htpy-hom-Type-With-Endomorphismᵉ Xᵉ Yᵉ
          ( hom-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ eᵉ))
        ( pr2ᵉ (pr1ᵉ eᵉ)))

  is-equiv-htpy-eq-equiv-Type-With-Endomorphismᵉ :
    (eᵉ fᵉ : equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ) →
    is-equivᵉ (htpy-eq-equiv-Type-With-Endomorphismᵉ eᵉ fᵉ)
  is-equiv-htpy-eq-equiv-Type-With-Endomorphismᵉ eᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-equiv-Type-With-Endomorphismᵉ eᵉ)
      ( htpy-eq-equiv-Type-With-Endomorphismᵉ eᵉ)

  extensionality-equiv-Type-With-Endomorphismᵉ :
    (eᵉ fᵉ : equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ) →
    (eᵉ ＝ᵉ fᵉ) ≃ᵉ htpy-equiv-Type-With-Endomorphismᵉ eᵉ fᵉ
  pr1ᵉ (extensionality-equiv-Type-With-Endomorphismᵉ eᵉ fᵉ) =
    htpy-eq-equiv-Type-With-Endomorphismᵉ eᵉ fᵉ
  pr2ᵉ (extensionality-equiv-Type-With-Endomorphismᵉ eᵉ fᵉ) =
    is-equiv-htpy-eq-equiv-Type-With-Endomorphismᵉ eᵉ fᵉ

  eq-htpy-equiv-Type-With-Endomorphismᵉ :
    (eᵉ fᵉ : equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ) →
    htpy-equiv-Type-With-Endomorphismᵉ eᵉ fᵉ → eᵉ ＝ᵉ fᵉ
  eq-htpy-equiv-Type-With-Endomorphismᵉ eᵉ fᵉ =
    map-inv-equivᵉ (extensionality-equiv-Type-With-Endomorphismᵉ eᵉ fᵉ)
```

## Properties

### Unit laws for composition of equivalences of types equipped with endomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Xᵉ : Type-With-Endomorphismᵉ l1ᵉ)
  (Yᵉ : Type-With-Endomorphismᵉ l2ᵉ)
  where

  left-unit-law-comp-equiv-Type-With-Endomorphismᵉ :
    (eᵉ : equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ) →
    comp-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ Yᵉ
      ( id-equiv-Type-With-Endomorphismᵉ Yᵉ) eᵉ ＝ᵉ
    eᵉ
  left-unit-law-comp-equiv-Type-With-Endomorphismᵉ eᵉ =
    eq-htpy-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ
      ( comp-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ Yᵉ
        ( id-equiv-Type-With-Endomorphismᵉ Yᵉ)
        ( eᵉ))
      ( eᵉ)
      ( pairᵉ
        ( refl-htpyᵉ)
        ( λ xᵉ →
          invᵉ
            ( ( right-unitᵉ) ∙ᵉ
              ( right-unitᵉ) ∙ᵉ
              ( ap-idᵉ
                ( coherence-square-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ eᵉ xᵉ)))))

  right-unit-law-comp-equiv-Type-With-Endomorphismᵉ :
    (eᵉ : equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ) →
    comp-equiv-Type-With-Endomorphismᵉ Xᵉ Xᵉ Yᵉ eᵉ
      ( id-equiv-Type-With-Endomorphismᵉ Xᵉ) ＝ᵉ
    eᵉ
  right-unit-law-comp-equiv-Type-With-Endomorphismᵉ eᵉ =
    eq-htpy-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ
      ( comp-equiv-Type-With-Endomorphismᵉ Xᵉ Xᵉ Yᵉ eᵉ
        ( id-equiv-Type-With-Endomorphismᵉ Xᵉ))
      ( eᵉ)
      ( pairᵉ
        ( refl-htpyᵉ)
        ( λ xᵉ → invᵉ right-unitᵉ))
```

### Extensionality of types equipped with endomorphisms

```agda
module _
  {l1ᵉ : Level} (Xᵉ : Type-With-Endomorphismᵉ l1ᵉ)
  where

  equiv-eq-Type-With-Endomorphismᵉ :
    ( Yᵉ : Type-With-Endomorphismᵉ l1ᵉ) →
    Xᵉ ＝ᵉ Yᵉ → equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ
  equiv-eq-Type-With-Endomorphismᵉ .Xᵉ reflᵉ =
    id-equiv-Type-With-Endomorphismᵉ Xᵉ

  is-torsorial-equiv-Type-With-Endomorphismᵉ :
    is-torsorialᵉ (equiv-Type-With-Endomorphismᵉ Xᵉ)
  is-torsorial-equiv-Type-With-Endomorphismᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equivᵉ (type-Type-With-Endomorphismᵉ Xᵉ))
      ( type-Type-With-Endomorphismᵉ Xᵉ ,ᵉ id-equivᵉ)
      ( is-torsorial-htpyᵉ (endomorphism-Type-With-Endomorphismᵉ Xᵉ))

  is-equiv-equiv-eq-Type-With-Endomorphismᵉ :
    ( Yᵉ : Type-With-Endomorphismᵉ l1ᵉ) →
    is-equivᵉ (equiv-eq-Type-With-Endomorphismᵉ Yᵉ)
  is-equiv-equiv-eq-Type-With-Endomorphismᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-Type-With-Endomorphismᵉ
      equiv-eq-Type-With-Endomorphismᵉ

  extensionality-Type-With-Endomorphismᵉ :
    (Yᵉ : Type-With-Endomorphismᵉ l1ᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ
  pr1ᵉ (extensionality-Type-With-Endomorphismᵉ Yᵉ) =
    equiv-eq-Type-With-Endomorphismᵉ Yᵉ
  pr2ᵉ (extensionality-Type-With-Endomorphismᵉ Yᵉ) =
    is-equiv-equiv-eq-Type-With-Endomorphismᵉ Yᵉ

  eq-equiv-Type-With-Endomorphismᵉ :
    (Yᵉ : Type-With-Endomorphismᵉ l1ᵉ) → equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ → Xᵉ ＝ᵉ Yᵉ
  eq-equiv-Type-With-Endomorphismᵉ Yᵉ =
    map-inv-is-equivᵉ (is-equiv-equiv-eq-Type-With-Endomorphismᵉ Yᵉ)

module _
  {lᵉ : Level}
  (Xᵉ : Type-With-Endomorphismᵉ lᵉ)
  (Yᵉ : Type-With-Endomorphismᵉ lᵉ)
  (Zᵉ : Type-With-Endomorphismᵉ lᵉ)
  where

  preserves-concat-equiv-eq-Type-With-Endomorphismᵉ :
    (pᵉ : Xᵉ ＝ᵉ Yᵉ) (qᵉ : Yᵉ ＝ᵉ Zᵉ) →
    ( equiv-eq-Type-With-Endomorphismᵉ Xᵉ Zᵉ (pᵉ ∙ᵉ qᵉ)) ＝ᵉ
    ( comp-equiv-Type-With-Endomorphismᵉ Xᵉ Yᵉ Zᵉ
      ( equiv-eq-Type-With-Endomorphismᵉ Yᵉ Zᵉ qᵉ)
      ( equiv-eq-Type-With-Endomorphismᵉ Xᵉ Yᵉ pᵉ))
  preserves-concat-equiv-eq-Type-With-Endomorphismᵉ reflᵉ qᵉ =
    invᵉ
      ( right-unit-law-comp-equiv-Type-With-Endomorphismᵉ Xᵉ Zᵉ
        ( equiv-eq-Type-With-Endomorphismᵉ Xᵉ Zᵉ qᵉ))
```