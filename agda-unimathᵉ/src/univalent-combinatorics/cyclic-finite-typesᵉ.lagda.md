# Cyclic finite types

```agda
module univalent-combinatorics.cyclic-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.modular-arithmeticᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.standard-cyclic-groupsᵉ

open import foundation.0-connected-typesᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.mere-equalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.isomorphisms-groupsᵉ

open import higher-group-theory.higher-groupsᵉ

open import structured-types.equivalences-types-equipped-with-endomorphismsᵉ
open import structured-types.mere-equivalences-types-equipped-with-endomorphismsᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.types-equipped-with-endomorphismsᵉ

open import synthetic-homotopy-theory.groups-of-loops-in-1-typesᵉ
open import synthetic-homotopy-theory.loop-spacesᵉ
```

</details>

## Idea

Aᵉ cyclicᵉ typeᵉ isᵉ aᵉ typeᵉ `X`ᵉ equippedᵉ with anᵉ endomorphismᵉ `fᵉ : Xᵉ → X`ᵉ suchᵉ thatᵉ
theᵉ pairᵉ `(X,ᵉ f)`ᵉ isᵉ merelyᵉ equivalentᵉ to theᵉ pairᵉ `(ℤ-Modᵉ k,ᵉ +1)`ᵉ forᵉ someᵉ
`kᵉ : ℕ`.ᵉ

## Definitions

### The type of cyclic types of a given order

```agda
is-cyclic-Type-With-Endomorphismᵉ :
  {lᵉ : Level} → ℕᵉ → Type-With-Endomorphismᵉ lᵉ → UUᵉ lᵉ
is-cyclic-Type-With-Endomorphismᵉ kᵉ Xᵉ =
  mere-equiv-Type-With-Endomorphismᵉ (ℤ-Mod-Type-With-Endomorphismᵉ kᵉ) Xᵉ

Cyclic-Typeᵉ : (lᵉ : Level) → ℕᵉ → UUᵉ (lsuc lᵉ)
Cyclic-Typeᵉ lᵉ kᵉ =
  Σᵉ (Type-With-Endomorphismᵉ lᵉ) (is-cyclic-Type-With-Endomorphismᵉ kᵉ)

module _
  {lᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ : Cyclic-Typeᵉ lᵉ kᵉ)
  where

  endo-Cyclic-Typeᵉ : Type-With-Endomorphismᵉ lᵉ
  endo-Cyclic-Typeᵉ = pr1ᵉ Xᵉ

  type-Cyclic-Typeᵉ : UUᵉ lᵉ
  type-Cyclic-Typeᵉ = type-Type-With-Endomorphismᵉ endo-Cyclic-Typeᵉ

  endomorphism-Cyclic-Typeᵉ : type-Cyclic-Typeᵉ → type-Cyclic-Typeᵉ
  endomorphism-Cyclic-Typeᵉ =
    endomorphism-Type-With-Endomorphismᵉ endo-Cyclic-Typeᵉ

  mere-equiv-endo-Cyclic-Typeᵉ :
    mere-equiv-Type-With-Endomorphismᵉ
      ( ℤ-Mod-Type-With-Endomorphismᵉ kᵉ)
      ( endo-Cyclic-Typeᵉ)
  mere-equiv-endo-Cyclic-Typeᵉ = pr2ᵉ Xᵉ

  is-set-type-Cyclic-Typeᵉ : is-setᵉ type-Cyclic-Typeᵉ
  is-set-type-Cyclic-Typeᵉ =
    apply-universal-property-trunc-Propᵉ
      ( mere-equiv-endo-Cyclic-Typeᵉ)
      ( is-set-Propᵉ type-Cyclic-Typeᵉ)
      ( λ eᵉ →
        is-set-equiv'ᵉ
          ( ℤ-Modᵉ kᵉ)
          ( equiv-equiv-Type-With-Endomorphismᵉ
            ( ℤ-Mod-Type-With-Endomorphismᵉ kᵉ)
            ( endo-Cyclic-Typeᵉ)
            ( eᵉ))
          ( is-set-ℤ-Modᵉ kᵉ))

  set-Cyclic-Typeᵉ : Setᵉ lᵉ
  pr1ᵉ set-Cyclic-Typeᵉ = type-Cyclic-Typeᵉ
  pr2ᵉ set-Cyclic-Typeᵉ = is-set-type-Cyclic-Typeᵉ
```

### Cyclic-Type structure on a type

```agda
cyclic-structureᵉ : {lᵉ : Level} → ℕᵉ → UUᵉ lᵉ → UUᵉ lᵉ
cyclic-structureᵉ kᵉ Xᵉ =
  Σᵉ (Xᵉ → Xᵉ) (λ fᵉ → is-cyclic-Type-With-Endomorphismᵉ kᵉ (Xᵉ ,ᵉ fᵉ))

cyclic-type-cyclic-structureᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Xᵉ : UUᵉ lᵉ} → cyclic-structureᵉ kᵉ Xᵉ → Cyclic-Typeᵉ lᵉ kᵉ
pr1ᵉ (pr1ᵉ (cyclic-type-cyclic-structureᵉ kᵉ {Xᵉ} cᵉ)) = Xᵉ
pr2ᵉ (pr1ᵉ (cyclic-type-cyclic-structureᵉ kᵉ cᵉ)) = pr1ᵉ cᵉ
pr2ᵉ (cyclic-type-cyclic-structureᵉ kᵉ cᵉ) = pr2ᵉ cᵉ
```

### The standard cyclic types

```agda
ℤ-Mod-Cyclic-Typeᵉ : (kᵉ : ℕᵉ) → Cyclic-Typeᵉ lzero kᵉ
pr1ᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ) =
  ℤ-Mod-Type-With-Endomorphismᵉ kᵉ
pr2ᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ) =
  refl-mere-equiv-Type-With-Endomorphismᵉ (ℤ-Mod-Type-With-Endomorphismᵉ kᵉ)

Fin-Cyclic-Typeᵉ : (kᵉ : ℕᵉ) → Cyclic-Typeᵉ lzero (succ-ℕᵉ kᵉ)
Fin-Cyclic-Typeᵉ kᵉ = ℤ-Mod-Cyclic-Typeᵉ (succ-ℕᵉ kᵉ)

Cyclic-Type-Pointed-Typeᵉ : (kᵉ : ℕᵉ) → Pointed-Typeᵉ (lsuc lzero)
pr1ᵉ (Cyclic-Type-Pointed-Typeᵉ kᵉ) = Cyclic-Typeᵉ lzero kᵉ
pr2ᵉ (Cyclic-Type-Pointed-Typeᵉ kᵉ) = ℤ-Mod-Cyclic-Typeᵉ kᵉ
```

### Equivalences of cyclic types

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ : Cyclic-Typeᵉ l1ᵉ kᵉ) (Yᵉ : Cyclic-Typeᵉ l2ᵉ kᵉ)
  where

  equiv-Cyclic-Typeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equiv-Cyclic-Typeᵉ =
    equiv-Type-With-Endomorphismᵉ (endo-Cyclic-Typeᵉ kᵉ Xᵉ) (endo-Cyclic-Typeᵉ kᵉ Yᵉ)

  equiv-equiv-Cyclic-Typeᵉ :
    equiv-Cyclic-Typeᵉ → type-Cyclic-Typeᵉ kᵉ Xᵉ ≃ᵉ type-Cyclic-Typeᵉ kᵉ Yᵉ
  equiv-equiv-Cyclic-Typeᵉ =
    equiv-equiv-Type-With-Endomorphismᵉ
      ( endo-Cyclic-Typeᵉ kᵉ Xᵉ)
      ( endo-Cyclic-Typeᵉ kᵉ Yᵉ)

  map-equiv-Cyclic-Typeᵉ :
    equiv-Cyclic-Typeᵉ → type-Cyclic-Typeᵉ kᵉ Xᵉ → type-Cyclic-Typeᵉ kᵉ Yᵉ
  map-equiv-Cyclic-Typeᵉ eᵉ =
    map-equiv-Type-With-Endomorphismᵉ
      ( endo-Cyclic-Typeᵉ kᵉ Xᵉ)
      ( endo-Cyclic-Typeᵉ kᵉ Yᵉ)
      ( eᵉ)

  coherence-square-equiv-Cyclic-Typeᵉ :
    ( eᵉ : equiv-Cyclic-Typeᵉ) →
    coherence-square-mapsᵉ
      ( map-equiv-Cyclic-Typeᵉ eᵉ)
      ( endomorphism-Cyclic-Typeᵉ kᵉ Xᵉ)
      ( endomorphism-Cyclic-Typeᵉ kᵉ Yᵉ)
      ( map-equiv-Cyclic-Typeᵉ eᵉ)
  coherence-square-equiv-Cyclic-Typeᵉ eᵉ = pr2ᵉ eᵉ

module _
  {lᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ : Cyclic-Typeᵉ lᵉ kᵉ)
  where

  id-equiv-Cyclic-Typeᵉ : equiv-Cyclic-Typeᵉ kᵉ Xᵉ Xᵉ
  id-equiv-Cyclic-Typeᵉ = id-equiv-Type-With-Endomorphismᵉ (endo-Cyclic-Typeᵉ kᵉ Xᵉ)

  equiv-eq-Cyclic-Typeᵉ :
    (Yᵉ : Cyclic-Typeᵉ lᵉ kᵉ) → Idᵉ Xᵉ Yᵉ → equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ
  equiv-eq-Cyclic-Typeᵉ .Xᵉ reflᵉ = id-equiv-Cyclic-Typeᵉ

is-torsorial-equiv-Cyclic-Typeᵉ :
  {l1ᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ : Cyclic-Typeᵉ l1ᵉ kᵉ) →
  is-torsorialᵉ (equiv-Cyclic-Typeᵉ kᵉ Xᵉ)
is-torsorial-equiv-Cyclic-Typeᵉ kᵉ Xᵉ =
  is-torsorial-Eq-subtypeᵉ
    ( is-torsorial-equiv-Type-With-Endomorphismᵉ (endo-Cyclic-Typeᵉ kᵉ Xᵉ))
    ( λ Yᵉ → is-prop-type-trunc-Propᵉ)
    ( endo-Cyclic-Typeᵉ kᵉ Xᵉ)
    ( id-equiv-Type-With-Endomorphismᵉ (endo-Cyclic-Typeᵉ kᵉ Xᵉ))
    ( mere-equiv-endo-Cyclic-Typeᵉ kᵉ Xᵉ)

module _
  {lᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ : Cyclic-Typeᵉ lᵉ kᵉ)
  where

  is-equiv-equiv-eq-Cyclic-Typeᵉ :
    (Yᵉ : Cyclic-Typeᵉ lᵉ kᵉ) → is-equivᵉ (equiv-eq-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ)
  is-equiv-equiv-eq-Cyclic-Typeᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-equiv-Cyclic-Typeᵉ kᵉ Xᵉ)
      ( equiv-eq-Cyclic-Typeᵉ kᵉ Xᵉ)

  extensionality-Cyclic-Typeᵉ :
    (Yᵉ : Cyclic-Typeᵉ lᵉ kᵉ) → Idᵉ Xᵉ Yᵉ ≃ᵉ equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ
  pr1ᵉ (extensionality-Cyclic-Typeᵉ Yᵉ) = equiv-eq-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ
  pr2ᵉ (extensionality-Cyclic-Typeᵉ Yᵉ) = is-equiv-equiv-eq-Cyclic-Typeᵉ Yᵉ

  eq-equiv-Cyclic-Typeᵉ :
    (Yᵉ : Cyclic-Typeᵉ lᵉ kᵉ) → equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ → Idᵉ Xᵉ Yᵉ
  eq-equiv-Cyclic-Typeᵉ Yᵉ = map-inv-is-equivᵉ (is-equiv-equiv-eq-Cyclic-Typeᵉ Yᵉ)
```

## Properties

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ : Cyclic-Typeᵉ l1ᵉ kᵉ) (Yᵉ : Cyclic-Typeᵉ l2ᵉ kᵉ)
  where

  htpy-equiv-Cyclic-Typeᵉ : (eᵉ fᵉ : equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-equiv-Cyclic-Typeᵉ eᵉ fᵉ =
    map-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ eᵉ ~ᵉ map-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ fᵉ

  refl-htpy-equiv-Cyclic-Typeᵉ :
    (eᵉ : equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ) → htpy-equiv-Cyclic-Typeᵉ eᵉ eᵉ
  refl-htpy-equiv-Cyclic-Typeᵉ eᵉ = refl-htpyᵉ

  htpy-eq-equiv-Cyclic-Typeᵉ :
    (eᵉ fᵉ : equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ) → Idᵉ eᵉ fᵉ → htpy-equiv-Cyclic-Typeᵉ eᵉ fᵉ
  htpy-eq-equiv-Cyclic-Typeᵉ eᵉ .eᵉ reflᵉ = refl-htpy-equiv-Cyclic-Typeᵉ eᵉ

  is-torsorial-htpy-equiv-Cyclic-Typeᵉ :
    (eᵉ : equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ) → is-torsorialᵉ (htpy-equiv-Cyclic-Typeᵉ eᵉ)
  is-torsorial-htpy-equiv-Cyclic-Typeᵉ eᵉ =
    is-contr-equiv'ᵉ
      ( Σᵉ ( equiv-Type-With-Endomorphismᵉ
            ( endo-Cyclic-Typeᵉ kᵉ Xᵉ)
            ( endo-Cyclic-Typeᵉ kᵉ Yᵉ))
          ( htpy-equiv-Type-With-Endomorphismᵉ
            ( endo-Cyclic-Typeᵉ kᵉ Xᵉ)
            ( endo-Cyclic-Typeᵉ kᵉ Yᵉ)
            ( eᵉ)))
      ( equiv-totᵉ
        ( λ fᵉ →
          right-unit-law-Σ-is-contrᵉ
            ( λ Hᵉ →
              is-contr-Πᵉ
                ( λ xᵉ →
                  is-set-type-Cyclic-Typeᵉ kᵉ Yᵉ
                  ( map-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ eᵉ
                    ( endomorphism-Cyclic-Typeᵉ kᵉ Xᵉ xᵉ))
                  ( endomorphism-Cyclic-Typeᵉ kᵉ Yᵉ
                    ( map-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ fᵉ xᵉ))
                  ( ( Hᵉ (endomorphism-Cyclic-Typeᵉ kᵉ Xᵉ xᵉ)) ∙ᵉ
                    ( coherence-square-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ fᵉ xᵉ))
                  ( ( coherence-square-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ eᵉ xᵉ) ∙ᵉ
                    ( apᵉ (endomorphism-Cyclic-Typeᵉ kᵉ Yᵉ) (Hᵉ xᵉ)))))))
      ( is-torsorial-htpy-equiv-Type-With-Endomorphismᵉ
        ( endo-Cyclic-Typeᵉ kᵉ Xᵉ)
        ( endo-Cyclic-Typeᵉ kᵉ Yᵉ)
        ( eᵉ))

  is-equiv-htpy-eq-equiv-Cyclic-Typeᵉ :
    (eᵉ fᵉ : equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ) → is-equivᵉ (htpy-eq-equiv-Cyclic-Typeᵉ eᵉ fᵉ)
  is-equiv-htpy-eq-equiv-Cyclic-Typeᵉ eᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-equiv-Cyclic-Typeᵉ eᵉ)
      ( htpy-eq-equiv-Cyclic-Typeᵉ eᵉ)

  extensionality-equiv-Cyclic-Typeᵉ :
    (eᵉ fᵉ : equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ) → (eᵉ ＝ᵉ fᵉ) ≃ᵉ htpy-equiv-Cyclic-Typeᵉ eᵉ fᵉ
  pr1ᵉ (extensionality-equiv-Cyclic-Typeᵉ eᵉ fᵉ) = htpy-eq-equiv-Cyclic-Typeᵉ eᵉ fᵉ
  pr2ᵉ (extensionality-equiv-Cyclic-Typeᵉ eᵉ fᵉ) =
    is-equiv-htpy-eq-equiv-Cyclic-Typeᵉ eᵉ fᵉ

  eq-htpy-equiv-Cyclic-Typeᵉ :
    (eᵉ fᵉ : equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ) → htpy-equiv-Cyclic-Typeᵉ eᵉ fᵉ → eᵉ ＝ᵉ fᵉ
  eq-htpy-equiv-Cyclic-Typeᵉ eᵉ fᵉ =
    map-inv-equivᵉ (extensionality-equiv-Cyclic-Typeᵉ eᵉ fᵉ)

comp-equiv-Cyclic-Typeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ : Cyclic-Typeᵉ l1ᵉ kᵉ) (Yᵉ : Cyclic-Typeᵉ l2ᵉ kᵉ)
  (Zᵉ : Cyclic-Typeᵉ l3ᵉ kᵉ) →
  equiv-Cyclic-Typeᵉ kᵉ Yᵉ Zᵉ → equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ → equiv-Cyclic-Typeᵉ kᵉ Xᵉ Zᵉ
comp-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ Zᵉ =
  comp-equiv-Type-With-Endomorphismᵉ
    ( endo-Cyclic-Typeᵉ kᵉ Xᵉ)
    ( endo-Cyclic-Typeᵉ kᵉ Yᵉ)
    ( endo-Cyclic-Typeᵉ kᵉ Zᵉ)

inv-equiv-Cyclic-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ : Cyclic-Typeᵉ l1ᵉ kᵉ) (Yᵉ : Cyclic-Typeᵉ l2ᵉ kᵉ) →
  equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ → equiv-Cyclic-Typeᵉ kᵉ Yᵉ Xᵉ
inv-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ =
  inv-equiv-Type-With-Endomorphismᵉ
    ( endo-Cyclic-Typeᵉ kᵉ Xᵉ)
    ( endo-Cyclic-Typeᵉ kᵉ Yᵉ)

associative-comp-equiv-Cyclic-Typeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ : Cyclic-Typeᵉ l1ᵉ kᵉ) (Yᵉ : Cyclic-Typeᵉ l2ᵉ kᵉ)
  (Zᵉ : Cyclic-Typeᵉ l3ᵉ kᵉ) (Wᵉ : Cyclic-Typeᵉ l4ᵉ kᵉ) (gᵉ : equiv-Cyclic-Typeᵉ kᵉ Zᵉ Wᵉ)
  (fᵉ : equiv-Cyclic-Typeᵉ kᵉ Yᵉ Zᵉ) (eᵉ : equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ) →
  ( comp-equiv-Cyclic-Typeᵉ
    kᵉ Xᵉ Yᵉ Wᵉ (comp-equiv-Cyclic-Typeᵉ kᵉ Yᵉ Zᵉ Wᵉ gᵉ fᵉ) eᵉ) ＝ᵉ
  ( comp-equiv-Cyclic-Typeᵉ
    kᵉ Xᵉ Zᵉ Wᵉ gᵉ (comp-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ Zᵉ fᵉ eᵉ))
associative-comp-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ Zᵉ Wᵉ gᵉ fᵉ eᵉ =
  eq-htpy-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Wᵉ
    ( comp-equiv-Cyclic-Typeᵉ
        kᵉ Xᵉ Yᵉ Wᵉ (comp-equiv-Cyclic-Typeᵉ kᵉ Yᵉ Zᵉ Wᵉ gᵉ fᵉ) eᵉ)
    ( comp-equiv-Cyclic-Typeᵉ
        kᵉ Xᵉ Zᵉ Wᵉ gᵉ (comp-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ Zᵉ fᵉ eᵉ))
    ( refl-htpyᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ : Cyclic-Typeᵉ l1ᵉ kᵉ) (Yᵉ : Cyclic-Typeᵉ l2ᵉ kᵉ)
  (eᵉ : equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ)
  where

  left-unit-law-comp-equiv-Cyclic-Typeᵉ :
    Idᵉ (comp-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ Yᵉ (id-equiv-Cyclic-Typeᵉ kᵉ Yᵉ) eᵉ) eᵉ
  left-unit-law-comp-equiv-Cyclic-Typeᵉ =
    eq-htpy-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ
      ( comp-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ Yᵉ (id-equiv-Cyclic-Typeᵉ kᵉ Yᵉ) eᵉ)
      ( eᵉ)
      ( refl-htpyᵉ)

  right-unit-law-comp-equiv-Cyclic-Typeᵉ :
    Idᵉ (comp-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Xᵉ Yᵉ eᵉ (id-equiv-Cyclic-Typeᵉ kᵉ Xᵉ)) eᵉ
  right-unit-law-comp-equiv-Cyclic-Typeᵉ =
    eq-htpy-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ
      ( comp-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Xᵉ Yᵉ eᵉ (id-equiv-Cyclic-Typeᵉ kᵉ Xᵉ))
      ( eᵉ)
      ( refl-htpyᵉ)

  left-inverse-law-comp-equiv-Cyclic-Typeᵉ :
    Idᵉ
      ( comp-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ Xᵉ (inv-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ eᵉ) eᵉ)
      ( id-equiv-Cyclic-Typeᵉ kᵉ Xᵉ)
  left-inverse-law-comp-equiv-Cyclic-Typeᵉ =
    eq-htpy-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Xᵉ
      ( comp-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ Xᵉ (inv-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ eᵉ) eᵉ)
      ( id-equiv-Cyclic-Typeᵉ kᵉ Xᵉ)
      ( is-retraction-map-inv-equivᵉ (equiv-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ eᵉ))

  right-inverse-law-comp-equiv-Cyclic-Typeᵉ :
    Idᵉ
      ( comp-equiv-Cyclic-Typeᵉ kᵉ Yᵉ Xᵉ Yᵉ eᵉ (inv-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ eᵉ))
      ( id-equiv-Cyclic-Typeᵉ kᵉ Yᵉ)
  right-inverse-law-comp-equiv-Cyclic-Typeᵉ =
    eq-htpy-equiv-Cyclic-Typeᵉ kᵉ Yᵉ Yᵉ
      ( comp-equiv-Cyclic-Typeᵉ kᵉ Yᵉ Xᵉ Yᵉ eᵉ (inv-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ eᵉ))
      ( id-equiv-Cyclic-Typeᵉ kᵉ Yᵉ)
      ( is-section-map-inv-equivᵉ (equiv-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ eᵉ))

mere-eq-Cyclic-Typeᵉ : {lᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ Yᵉ : Cyclic-Typeᵉ lᵉ kᵉ) → mere-eqᵉ Xᵉ Yᵉ
mere-eq-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ =
  apply-universal-property-trunc-Propᵉ
    ( mere-equiv-endo-Cyclic-Typeᵉ kᵉ Xᵉ)
    ( mere-eq-Propᵉ Xᵉ Yᵉ)
    ( λ eᵉ →
      apply-universal-property-trunc-Propᵉ
        ( mere-equiv-endo-Cyclic-Typeᵉ kᵉ Yᵉ)
        ( mere-eq-Propᵉ Xᵉ Yᵉ)
        ( λ fᵉ →
          unit-trunc-Propᵉ
            ( eq-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ
              ( comp-equiv-Cyclic-Typeᵉ kᵉ Xᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ) Yᵉ fᵉ
                ( inv-equiv-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ) Xᵉ eᵉ)))))

is-0-connected-Cyclic-Typeᵉ :
  (kᵉ : ℕᵉ) → is-0-connectedᵉ (Cyclic-Typeᵉ lzero kᵉ)
is-0-connected-Cyclic-Typeᵉ kᵉ =
  is-0-connected-mere-eqᵉ
    ( ℤ-Mod-Cyclic-Typeᵉ kᵉ)
    ( mere-eq-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ))

∞-group-Cyclic-Typeᵉ :
  (kᵉ : ℕᵉ) → ∞-Groupᵉ (lsuc lzero)
pr1ᵉ (∞-group-Cyclic-Typeᵉ kᵉ) = Cyclic-Type-Pointed-Typeᵉ kᵉ
pr2ᵉ (∞-group-Cyclic-Typeᵉ kᵉ) = is-0-connected-Cyclic-Typeᵉ kᵉ

Eq-Cyclic-Typeᵉ : (kᵉ : ℕᵉ) → Cyclic-Typeᵉ lzero kᵉ → UUᵉ lzero
Eq-Cyclic-Typeᵉ kᵉ Xᵉ = type-Cyclic-Typeᵉ kᵉ Xᵉ

refl-Eq-Cyclic-Typeᵉ : (kᵉ : ℕᵉ) → Eq-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ)
refl-Eq-Cyclic-Typeᵉ kᵉ = zero-ℤ-Modᵉ kᵉ

Eq-equiv-Cyclic-Typeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ : Cyclic-Typeᵉ lzero kᵉ) →
  equiv-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ) Xᵉ → Eq-Cyclic-Typeᵉ kᵉ Xᵉ
Eq-equiv-Cyclic-Typeᵉ kᵉ Xᵉ eᵉ =
  map-equiv-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ) Xᵉ eᵉ (zero-ℤ-Modᵉ kᵉ)

equiv-Eq-Cyclic-Typeᵉ :
  (kᵉ : ℕᵉ) → Eq-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ) →
  equiv-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ) (ℤ-Mod-Cyclic-Typeᵉ kᵉ)
pr1ᵉ (equiv-Eq-Cyclic-Typeᵉ kᵉ xᵉ) = equiv-add-ℤ-Mod'ᵉ kᵉ xᵉ
pr2ᵉ (equiv-Eq-Cyclic-Typeᵉ kᵉ xᵉ) yᵉ = left-successor-law-add-ℤ-Modᵉ kᵉ yᵉ xᵉ

is-section-equiv-Eq-Cyclic-Typeᵉ :
  (kᵉ : ℕᵉ) →
  (Eq-equiv-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ) ∘ᵉ equiv-Eq-Cyclic-Typeᵉ kᵉ) ~ᵉ idᵉ
is-section-equiv-Eq-Cyclic-Typeᵉ zero-ℕᵉ xᵉ = left-unit-law-add-ℤᵉ xᵉ
is-section-equiv-Eq-Cyclic-Typeᵉ (succ-ℕᵉ kᵉ) xᵉ = left-unit-law-add-Finᵉ kᵉ xᵉ

preserves-pred-preserves-succ-map-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (fᵉ : ℤ-Modᵉ kᵉ → ℤ-Modᵉ kᵉ) →
  (fᵉ ∘ᵉ succ-ℤ-Modᵉ kᵉ) ~ᵉ (succ-ℤ-Modᵉ kᵉ ∘ᵉ fᵉ) →
  (fᵉ ∘ᵉ pred-ℤ-Modᵉ kᵉ) ~ᵉ (pred-ℤ-Modᵉ kᵉ ∘ᵉ fᵉ)
preserves-pred-preserves-succ-map-ℤ-Modᵉ kᵉ fᵉ Hᵉ xᵉ =
  ( invᵉ (is-retraction-pred-ℤ-Modᵉ kᵉ (fᵉ (pred-ℤ-Modᵉ kᵉ xᵉ)))) ∙ᵉ
  ( apᵉ
    ( pred-ℤ-Modᵉ kᵉ)
    ( ( invᵉ (Hᵉ (pred-ℤ-Modᵉ kᵉ xᵉ))) ∙ᵉ
      ( apᵉ fᵉ (is-section-pred-ℤ-Modᵉ kᵉ xᵉ))))

compute-map-preserves-succ-map-ℤ-Mod'ᵉ :
  (kᵉ : ℕᵉ) (fᵉ : ℤ-Modᵉ kᵉ → ℤ-Modᵉ kᵉ) → (fᵉ ∘ᵉ succ-ℤ-Modᵉ kᵉ) ~ᵉ (succ-ℤ-Modᵉ kᵉ ∘ᵉ fᵉ) →
  (xᵉ : ℤᵉ) → Idᵉ (add-ℤ-Modᵉ kᵉ (mod-ℤᵉ kᵉ xᵉ) (fᵉ (zero-ℤ-Modᵉ kᵉ))) (fᵉ (mod-ℤᵉ kᵉ xᵉ))
compute-map-preserves-succ-map-ℤ-Mod'ᵉ kᵉ fᵉ Hᵉ (inlᵉ zero-ℕᵉ) =
  ( apᵉ (add-ℤ-Mod'ᵉ kᵉ (fᵉ (zero-ℤ-Modᵉ kᵉ))) (mod-neg-one-ℤᵉ kᵉ)) ∙ᵉ
  ( ( invᵉ (is-left-add-neg-one-pred-ℤ-Modᵉ kᵉ (fᵉ (zero-ℤ-Modᵉ kᵉ)))) ∙ᵉ
    ( ( apᵉ (pred-ℤ-Modᵉ kᵉ) (apᵉ fᵉ (invᵉ (mod-zero-ℤᵉ kᵉ)))) ∙ᵉ
      ( ( invᵉ
          ( preserves-pred-preserves-succ-map-ℤ-Modᵉ kᵉ fᵉ Hᵉ (mod-ℤᵉ kᵉ zero-ℤᵉ))) ∙ᵉ
        ( invᵉ (apᵉ fᵉ (preserves-predecessor-mod-ℤᵉ kᵉ zero-ℤᵉ))))))
compute-map-preserves-succ-map-ℤ-Mod'ᵉ kᵉ fᵉ Hᵉ (inlᵉ (succ-ℕᵉ xᵉ)) =
  ( apᵉ
    ( add-ℤ-Mod'ᵉ kᵉ (fᵉ (zero-ℤ-Modᵉ kᵉ)))
    ( preserves-predecessor-mod-ℤᵉ kᵉ (inlᵉ xᵉ))) ∙ᵉ
  ( ( left-predecessor-law-add-ℤ-Modᵉ kᵉ (mod-ℤᵉ kᵉ (inlᵉ xᵉ)) (fᵉ (zero-ℤ-Modᵉ kᵉ))) ∙ᵉ
    ( ( apᵉ
        ( pred-ℤ-Modᵉ kᵉ)
        ( compute-map-preserves-succ-map-ℤ-Mod'ᵉ kᵉ fᵉ Hᵉ (inlᵉ xᵉ))) ∙ᵉ
      ( ( invᵉ
          ( preserves-pred-preserves-succ-map-ℤ-Modᵉ kᵉ fᵉ Hᵉ (mod-ℤᵉ kᵉ (inlᵉ xᵉ)))) ∙ᵉ
        ( apᵉ fᵉ (invᵉ (preserves-predecessor-mod-ℤᵉ kᵉ (inlᵉ xᵉ)))))))
compute-map-preserves-succ-map-ℤ-Mod'ᵉ kᵉ fᵉ Hᵉ (inrᵉ (inlᵉ _)) =
  ( apᵉ (add-ℤ-Mod'ᵉ kᵉ (fᵉ (zero-ℤ-Modᵉ kᵉ))) (mod-zero-ℤᵉ kᵉ)) ∙ᵉ
  ( ( left-unit-law-add-ℤ-Modᵉ kᵉ (fᵉ (zero-ℤ-Modᵉ kᵉ))) ∙ᵉ
    ( apᵉ fᵉ (invᵉ (mod-zero-ℤᵉ kᵉ))))
compute-map-preserves-succ-map-ℤ-Mod'ᵉ kᵉ fᵉ Hᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) =
  ( ap-add-ℤ-Modᵉ kᵉ (mod-one-ℤᵉ kᵉ) (apᵉ fᵉ (invᵉ (mod-zero-ℤᵉ kᵉ)))) ∙ᵉ
  ( ( invᵉ (is-left-add-one-succ-ℤ-Modᵉ kᵉ (fᵉ (mod-ℤᵉ kᵉ zero-ℤᵉ)))) ∙ᵉ
    ( ( invᵉ (Hᵉ (mod-ℤᵉ kᵉ zero-ℤᵉ))) ∙ᵉ
      ( apᵉ fᵉ (invᵉ (preserves-successor-mod-ℤᵉ kᵉ zero-ℤᵉ)))))
compute-map-preserves-succ-map-ℤ-Mod'ᵉ kᵉ fᵉ Hᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) =
  ( apᵉ
    ( add-ℤ-Mod'ᵉ kᵉ (fᵉ (zero-ℤ-Modᵉ kᵉ)))
    ( preserves-successor-mod-ℤᵉ kᵉ (inrᵉ (inrᵉ xᵉ)))) ∙ᵉ
  ( ( left-successor-law-add-ℤ-Modᵉ kᵉ
      ( mod-ℤᵉ kᵉ (inrᵉ (inrᵉ xᵉ)))
      ( fᵉ (zero-ℤ-Modᵉ kᵉ))) ∙ᵉ
    ( ( apᵉ
        ( succ-ℤ-Modᵉ kᵉ)
        ( compute-map-preserves-succ-map-ℤ-Mod'ᵉ kᵉ fᵉ Hᵉ (inrᵉ (inrᵉ xᵉ)))) ∙ᵉ
      ( ( invᵉ (Hᵉ (mod-ℤᵉ kᵉ (inrᵉ (inrᵉ xᵉ))))) ∙ᵉ
        ( apᵉ fᵉ (invᵉ (preserves-successor-mod-ℤᵉ kᵉ (inrᵉ (inrᵉ xᵉ))))))))

compute-map-preserves-succ-map-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (fᵉ : ℤ-Modᵉ kᵉ → ℤ-Modᵉ kᵉ) (Hᵉ : (fᵉ ∘ᵉ succ-ℤ-Modᵉ kᵉ) ~ᵉ (succ-ℤ-Modᵉ kᵉ ∘ᵉ fᵉ))
  (xᵉ : ℤ-Modᵉ kᵉ) → Idᵉ (add-ℤ-Modᵉ kᵉ xᵉ (fᵉ (zero-ℤ-Modᵉ kᵉ))) (fᵉ xᵉ)
compute-map-preserves-succ-map-ℤ-Modᵉ kᵉ fᵉ Hᵉ xᵉ =
  ( apᵉ (add-ℤ-Mod'ᵉ kᵉ (fᵉ (zero-ℤ-Modᵉ kᵉ))) (invᵉ (is-section-int-ℤ-Modᵉ kᵉ xᵉ))) ∙ᵉ
  ( ( compute-map-preserves-succ-map-ℤ-Mod'ᵉ kᵉ fᵉ Hᵉ (int-ℤ-Modᵉ kᵉ xᵉ)) ∙ᵉ
    ( apᵉ fᵉ (is-section-int-ℤ-Modᵉ kᵉ xᵉ)))

is-retraction-equiv-Eq-Cyclic-Typeᵉ :
  (kᵉ : ℕᵉ) →
  (equiv-Eq-Cyclic-Typeᵉ kᵉ ∘ᵉ Eq-equiv-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ)) ~ᵉ idᵉ
is-retraction-equiv-Eq-Cyclic-Typeᵉ kᵉ eᵉ =
  eq-htpy-equiv-Cyclic-Typeᵉ kᵉ
    ( ℤ-Mod-Cyclic-Typeᵉ kᵉ)
    ( ℤ-Mod-Cyclic-Typeᵉ kᵉ)
    ( equiv-Eq-Cyclic-Typeᵉ kᵉ (Eq-equiv-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ) eᵉ))
    ( eᵉ)
    ( compute-map-preserves-succ-map-ℤ-Modᵉ
      ( kᵉ)
      ( map-equiv-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ) (ℤ-Mod-Cyclic-Typeᵉ kᵉ) eᵉ)
      ( coherence-square-equiv-Cyclic-Typeᵉ
        ( kᵉ)
        ( ℤ-Mod-Cyclic-Typeᵉ kᵉ)
        ( ℤ-Mod-Cyclic-Typeᵉ kᵉ)
        ( eᵉ)))

abstract
  is-equiv-Eq-equiv-Cyclic-Typeᵉ :
    (kᵉ : ℕᵉ) (Xᵉ : Cyclic-Typeᵉ lzero kᵉ) → is-equivᵉ (Eq-equiv-Cyclic-Typeᵉ kᵉ Xᵉ)
  is-equiv-Eq-equiv-Cyclic-Typeᵉ kᵉ Xᵉ =
    apply-universal-property-trunc-Propᵉ
      ( mere-eq-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ) Xᵉ)
      ( is-equiv-Propᵉ (Eq-equiv-Cyclic-Typeᵉ kᵉ Xᵉ))
      ( λ where
        reflᵉ →
          is-equiv-is-invertibleᵉ
            ( equiv-Eq-Cyclic-Typeᵉ kᵉ)
            ( is-section-equiv-Eq-Cyclic-Typeᵉ kᵉ)
            ( is-retraction-equiv-Eq-Cyclic-Typeᵉ kᵉ))

equiv-compute-Ω-Cyclic-Typeᵉ :
  (kᵉ : ℕᵉ) → type-Ωᵉ (pairᵉ (Cyclic-Typeᵉ lzero kᵉ) (ℤ-Mod-Cyclic-Typeᵉ kᵉ)) ≃ᵉ ℤ-Modᵉ kᵉ
equiv-compute-Ω-Cyclic-Typeᵉ kᵉ =
  ( pairᵉ
    ( Eq-equiv-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ))
    ( is-equiv-Eq-equiv-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ))) ∘eᵉ
  ( extensionality-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ) (ℤ-Mod-Cyclic-Typeᵉ kᵉ))

map-equiv-compute-Ω-Cyclic-Typeᵉ :
  (kᵉ : ℕᵉ) → type-Ωᵉ (pairᵉ (Cyclic-Typeᵉ lzero kᵉ) (ℤ-Mod-Cyclic-Typeᵉ kᵉ)) → ℤ-Modᵉ kᵉ
map-equiv-compute-Ω-Cyclic-Typeᵉ kᵉ = map-equivᵉ (equiv-compute-Ω-Cyclic-Typeᵉ kᵉ)

preserves-concat-equiv-eq-Cyclic-Typeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ Yᵉ Zᵉ : Cyclic-Typeᵉ lzero kᵉ) (pᵉ : Idᵉ Xᵉ Yᵉ) (qᵉ : Idᵉ Yᵉ Zᵉ) →
  Idᵉ
    ( equiv-eq-Cyclic-Typeᵉ kᵉ Xᵉ Zᵉ (pᵉ ∙ᵉ qᵉ))
    ( comp-equiv-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ Zᵉ
      ( equiv-eq-Cyclic-Typeᵉ kᵉ Yᵉ Zᵉ qᵉ)
      ( equiv-eq-Cyclic-Typeᵉ kᵉ Xᵉ Yᵉ pᵉ))
preserves-concat-equiv-eq-Cyclic-Typeᵉ kᵉ Xᵉ .Xᵉ Zᵉ reflᵉ qᵉ =
  invᵉ
    ( right-unit-law-comp-equiv-Cyclic-Typeᵉ
        kᵉ Xᵉ Zᵉ (equiv-eq-Cyclic-Typeᵉ kᵉ Xᵉ Zᵉ qᵉ))

preserves-comp-Eq-equiv-Cyclic-Typeᵉ :
  (kᵉ : ℕᵉ)
  (eᵉ fᵉ : equiv-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ) (ℤ-Mod-Cyclic-Typeᵉ kᵉ)) →
  Idᵉ
    ( Eq-equiv-Cyclic-Typeᵉ kᵉ
      ( ℤ-Mod-Cyclic-Typeᵉ kᵉ)
      ( comp-equiv-Cyclic-Typeᵉ kᵉ
        ( ℤ-Mod-Cyclic-Typeᵉ kᵉ)
        ( ℤ-Mod-Cyclic-Typeᵉ kᵉ)
        ( ℤ-Mod-Cyclic-Typeᵉ kᵉ)
        ( fᵉ)
        ( eᵉ)))
    ( add-ℤ-Modᵉ kᵉ
      ( Eq-equiv-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ) eᵉ)
      ( Eq-equiv-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ) fᵉ))
preserves-comp-Eq-equiv-Cyclic-Typeᵉ kᵉ eᵉ fᵉ =
  invᵉ
  ( compute-map-preserves-succ-map-ℤ-Modᵉ kᵉ
    ( map-equiv-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ) (ℤ-Mod-Cyclic-Typeᵉ kᵉ) fᵉ)
    ( coherence-square-equiv-Cyclic-Typeᵉ kᵉ
      ( ℤ-Mod-Cyclic-Typeᵉ kᵉ)
      ( ℤ-Mod-Cyclic-Typeᵉ kᵉ)
      ( fᵉ))
    ( map-equiv-Cyclic-Typeᵉ kᵉ
      ( ℤ-Mod-Cyclic-Typeᵉ kᵉ)
      ( ℤ-Mod-Cyclic-Typeᵉ kᵉ)
      ( eᵉ)
      ( zero-ℤ-Modᵉ kᵉ)))

preserves-concat-equiv-compute-Ω-Cyclic-Typeᵉ :
  (kᵉ : ℕᵉ) {pᵉ qᵉ : type-Ωᵉ (Cyclic-Type-Pointed-Typeᵉ kᵉ)} →
  Idᵉ
    ( map-equivᵉ (equiv-compute-Ω-Cyclic-Typeᵉ kᵉ) (pᵉ ∙ᵉ qᵉ))
    ( add-ℤ-Modᵉ kᵉ
      ( map-equivᵉ (equiv-compute-Ω-Cyclic-Typeᵉ kᵉ) pᵉ)
      ( map-equivᵉ (equiv-compute-Ω-Cyclic-Typeᵉ kᵉ) qᵉ))
preserves-concat-equiv-compute-Ω-Cyclic-Typeᵉ kᵉ {pᵉ} {qᵉ} =
  ( apᵉ
    ( Eq-equiv-Cyclic-Typeᵉ kᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ))
    ( preserves-concat-equiv-eq-Cyclic-Typeᵉ kᵉ
      ( ℤ-Mod-Cyclic-Typeᵉ kᵉ)
      ( ℤ-Mod-Cyclic-Typeᵉ kᵉ)
      ( ℤ-Mod-Cyclic-Typeᵉ kᵉ)
      ( pᵉ)
      ( qᵉ))) ∙ᵉ
  ( preserves-comp-Eq-equiv-Cyclic-Typeᵉ kᵉ
    ( equiv-eq-Cyclic-Typeᵉ kᵉ ( ℤ-Mod-Cyclic-Typeᵉ kᵉ) ( ℤ-Mod-Cyclic-Typeᵉ kᵉ) pᵉ)
    ( equiv-eq-Cyclic-Typeᵉ kᵉ ( ℤ-Mod-Cyclic-Typeᵉ kᵉ) ( ℤ-Mod-Cyclic-Typeᵉ kᵉ) qᵉ))

type-Ω-Cyclic-Typeᵉ : (kᵉ : ℕᵉ) → UUᵉ (lsuc lzero)
type-Ω-Cyclic-Typeᵉ kᵉ = Idᵉ (ℤ-Mod-Cyclic-Typeᵉ kᵉ) (ℤ-Mod-Cyclic-Typeᵉ kᵉ)

is-set-type-Ω-Cyclic-Typeᵉ : (kᵉ : ℕᵉ) → is-setᵉ (type-Ω-Cyclic-Typeᵉ kᵉ)
is-set-type-Ω-Cyclic-Typeᵉ kᵉ =
  is-set-equivᵉ
    ( ℤ-Modᵉ kᵉ)
    ( equiv-compute-Ω-Cyclic-Typeᵉ kᵉ)
    ( is-set-ℤ-Modᵉ kᵉ)

concrete-group-Cyclic-Typeᵉ :
  (kᵉ : ℕᵉ) → Concrete-Groupᵉ (lsuc lzero)
pr1ᵉ (concrete-group-Cyclic-Typeᵉ kᵉ) = ∞-group-Cyclic-Typeᵉ kᵉ
pr2ᵉ (concrete-group-Cyclic-Typeᵉ kᵉ) = is-set-type-Ω-Cyclic-Typeᵉ kᵉ

Ω-Cyclic-Type-Groupᵉ : (kᵉ : ℕᵉ) → Groupᵉ (lsuc lzero)
Ω-Cyclic-Type-Groupᵉ kᵉ =
  loop-space-Groupᵉ
    ( pairᵉ (Cyclic-Typeᵉ lzero kᵉ) (ℤ-Mod-Cyclic-Typeᵉ kᵉ))
    ( is-set-type-Ω-Cyclic-Typeᵉ kᵉ)

equiv-Ω-Cyclic-Type-Groupᵉ :
  (kᵉ : ℕᵉ) → equiv-Groupᵉ (Ω-Cyclic-Type-Groupᵉ kᵉ) (ℤ-Mod-Groupᵉ kᵉ)
pr1ᵉ (equiv-Ω-Cyclic-Type-Groupᵉ kᵉ) = equiv-compute-Ω-Cyclic-Typeᵉ kᵉ
pr2ᵉ (equiv-Ω-Cyclic-Type-Groupᵉ kᵉ) {xᵉ} {yᵉ} =
  preserves-concat-equiv-compute-Ω-Cyclic-Typeᵉ kᵉ {xᵉ} {yᵉ}

iso-Ω-Cyclic-Type-Groupᵉ :
  (kᵉ : ℕᵉ) → iso-Groupᵉ (Ω-Cyclic-Type-Groupᵉ kᵉ) (ℤ-Mod-Groupᵉ kᵉ)
iso-Ω-Cyclic-Type-Groupᵉ kᵉ =
  iso-equiv-Groupᵉ
    ( Ω-Cyclic-Type-Groupᵉ kᵉ)
    ( ℤ-Mod-Groupᵉ kᵉ)
    ( equiv-Ω-Cyclic-Type-Groupᵉ kᵉ)
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}