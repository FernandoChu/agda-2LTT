# Infinite cyclic types

```agda
module synthetic-homotopy-theory.infinite-cyclic-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.equivalences-types-equipped-with-endomorphismsᵉ
open import structured-types.initial-pointed-type-equipped-with-automorphismᵉ
open import structured-types.mere-equivalences-types-equipped-with-endomorphismsᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.pointed-types-equipped-with-automorphismsᵉ
open import structured-types.types-equipped-with-endomorphismsᵉ

open import synthetic-homotopy-theory.loop-spacesᵉ

open import univalent-combinatorics.cyclic-finite-typesᵉ
```

</details>

## Definitions

```agda
Infinite-Cyclic-Typeᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Infinite-Cyclic-Typeᵉ lᵉ = Cyclic-Typeᵉ lᵉ zero-ℕᵉ

ℤ-Infinite-Cyclic-Typeᵉ : Infinite-Cyclic-Typeᵉ lzero
ℤ-Infinite-Cyclic-Typeᵉ = ℤ-Mod-Cyclic-Typeᵉ zero-ℕᵉ

Infinite-Cyclic-Type-Pointed-Typeᵉ : Pointed-Typeᵉ (lsuc lzero)
Infinite-Cyclic-Type-Pointed-Typeᵉ = Cyclic-Type-Pointed-Typeᵉ zero-ℕᵉ

module _
  {lᵉ : Level} (Xᵉ : Infinite-Cyclic-Typeᵉ lᵉ)
  where

  endo-Infinite-Cyclic-Typeᵉ : Type-With-Endomorphismᵉ lᵉ
  endo-Infinite-Cyclic-Typeᵉ = endo-Cyclic-Typeᵉ zero-ℕᵉ Xᵉ

  type-Infinite-Cyclic-Typeᵉ : UUᵉ lᵉ
  type-Infinite-Cyclic-Typeᵉ = type-Cyclic-Typeᵉ zero-ℕᵉ Xᵉ

  endomorphism-Infinite-Cyclic-Typeᵉ :
    type-Infinite-Cyclic-Typeᵉ → type-Infinite-Cyclic-Typeᵉ
  endomorphism-Infinite-Cyclic-Typeᵉ = endomorphism-Cyclic-Typeᵉ zero-ℕᵉ Xᵉ

  mere-equiv-ℤ-Infinite-Cyclic-Typeᵉ :
    mere-equiv-Type-With-Endomorphismᵉ
      ( ℤ-Type-With-Endomorphismᵉ)
      ( endo-Infinite-Cyclic-Typeᵉ)
  mere-equiv-ℤ-Infinite-Cyclic-Typeᵉ = pr2ᵉ Xᵉ

module _
  (lᵉ : Level)
  where

  point-Infinite-Cyclic-Typeᵉ : Infinite-Cyclic-Typeᵉ lᵉ
  pr1ᵉ (pr1ᵉ point-Infinite-Cyclic-Typeᵉ) = raiseᵉ lᵉ ℤᵉ
  pr2ᵉ (pr1ᵉ point-Infinite-Cyclic-Typeᵉ) = (map-raiseᵉ ∘ᵉ succ-ℤᵉ) ∘ᵉ map-inv-raiseᵉ
  pr2ᵉ point-Infinite-Cyclic-Typeᵉ =
    unit-trunc-Propᵉ (pairᵉ (compute-raiseᵉ lᵉ ℤᵉ) refl-htpyᵉ)

  Infinite-Cyclic-Type-Pointed-Type-Levelᵉ : Pointed-Typeᵉ (lsuc lᵉ)
  pr1ᵉ Infinite-Cyclic-Type-Pointed-Type-Levelᵉ = Infinite-Cyclic-Typeᵉ lᵉ
  pr2ᵉ Infinite-Cyclic-Type-Pointed-Type-Levelᵉ = point-Infinite-Cyclic-Typeᵉ

module _
  {l1ᵉ : Level} (Xᵉ : Infinite-Cyclic-Typeᵉ l1ᵉ)
  where

  equiv-Infinite-Cyclic-Typeᵉ :
    {l2ᵉ : Level} → Infinite-Cyclic-Typeᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equiv-Infinite-Cyclic-Typeᵉ = equiv-Cyclic-Typeᵉ zero-ℕᵉ Xᵉ

  id-equiv-Infinite-Cyclic-Typeᵉ : equiv-Infinite-Cyclic-Typeᵉ Xᵉ
  id-equiv-Infinite-Cyclic-Typeᵉ = id-equiv-Cyclic-Typeᵉ zero-ℕᵉ Xᵉ

  equiv-eq-Infinite-Cyclic-Typeᵉ :
    (Yᵉ : Infinite-Cyclic-Typeᵉ l1ᵉ) → Idᵉ Xᵉ Yᵉ → equiv-Infinite-Cyclic-Typeᵉ Yᵉ
  equiv-eq-Infinite-Cyclic-Typeᵉ = equiv-eq-Cyclic-Typeᵉ zero-ℕᵉ Xᵉ

  is-torsorial-equiv-Infinite-Cyclic-Typeᵉ :
    is-torsorialᵉ equiv-Infinite-Cyclic-Typeᵉ
  is-torsorial-equiv-Infinite-Cyclic-Typeᵉ =
    is-torsorial-equiv-Cyclic-Typeᵉ zero-ℕᵉ Xᵉ

  is-equiv-equiv-eq-Infinite-Cyclic-Typeᵉ :
    (Yᵉ : Infinite-Cyclic-Typeᵉ l1ᵉ) → is-equivᵉ (equiv-eq-Infinite-Cyclic-Typeᵉ Yᵉ)
  is-equiv-equiv-eq-Infinite-Cyclic-Typeᵉ =
    is-equiv-equiv-eq-Cyclic-Typeᵉ zero-ℕᵉ Xᵉ

  extensionality-Infinite-Cyclic-Typeᵉ :
    (Yᵉ : Infinite-Cyclic-Typeᵉ l1ᵉ) → Idᵉ Xᵉ Yᵉ ≃ᵉ equiv-Infinite-Cyclic-Typeᵉ Yᵉ
  extensionality-Infinite-Cyclic-Typeᵉ = extensionality-Cyclic-Typeᵉ zero-ℕᵉ Xᵉ

module _
  where

  map-left-factor-compute-Ω-Infinite-Cyclic-Typeᵉ :
    equiv-Infinite-Cyclic-Typeᵉ ℤ-Infinite-Cyclic-Typeᵉ ℤ-Infinite-Cyclic-Typeᵉ → ℤᵉ
  map-left-factor-compute-Ω-Infinite-Cyclic-Typeᵉ eᵉ =
    map-equiv-Type-With-Endomorphismᵉ
      ( ℤ-Type-With-Endomorphismᵉ)
      ( ℤ-Type-With-Endomorphismᵉ)
      ( eᵉ)
      ( zero-ℤᵉ)

  abstract
    is-equiv-map-left-factor-compute-Ω-Infinite-Cyclic-Typeᵉ :
      is-equivᵉ map-left-factor-compute-Ω-Infinite-Cyclic-Typeᵉ
    is-equiv-map-left-factor-compute-Ω-Infinite-Cyclic-Typeᵉ =
      is-equiv-is-contr-mapᵉ
        ( λ xᵉ →
          is-contr-equivᵉ
            ( hom-Pointed-Type-With-Autᵉ
                ℤ-Pointed-Type-With-Autᵉ
                ℤ-Pointed-Type-With-Autᵉ)
            ( ( right-unit-law-Σ-is-contrᵉ
                { Bᵉ = λ fᵉ → is-equivᵉ (pr1ᵉ fᵉ)}
                ( λ fᵉ →
                  is-proof-irrelevant-is-propᵉ
                    ( is-property-is-equivᵉ (pr1ᵉ fᵉ))
                    ( is-equiv-htpyᵉ idᵉ
                      ( htpy-eqᵉ
                        ( apᵉ
                          ( pr1ᵉ)
                          { xᵉ = fᵉ}
                          { yᵉ = pairᵉ idᵉ (pairᵉ reflᵉ refl-htpyᵉ)}
                          ( eq-is-contrᵉ
                            ( is-initial-ℤ-Pointed-Type-With-Autᵉ
                              ℤ-Pointed-Type-With-Autᵉ))))
                      ( is-equiv-idᵉ)))) ∘eᵉ
              ( ( equiv-right-swap-Σᵉ) ∘eᵉ
                ( ( associative-Σᵉ
                    ( ℤᵉ ≃ᵉ ℤᵉ)
                    ( λ eᵉ → Idᵉ (map-equivᵉ eᵉ zero-ℤᵉ) zero-ℤᵉ)
                    ( λ eᵉ →
                      ( map-equivᵉ (pr1ᵉ eᵉ) ∘ᵉ succ-ℤᵉ) ~ᵉ
                      ( succ-ℤᵉ ∘ᵉ map-equivᵉ (pr1ᵉ eᵉ)))) ∘eᵉ
                  ( ( equiv-right-swap-Σᵉ) ∘eᵉ
                    ( equiv-Σᵉ
                      ( λ eᵉ → Idᵉ (map-equivᵉ (pr1ᵉ eᵉ) zero-ℤᵉ) zero-ℤᵉ)
                      ( equiv-Σᵉ
                        ( λ eᵉ → (map-equivᵉ eᵉ ∘ᵉ succ-ℤᵉ) ~ᵉ (succ-ℤᵉ ∘ᵉ map-equivᵉ eᵉ))
                        ( equiv-postcomp-equivᵉ (equiv-left-add-ℤᵉ (neg-ℤᵉ xᵉ)) ℤᵉ)
                        ( λ eᵉ →
                          equiv-Π-equiv-familyᵉ
                            ( λ kᵉ →
                              ( equiv-concat'ᵉ
                                ( (neg-ℤᵉ xᵉ) +ℤᵉ (map-equivᵉ eᵉ (succ-ℤᵉ kᵉ)))
                                ( right-successor-law-add-ℤᵉ
                                  ( neg-ℤᵉ xᵉ)
                                  ( map-equivᵉ eᵉ kᵉ))) ∘eᵉ
                              ( equiv-apᵉ
                                ( equiv-left-add-ℤᵉ (neg-ℤᵉ xᵉ))
                                ( map-equivᵉ eᵉ (succ-ℤᵉ kᵉ))
                                ( succ-ℤᵉ (map-equivᵉ eᵉ kᵉ))))))
                      ( λ eᵉ →
                        ( equiv-concat'ᵉ
                          ( (neg-ℤᵉ xᵉ) +ℤᵉ (map-equivᵉ (pr1ᵉ eᵉ) zero-ℤᵉ))
                          ( left-inverse-law-add-ℤᵉ xᵉ)) ∘eᵉ
                        ( equiv-apᵉ
                          ( equiv-left-add-ℤᵉ (neg-ℤᵉ xᵉ))
                          ( map-equivᵉ (pr1ᵉ eᵉ) zero-ℤᵉ)
                          ( xᵉ))))))))
            ( is-initial-ℤ-Pointed-Type-With-Autᵉ ℤ-Pointed-Type-With-Autᵉ))

  equiv-left-factor-compute-Ω-Infinite-Cyclic-Typeᵉ :
    equiv-Infinite-Cyclic-Typeᵉ
      ℤ-Infinite-Cyclic-Typeᵉ
      ℤ-Infinite-Cyclic-Typeᵉ ≃ᵉ ℤᵉ
  pr1ᵉ equiv-left-factor-compute-Ω-Infinite-Cyclic-Typeᵉ =
    map-left-factor-compute-Ω-Infinite-Cyclic-Typeᵉ
  pr2ᵉ equiv-left-factor-compute-Ω-Infinite-Cyclic-Typeᵉ =
    is-equiv-map-left-factor-compute-Ω-Infinite-Cyclic-Typeᵉ

  compute-Ω-Infinite-Cyclic-Typeᵉ :
    type-Ωᵉ (Infinite-Cyclic-Type-Pointed-Typeᵉ) ≃ᵉ ℤᵉ
  compute-Ω-Infinite-Cyclic-Typeᵉ =
    ( equiv-left-factor-compute-Ω-Infinite-Cyclic-Typeᵉ) ∘eᵉ
    ( extensionality-Infinite-Cyclic-Typeᵉ
        ℤ-Infinite-Cyclic-Typeᵉ
        ℤ-Infinite-Cyclic-Typeᵉ)
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}