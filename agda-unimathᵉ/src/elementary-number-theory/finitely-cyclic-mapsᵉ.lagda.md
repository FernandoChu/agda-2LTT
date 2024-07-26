# Finitely cyclic maps

```agda
module elementary-number-theory.finitely-cyclic-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterating-functionsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Definitions

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  is-finitely-cyclic-mapᵉ : (fᵉ : Xᵉ → Xᵉ) → UUᵉ lᵉ
  is-finitely-cyclic-mapᵉ fᵉ = (xᵉ yᵉ : Xᵉ) → Σᵉ ℕᵉ (λ kᵉ → iterateᵉ kᵉ fᵉ xᵉ ＝ᵉ yᵉ)

  length-path-is-finitely-cyclic-mapᵉ :
    {fᵉ : Xᵉ → Xᵉ} → is-finitely-cyclic-mapᵉ fᵉ → Xᵉ → Xᵉ → ℕᵉ
  length-path-is-finitely-cyclic-mapᵉ Hᵉ xᵉ yᵉ = pr1ᵉ (Hᵉ xᵉ yᵉ)

  eq-is-finitely-cyclic-mapᵉ :
    {fᵉ : Xᵉ → Xᵉ} (Hᵉ : is-finitely-cyclic-mapᵉ fᵉ) (xᵉ yᵉ : Xᵉ) →
    iterateᵉ (length-path-is-finitely-cyclic-mapᵉ Hᵉ xᵉ yᵉ) fᵉ xᵉ ＝ᵉ yᵉ
  eq-is-finitely-cyclic-mapᵉ Hᵉ xᵉ yᵉ = pr2ᵉ (Hᵉ xᵉ yᵉ)
```

## Properties

### Finitely cyclic maps are equivalences

```agda
  map-inv-is-finitely-cyclic-mapᵉ :
    (fᵉ : Xᵉ → Xᵉ) (Hᵉ : is-finitely-cyclic-mapᵉ fᵉ) → Xᵉ → Xᵉ
  map-inv-is-finitely-cyclic-mapᵉ fᵉ Hᵉ xᵉ =
    iterateᵉ (length-path-is-finitely-cyclic-mapᵉ Hᵉ (fᵉ xᵉ) xᵉ) fᵉ xᵉ

  is-section-map-inv-is-finitely-cyclic-mapᵉ :
    (fᵉ : Xᵉ → Xᵉ) (Hᵉ : is-finitely-cyclic-mapᵉ fᵉ) →
    (fᵉ ∘ᵉ map-inv-is-finitely-cyclic-mapᵉ fᵉ Hᵉ) ~ᵉ idᵉ
  is-section-map-inv-is-finitely-cyclic-mapᵉ fᵉ Hᵉ xᵉ =
    ( iterate-succ-ℕᵉ (length-path-is-finitely-cyclic-mapᵉ Hᵉ (fᵉ xᵉ) xᵉ) fᵉ xᵉ) ∙ᵉ
    ( eq-is-finitely-cyclic-mapᵉ Hᵉ (fᵉ xᵉ) xᵉ)

  is-retraction-map-inv-is-finitely-cyclic-mapᵉ :
    (fᵉ : Xᵉ → Xᵉ) (Hᵉ : is-finitely-cyclic-mapᵉ fᵉ) →
    (map-inv-is-finitely-cyclic-mapᵉ fᵉ Hᵉ ∘ᵉ fᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-is-finitely-cyclic-mapᵉ fᵉ Hᵉ xᵉ =
    ( apᵉ
      ( iterateᵉ (length-path-is-finitely-cyclic-mapᵉ Hᵉ (fᵉ (fᵉ xᵉ)) (fᵉ xᵉ)) fᵉ ∘ᵉ fᵉ)
      ( invᵉ (eq-is-finitely-cyclic-mapᵉ Hᵉ (fᵉ xᵉ) xᵉ))) ∙ᵉ
    ( ( apᵉ
        ( iterateᵉ (length-path-is-finitely-cyclic-mapᵉ Hᵉ (fᵉ (fᵉ xᵉ)) (fᵉ xᵉ)) fᵉ)
          ( iterate-succ-ℕᵉ
            ( length-path-is-finitely-cyclic-mapᵉ Hᵉ (fᵉ xᵉ) xᵉ) fᵉ (fᵉ xᵉ))) ∙ᵉ
      ( ( iterate-iterateᵉ
          ( length-path-is-finitely-cyclic-mapᵉ Hᵉ (fᵉ (fᵉ xᵉ)) (fᵉ xᵉ))
          ( length-path-is-finitely-cyclic-mapᵉ Hᵉ (fᵉ xᵉ) xᵉ) fᵉ (fᵉ (fᵉ xᵉ))) ∙ᵉ
        ( ( apᵉ
            ( iterateᵉ (length-path-is-finitely-cyclic-mapᵉ Hᵉ (fᵉ xᵉ) xᵉ) fᵉ)
            ( eq-is-finitely-cyclic-mapᵉ Hᵉ (fᵉ (fᵉ xᵉ)) (fᵉ xᵉ))) ∙ᵉ
          ( eq-is-finitely-cyclic-mapᵉ Hᵉ (fᵉ xᵉ) xᵉ))))

  is-equiv-is-finitely-cyclic-mapᵉ :
    (fᵉ : Xᵉ → Xᵉ) → is-finitely-cyclic-mapᵉ fᵉ → is-equivᵉ fᵉ
  is-equiv-is-finitely-cyclic-mapᵉ fᵉ Hᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-is-finitely-cyclic-mapᵉ fᵉ Hᵉ)
      ( is-section-map-inv-is-finitely-cyclic-mapᵉ fᵉ Hᵉ)
      ( is-retraction-map-inv-is-finitely-cyclic-mapᵉ fᵉ Hᵉ)
```

### The successor functions on standard finite types are finitely cyclic

```agda
compute-iterate-succ-Finᵉ :
  {kᵉ : ℕᵉ} (nᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) →
  iterateᵉ nᵉ (succ-Finᵉ (succ-ℕᵉ kᵉ)) xᵉ ＝ᵉ add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (mod-succ-ℕᵉ kᵉ nᵉ)
compute-iterate-succ-Finᵉ {kᵉ} zero-ℕᵉ xᵉ = invᵉ (right-unit-law-add-Finᵉ kᵉ xᵉ)
compute-iterate-succ-Finᵉ {kᵉ} (succ-ℕᵉ nᵉ) xᵉ =
  ( apᵉ (succ-Finᵉ (succ-ℕᵉ kᵉ)) (compute-iterate-succ-Finᵉ nᵉ xᵉ)) ∙ᵉ
  ( invᵉ (right-successor-law-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (mod-succ-ℕᵉ kᵉ nᵉ)))

is-finitely-cyclic-succ-Finᵉ : {kᵉ : ℕᵉ} → is-finitely-cyclic-mapᵉ (succ-Finᵉ kᵉ)
pr1ᵉ (is-finitely-cyclic-succ-Finᵉ {succ-ℕᵉ kᵉ} xᵉ yᵉ) =
  nat-Finᵉ (succ-ℕᵉ kᵉ) (add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))
pr2ᵉ (is-finitely-cyclic-succ-Finᵉ {succ-ℕᵉ kᵉ} xᵉ yᵉ) =
  ( compute-iterate-succ-Finᵉ
    ( nat-Finᵉ (succ-ℕᵉ kᵉ) (add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)))
    ( xᵉ)) ∙ᵉ
    ( ( apᵉ
        ( add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
        ( is-section-nat-Finᵉ kᵉ (add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)))) ∙ᵉ
      ( ( commutative-add-Finᵉ
          ( succ-ℕᵉ kᵉ)
          ( xᵉ)
          ( add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))) ∙ᵉ
        ( ( associative-add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) xᵉ) ∙ᵉ
          ( ( apᵉ (add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ) (left-inverse-law-add-Finᵉ kᵉ xᵉ)) ∙ᵉ
            ( right-unit-law-add-Finᵉ kᵉ yᵉ)))))
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}