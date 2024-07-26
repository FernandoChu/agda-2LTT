# Methane

```agda
module organic-chemistry.methaneᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbersᵉ

open import finite-group-theory.tetrahedra-in-3-spaceᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.walks-undirected-graphsᵉ

open import organic-chemistry.alkanesᵉ
open import organic-chemistry.hydrocarbonsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>
## Idea

**Methane**ᵉ isᵉ theᵉ simplestᵉ hydrocarbon,ᵉ andᵉ theᵉ firstᵉ alkane.ᵉ

## Definition

```agda
module _
  (tᵉ : tetrahedron-in-3-spaceᵉ)
  where

  methaneᵉ : hydrocarbonᵉ lzero lzero
  pr1ᵉ (pr1ᵉ methaneᵉ) = unit-𝔽ᵉ
  pr2ᵉ (pr1ᵉ methaneᵉ) xᵉ = empty-𝔽ᵉ
  pr1ᵉ (pr2ᵉ methaneᵉ) cᵉ = tᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ methaneᵉ)) cᵉ) eᵉ = ex-falsoᵉ (pr2ᵉ eᵉ)
  pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ methaneᵉ)) cᵉ) eᵉ = ex-falsoᵉ (pr2ᵉ eᵉ)
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ methaneᵉ))) cᵉ xᵉ = xᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ methaneᵉ)))) cᵉ c'ᵉ =
    concatenate-eq-leq-ℕᵉ
      ( 3ᵉ)
      ( invᵉ (compute-number-of-elements-is-finiteᵉ count-emptyᵉ is-finite-emptyᵉ))
      ( starᵉ)
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ methaneᵉ)))) starᵉ starᵉ =
    unit-trunc-Propᵉ refl-walk-Undirected-Graphᵉ

  is-alkane-methaneᵉ : is-alkane-hydrocarbonᵉ methaneᵉ
  is-alkane-methaneᵉ cᵉ c'ᵉ eᵉ e'ᵉ = is-prop-emptyᵉ eᵉ e'ᵉ
```