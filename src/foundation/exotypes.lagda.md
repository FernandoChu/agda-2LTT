# Exotypes

```agda
module foundation.exotypes where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-subprecategoriesᵉ
open import category-theory.coslice-precategoriesᵉ
open import category-theory.opposite-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-typesᵉ
open import foundation.negation
open import foundation.logical-equivalences
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-types
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levelsᵉ
```

</details>

```agda
is-setᵉ-exotype : {l : Level} (X : UUᵉ l) → is-setᵉ X
pr1ᵉ (is-setᵉ-exotype X x .x reflᵉ reflᵉ) = reflᵉ
pr2ᵉ (is-setᵉ-exotype X x .x reflᵉ reflᵉ) reflᵉ = reflᵉ

exotype-Setᵉ : {l : Level} (X : UUᵉ l) → Setᵉ l
pr1ᵉ (exotype-Setᵉ X) = X
pr2ᵉ (exotype-Setᵉ X) = is-setᵉ-exotype X
```
