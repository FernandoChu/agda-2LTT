# Groups of loops in `1`-types

```agda
module synthetic-homotopy-theory.groups-of-loops-in-1-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.1-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.semigroupsᵉ

open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.loop-spacesᵉ
```

</details>

## Idea

Theᵉ [loopᵉ space](synthetic-homotopy-theory.loop-spaces.mdᵉ) ofᵉ anyᵉ
[pointed](structured-types.pointed-types.mdᵉ) [1-type](foundation.1-types.mdᵉ) isᵉ
aᵉ [group](group-theory.groups.md).ᵉ

## Definitions

```agda
module _
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ)
  where

  loop-space-Setᵉ : is-setᵉ (type-Ωᵉ Aᵉ) → Setᵉ lᵉ
  pr1ᵉ (loop-space-Setᵉ is-set-Ωᵉ) = type-Ωᵉ Aᵉ
  pr2ᵉ (loop-space-Setᵉ is-set-Ωᵉ) = is-set-Ωᵉ

  loop-space-Semigroupᵉ : is-setᵉ (type-Ωᵉ Aᵉ) → Semigroupᵉ lᵉ
  pr1ᵉ (loop-space-Semigroupᵉ is-set-Ωᵉ) = loop-space-Setᵉ is-set-Ωᵉ
  pr1ᵉ (pr2ᵉ (loop-space-Semigroupᵉ is-set-Ωᵉ)) pᵉ qᵉ = pᵉ ∙ᵉ qᵉ
  pr2ᵉ (pr2ᵉ (loop-space-Semigroupᵉ is-set-Ωᵉ)) = assocᵉ

  loop-space-Groupᵉ : is-setᵉ (type-Ωᵉ Aᵉ) → Groupᵉ lᵉ
  pr1ᵉ (loop-space-Groupᵉ is-set-Ωᵉ) = loop-space-Semigroupᵉ is-set-Ωᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ (loop-space-Groupᵉ is-set-Ωᵉ))) = reflᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (loop-space-Groupᵉ is-set-Ωᵉ)))) qᵉ = left-unitᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (loop-space-Groupᵉ is-set-Ωᵉ)))) pᵉ = right-unitᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (loop-space-Groupᵉ is-set-Ωᵉ))) = invᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (loop-space-Groupᵉ is-set-Ωᵉ)))) = left-invᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (loop-space-Groupᵉ is-set-Ωᵉ)))) = right-invᵉ

loop-space-1-type-Setᵉ :
  {lᵉ : Level} (Aᵉ : 1-Typeᵉ lᵉ) (aᵉ : type-1-Typeᵉ Aᵉ) → Setᵉ lᵉ
loop-space-1-type-Setᵉ Aᵉ aᵉ =
  loop-space-Setᵉ (pairᵉ (type-1-Typeᵉ Aᵉ) aᵉ) (is-1-type-type-1-Typeᵉ Aᵉ aᵉ aᵉ)

loop-space-1-type-Semigroupᵉ :
  {lᵉ : Level} (Aᵉ : 1-Typeᵉ lᵉ) (aᵉ : type-1-Typeᵉ Aᵉ) → Semigroupᵉ lᵉ
loop-space-1-type-Semigroupᵉ Aᵉ aᵉ =
  loop-space-Semigroupᵉ (pairᵉ (type-1-Typeᵉ Aᵉ) aᵉ) (is-1-type-type-1-Typeᵉ Aᵉ aᵉ aᵉ)

loop-space-1-type-Groupᵉ :
  {lᵉ : Level} (Aᵉ : 1-Typeᵉ lᵉ) (aᵉ : type-1-Typeᵉ Aᵉ) → Groupᵉ lᵉ
loop-space-1-type-Groupᵉ Aᵉ aᵉ =
  loop-space-Groupᵉ (pairᵉ (type-1-Typeᵉ Aᵉ) aᵉ) (is-1-type-type-1-Typeᵉ Aᵉ aᵉ aᵉ)
```