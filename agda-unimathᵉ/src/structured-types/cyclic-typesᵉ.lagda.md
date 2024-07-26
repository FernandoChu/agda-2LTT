# Cyclic types

```agda
module structured-types.cyclic-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphismsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.iterating-automorphismsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.sets-equipped-with-automorphismsᵉ
```

</details>

## Idea

Aᵉ **cyclicᵉ set**ᵉ consistsᵉ ofᵉ aᵉ [set](foundation.sets.mdᵉ) `A`ᵉ equippedᵉ with anᵉ
[automorphism](foundation.automorphisms.mdᵉ) `eᵉ : Aᵉ ≃ᵉ A`ᵉ whichᵉ isᵉ _cyclicᵉ_ in theᵉ
senseᵉ thatᵉ itsᵉ underlyingᵉ setᵉ isᵉ [inhabited](foundation.inhabited-types.mdᵉ) andᵉ
theᵉ mapᵉ

```text
  kᵉ ↦ᵉ eᵏᵉ xᵉ
```

isᵉ [surjective](foundation.surjective-maps.mdᵉ) forᵉ everyᵉ `xᵉ : A`.ᵉ Thereᵉ areᵉ
severalᵉ equivalentᵉ waysᵉ ofᵉ statingᵉ theᵉ conceptᵉ ofᵉ cyclicᵉ sets.ᵉ Twoᵉ furtherᵉ
equivalentᵉ waysᵉ areᵉ:

-ᵉ Aᵉ cyclicᵉ setᵉ isᵉ aᵉ
  [connectedᵉ setᵉ bundle](synthetic-homotopy-theory.connected-set-bundles-circle.mdᵉ)
  overᵉ theᵉ [circle](synthetic-homotopy-theory.circle.md).ᵉ
-ᵉ Aᵉ cyclicᵉ setᵉ isᵉ aᵉ setᵉ equippedᵉ with aᵉ
  [transitive](group-theory.transitive-group-actions.mdᵉ) `ℤ`-action.ᵉ
-ᵉ Aᵉ cyclicᵉ setᵉ isᵉ aᵉ setᵉ whichᵉ isᵉ aᵉ [`C`-torsor](group-theory.torsors.mdᵉ) forᵉ
  someᵉ [cyclicᵉ group](group-theory.cyclic-groups.mdᵉ) `C`.ᵉ

Noteᵉ thatᵉ theᵉ [emptyᵉ set](foundation.empty-types.mdᵉ) equippedᵉ with theᵉ identityᵉ
automorphismᵉ isᵉ notᵉ consideredᵉ to beᵉ aᵉ cyclicᵉ set,ᵉ forᵉ reasonsᵉ similarᵉ to thoseᵉ
ofᵉ notᵉ consideringᵉ emptyᵉ groupᵉ actionsᵉ to beᵉ transitive.ᵉ

## Definition

### The predicate of being a cyclic set

```agda
module _
  {lᵉ : Level} (Xᵉ : Set-With-Automorphismᵉ lᵉ)
  where

  is-cyclic-prop-Set-With-Automorphismᵉ : Propᵉ lᵉ
  is-cyclic-prop-Set-With-Automorphismᵉ =
    product-Propᵉ
      ( trunc-Propᵉ (type-Set-With-Automorphismᵉ Xᵉ))
      ( Π-Propᵉ
        ( type-Set-With-Automorphismᵉ Xᵉ)
        ( λ xᵉ →
          is-surjective-Propᵉ
            ( λ kᵉ →
              map-iterate-automorphism-ℤᵉ kᵉ (aut-Set-With-Automorphismᵉ Xᵉ) xᵉ)))

  is-cyclic-Set-With-Automorphismᵉ : UUᵉ lᵉ
  is-cyclic-Set-With-Automorphismᵉ =
    type-Propᵉ is-cyclic-prop-Set-With-Automorphismᵉ
```

### Cyclic sets

```agda
Cyclic-Setᵉ :
  (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Cyclic-Setᵉ lᵉ =
  Σᵉ (Set-With-Automorphismᵉ lᵉ) (λ Xᵉ → is-cyclic-Set-With-Automorphismᵉ Xᵉ)

module _
  {lᵉ : Level} (Xᵉ : Cyclic-Setᵉ lᵉ)
  where

  set-with-automorphism-Cyclic-Setᵉ : Set-With-Automorphismᵉ lᵉ
  set-with-automorphism-Cyclic-Setᵉ = pr1ᵉ Xᵉ

  set-Cyclic-Setᵉ : Setᵉ lᵉ
  set-Cyclic-Setᵉ = set-Set-With-Automorphismᵉ set-with-automorphism-Cyclic-Setᵉ

  type-Cyclic-Setᵉ : UUᵉ lᵉ
  type-Cyclic-Setᵉ = type-Set-With-Automorphismᵉ set-with-automorphism-Cyclic-Setᵉ

  is-set-type-Cyclic-Setᵉ : is-setᵉ type-Cyclic-Setᵉ
  is-set-type-Cyclic-Setᵉ =
    is-set-type-Set-With-Automorphismᵉ set-with-automorphism-Cyclic-Setᵉ

  aut-Cyclic-Setᵉ : Autᵉ type-Cyclic-Setᵉ
  aut-Cyclic-Setᵉ = aut-Set-With-Automorphismᵉ set-with-automorphism-Cyclic-Setᵉ

  map-Cyclic-Setᵉ : type-Cyclic-Setᵉ → type-Cyclic-Setᵉ
  map-Cyclic-Setᵉ = map-Set-With-Automorphismᵉ set-with-automorphism-Cyclic-Setᵉ
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}