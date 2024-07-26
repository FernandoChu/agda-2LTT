# Iterating automorphisms

```agda
module foundation.iterating-automorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.automorphismsᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.iterating-functionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.coproduct-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
```

</details>

## Definition

### Iterating automorphisms

#### Iterating by postcomposition using a natural number

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  iterate-automorphism-ℕᵉ : ℕᵉ → Autᵉ Xᵉ → Autᵉ Xᵉ
  iterate-automorphism-ℕᵉ zero-ℕᵉ eᵉ = id-equivᵉ
  iterate-automorphism-ℕᵉ (succ-ℕᵉ nᵉ) eᵉ = eᵉ ∘eᵉ (iterate-automorphism-ℕᵉ nᵉ eᵉ)

  map-iterate-automorphismᵉ : ℕᵉ → Autᵉ Xᵉ → Xᵉ → Xᵉ
  map-iterate-automorphismᵉ nᵉ eᵉ = map-equivᵉ (iterate-automorphism-ℕᵉ nᵉ eᵉ)

  is-equiv-map-iterate-automorphismᵉ :
    (nᵉ : ℕᵉ) (eᵉ : Autᵉ Xᵉ) → is-equivᵉ (map-iterate-automorphismᵉ nᵉ eᵉ)
  is-equiv-map-iterate-automorphismᵉ nᵉ eᵉ =
    is-equiv-map-equivᵉ (iterate-automorphism-ℕᵉ nᵉ eᵉ)

  compute-map-iterate-automorphismᵉ :
    (nᵉ : ℕᵉ) (eᵉ : Autᵉ Xᵉ) → map-iterate-automorphismᵉ nᵉ eᵉ ~ᵉ iterateᵉ nᵉ (map-equivᵉ eᵉ)
  compute-map-iterate-automorphismᵉ zero-ℕᵉ eᵉ = refl-htpyᵉ
  compute-map-iterate-automorphismᵉ (succ-ℕᵉ nᵉ) eᵉ =
    map-equivᵉ eᵉ ·lᵉ (compute-map-iterate-automorphismᵉ nᵉ eᵉ)
```

#### Iterating by precomposition using a natural number

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  iterate-automorphism-ℕ'ᵉ : ℕᵉ → Autᵉ Xᵉ → Autᵉ Xᵉ
  iterate-automorphism-ℕ'ᵉ zero-ℕᵉ eᵉ = id-equivᵉ
  iterate-automorphism-ℕ'ᵉ (succ-ℕᵉ nᵉ) eᵉ = iterate-automorphism-ℕ'ᵉ nᵉ eᵉ ∘eᵉ eᵉ

  map-iterate-automorphism-ℕ'ᵉ : ℕᵉ → Autᵉ Xᵉ → Xᵉ → Xᵉ
  map-iterate-automorphism-ℕ'ᵉ nᵉ eᵉ = map-equivᵉ (iterate-automorphism-ℕ'ᵉ nᵉ eᵉ)

  is-equiv-map-iterate-automorphism-ℕ'ᵉ :
    (nᵉ : ℕᵉ) (eᵉ : Autᵉ Xᵉ) → is-equivᵉ (map-iterate-automorphism-ℕ'ᵉ nᵉ eᵉ)
  is-equiv-map-iterate-automorphism-ℕ'ᵉ nᵉ eᵉ =
    is-equiv-map-equivᵉ (iterate-automorphism-ℕ'ᵉ nᵉ eᵉ)

  compute-map-iterate-automorphism-ℕ'ᵉ :
    (nᵉ : ℕᵉ) (eᵉ : Autᵉ Xᵉ) →
    map-iterate-automorphism-ℕ'ᵉ nᵉ eᵉ ~ᵉ iterate'ᵉ nᵉ (map-equivᵉ eᵉ)
  compute-map-iterate-automorphism-ℕ'ᵉ zero-ℕᵉ eᵉ = refl-htpyᵉ
  compute-map-iterate-automorphism-ℕ'ᵉ (succ-ℕᵉ nᵉ) eᵉ =
    (compute-map-iterate-automorphism-ℕ'ᵉ nᵉ eᵉ ·rᵉ (map-equivᵉ eᵉ))
```

#### Iterating by postcomposition using an integer

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  iterate-automorphism-ℤᵉ : ℤᵉ → Autᵉ Xᵉ → Autᵉ Xᵉ
  iterate-automorphism-ℤᵉ (inlᵉ zero-ℕᵉ) eᵉ = inv-equivᵉ eᵉ
  iterate-automorphism-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) eᵉ =
    inv-equivᵉ eᵉ ∘eᵉ (iterate-automorphism-ℤᵉ (inlᵉ xᵉ) eᵉ)
  iterate-automorphism-ℤᵉ (inrᵉ (inlᵉ _)) eᵉ = id-equivᵉ
  iterate-automorphism-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) eᵉ = eᵉ
  iterate-automorphism-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) eᵉ =
    eᵉ ∘eᵉ (iterate-automorphism-ℤᵉ (inrᵉ (inrᵉ xᵉ)) eᵉ)

  map-iterate-automorphism-ℤᵉ : ℤᵉ → Autᵉ Xᵉ → Xᵉ → Xᵉ
  map-iterate-automorphism-ℤᵉ kᵉ eᵉ = map-equivᵉ (iterate-automorphism-ℤᵉ kᵉ eᵉ)

  is-equiv-map-iterate-automorphism-ℤᵉ :
    (kᵉ : ℤᵉ) (eᵉ : Autᵉ Xᵉ) → is-equivᵉ (map-iterate-automorphism-ℤᵉ kᵉ eᵉ)
  is-equiv-map-iterate-automorphism-ℤᵉ kᵉ eᵉ =
    is-equiv-map-equivᵉ (iterate-automorphism-ℤᵉ kᵉ eᵉ)

  map-inv-iterate-automorphism-ℤᵉ : ℤᵉ → Autᵉ Xᵉ → Xᵉ → Xᵉ
  map-inv-iterate-automorphism-ℤᵉ kᵉ eᵉ =
    map-inv-equivᵉ (iterate-automorphism-ℤᵉ kᵉ eᵉ)

  is-section-map-inv-iterate-automorphism-ℤᵉ :
    (kᵉ : ℤᵉ) (eᵉ : Autᵉ Xᵉ) →
    (map-iterate-automorphism-ℤᵉ kᵉ eᵉ ∘ᵉ map-inv-iterate-automorphism-ℤᵉ kᵉ eᵉ) ~ᵉ idᵉ
  is-section-map-inv-iterate-automorphism-ℤᵉ kᵉ eᵉ =
    is-section-map-inv-equivᵉ (iterate-automorphism-ℤᵉ kᵉ eᵉ)

  is-retraction-map-inv-iterate-automorphism-ℤᵉ :
    (kᵉ : ℤᵉ) (eᵉ : Autᵉ Xᵉ) →
    (map-inv-iterate-automorphism-ℤᵉ kᵉ eᵉ ∘ᵉ map-iterate-automorphism-ℤᵉ kᵉ eᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-iterate-automorphism-ℤᵉ kᵉ eᵉ =
    is-retraction-map-inv-equivᵉ (iterate-automorphism-ℤᵉ kᵉ eᵉ)
```

#### Iterating by precomposition using an integer

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  iterate-automorphism-ℤ'ᵉ : ℤᵉ → Autᵉ Xᵉ → Autᵉ Xᵉ
  iterate-automorphism-ℤ'ᵉ (inlᵉ zero-ℕᵉ) eᵉ = inv-equivᵉ eᵉ
  iterate-automorphism-ℤ'ᵉ (inlᵉ (succ-ℕᵉ xᵉ)) eᵉ =
    iterate-automorphism-ℤ'ᵉ (inlᵉ xᵉ) eᵉ ∘eᵉ inv-equivᵉ eᵉ
  iterate-automorphism-ℤ'ᵉ (inrᵉ (inlᵉ _)) eᵉ = id-equivᵉ
  iterate-automorphism-ℤ'ᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) eᵉ = eᵉ
  iterate-automorphism-ℤ'ᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) eᵉ =
    iterate-automorphism-ℤ'ᵉ (inrᵉ (inrᵉ xᵉ)) eᵉ ∘eᵉ eᵉ
```

## Properties

### Iterating an automorphism by a natural number `n` is the same as iterating it by the integer `int-ℕ n`

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  iterate-automorphism-int-ℕᵉ :
    (nᵉ : ℕᵉ) (eᵉ : Autᵉ Xᵉ) →
    htpy-equivᵉ (iterate-automorphism-ℕᵉ nᵉ eᵉ) (iterate-automorphism-ℤᵉ (int-ℕᵉ nᵉ) eᵉ)
  iterate-automorphism-int-ℕᵉ zero-ℕᵉ eᵉ = refl-htpyᵉ
  iterate-automorphism-int-ℕᵉ (succ-ℕᵉ zero-ℕᵉ) eᵉ = refl-htpyᵉ
  iterate-automorphism-int-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) eᵉ =
    map-equivᵉ eᵉ ·lᵉ (iterate-automorphism-int-ℕᵉ (succ-ℕᵉ nᵉ) eᵉ)
```

### Iterating by postcomposition is homotopic to iterating by precomposition

#### For the natural numbers

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  iterate-automorphism-succ-ℕᵉ :
    (nᵉ : ℕᵉ) (eᵉ : Autᵉ Xᵉ) →
    htpy-equivᵉ
      ( iterate-automorphism-ℕᵉ (succ-ℕᵉ nᵉ) eᵉ)
      ( iterate-automorphism-ℕᵉ nᵉ eᵉ ∘eᵉ eᵉ)
  iterate-automorphism-succ-ℕᵉ zero-ℕᵉ eᵉ = refl-htpyᵉ
  iterate-automorphism-succ-ℕᵉ (succ-ℕᵉ nᵉ) eᵉ =
    map-equivᵉ eᵉ ·lᵉ (iterate-automorphism-succ-ℕᵉ nᵉ eᵉ)

  reassociate-iterate-automorphism-ℕᵉ :
    (nᵉ : ℕᵉ) (eᵉ : Autᵉ Xᵉ) →
    htpy-equivᵉ (iterate-automorphism-ℕᵉ nᵉ eᵉ) (iterate-automorphism-ℕ'ᵉ nᵉ eᵉ)
  reassociate-iterate-automorphism-ℕᵉ zero-ℕᵉ eᵉ = refl-htpyᵉ
  reassociate-iterate-automorphism-ℕᵉ (succ-ℕᵉ nᵉ) eᵉ =
    ( iterate-automorphism-succ-ℕᵉ nᵉ eᵉ) ∙hᵉ
    ( reassociate-iterate-automorphism-ℕᵉ nᵉ eᵉ ·rᵉ map-equivᵉ eᵉ)
```

#### For the integers

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  iterate-automorphism-succ-ℤᵉ :
    (kᵉ : ℤᵉ) (eᵉ : Autᵉ Xᵉ) →
    htpy-equivᵉ
      ( iterate-automorphism-ℤᵉ (succ-ℤᵉ kᵉ) eᵉ)
      ( iterate-automorphism-ℤᵉ kᵉ eᵉ ∘eᵉ eᵉ)
  iterate-automorphism-succ-ℤᵉ (inlᵉ zero-ℕᵉ) eᵉ =
    inv-htpyᵉ (is-retraction-map-inv-equivᵉ eᵉ)
  iterate-automorphism-succ-ℤᵉ (inlᵉ (succ-ℕᵉ zero-ℕᵉ)) eᵉ =
    inv-htpyᵉ (map-inv-equivᵉ eᵉ ·lᵉ is-retraction-map-inv-equivᵉ eᵉ)
  iterate-automorphism-succ-ℤᵉ (inlᵉ (succ-ℕᵉ (succ-ℕᵉ xᵉ))) eᵉ =
    map-inv-equivᵉ eᵉ ·lᵉ iterate-automorphism-succ-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) eᵉ
  iterate-automorphism-succ-ℤᵉ (inrᵉ (inlᵉ _)) eᵉ = refl-htpyᵉ
  iterate-automorphism-succ-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) eᵉ = refl-htpyᵉ
  iterate-automorphism-succ-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) eᵉ =
    map-equivᵉ eᵉ ·lᵉ iterate-automorphism-succ-ℤᵉ (inrᵉ (inrᵉ xᵉ)) eᵉ

  iterate-automorphism-succ-ℤ'ᵉ :
    (kᵉ : ℤᵉ) (eᵉ : Autᵉ Xᵉ) →
    htpy-equivᵉ
      ( iterate-automorphism-ℤᵉ (succ-ℤᵉ kᵉ) eᵉ)
      ( eᵉ ∘eᵉ iterate-automorphism-ℤᵉ kᵉ eᵉ)
  iterate-automorphism-succ-ℤ'ᵉ (inlᵉ zero-ℕᵉ) eᵉ =
    inv-htpyᵉ (is-section-map-inv-equivᵉ eᵉ)
  iterate-automorphism-succ-ℤ'ᵉ (inlᵉ (succ-ℕᵉ xᵉ)) eᵉ =
    ( inv-htpyᵉ (is-section-map-inv-equivᵉ eᵉ)) ·rᵉ
    ( map-iterate-automorphism-ℤᵉ (inlᵉ xᵉ) eᵉ)
  iterate-automorphism-succ-ℤ'ᵉ (inrᵉ (inlᵉ _)) eᵉ = refl-htpyᵉ
  iterate-automorphism-succ-ℤ'ᵉ (inrᵉ (inrᵉ xᵉ)) eᵉ = refl-htpyᵉ

  iterate-automorphism-pred-ℤᵉ :
    (kᵉ : ℤᵉ) (eᵉ : Autᵉ Xᵉ) →
    htpy-equivᵉ
      ( iterate-automorphism-ℤᵉ (pred-ℤᵉ kᵉ) eᵉ)
      ( iterate-automorphism-ℤᵉ kᵉ eᵉ ∘eᵉ inv-equivᵉ eᵉ)
  iterate-automorphism-pred-ℤᵉ (inlᵉ zero-ℕᵉ) eᵉ = refl-htpyᵉ
  iterate-automorphism-pred-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) eᵉ =
    map-inv-equivᵉ eᵉ ·lᵉ iterate-automorphism-pred-ℤᵉ (inlᵉ xᵉ) eᵉ
  iterate-automorphism-pred-ℤᵉ (inrᵉ (inlᵉ _)) eᵉ = refl-htpyᵉ
  iterate-automorphism-pred-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) eᵉ =
    inv-htpyᵉ (is-section-map-inv-equivᵉ eᵉ)
  iterate-automorphism-pred-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ zero-ℕᵉ))) eᵉ =
    inv-htpyᵉ (map-equivᵉ eᵉ ·lᵉ is-section-map-inv-equivᵉ eᵉ)
  iterate-automorphism-pred-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ (succ-ℕᵉ xᵉ)))) eᵉ =
    map-equivᵉ eᵉ ·lᵉ iterate-automorphism-pred-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) eᵉ

  iterate-automorphism-pred-ℤ'ᵉ :
    (kᵉ : ℤᵉ) (eᵉ : Autᵉ Xᵉ) →
    htpy-equivᵉ
      ( iterate-automorphism-ℤᵉ (pred-ℤᵉ kᵉ) eᵉ)
      ( inv-equivᵉ eᵉ ∘eᵉ iterate-automorphism-ℤᵉ kᵉ eᵉ)
  iterate-automorphism-pred-ℤ'ᵉ (inlᵉ zero-ℕᵉ) eᵉ = refl-htpyᵉ
  iterate-automorphism-pred-ℤ'ᵉ (inlᵉ (succ-ℕᵉ xᵉ)) eᵉ = refl-htpyᵉ
  iterate-automorphism-pred-ℤ'ᵉ (inrᵉ (inlᵉ _)) eᵉ = refl-htpyᵉ
  iterate-automorphism-pred-ℤ'ᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) eᵉ =
    inv-htpyᵉ (is-retraction-map-inv-equivᵉ eᵉ)
  iterate-automorphism-pred-ℤ'ᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) eᵉ =
    ( inv-htpyᵉ (is-retraction-map-inv-equivᵉ eᵉ)) ·rᵉ
    ( map-equivᵉ (iterate-automorphism-ℤᵉ (inrᵉ (inrᵉ xᵉ)) eᵉ))

  reassociate-iterate-automorphism-ℤᵉ :
    (kᵉ : ℤᵉ) (eᵉ : Autᵉ Xᵉ) →
    htpy-equivᵉ (iterate-automorphism-ℤᵉ kᵉ eᵉ) (iterate-automorphism-ℤ'ᵉ kᵉ eᵉ)
  reassociate-iterate-automorphism-ℤᵉ (inlᵉ zero-ℕᵉ) eᵉ = refl-htpyᵉ
  reassociate-iterate-automorphism-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) eᵉ =
    ( iterate-automorphism-pred-ℤᵉ (inlᵉ xᵉ) eᵉ) ∙hᵉ
    ( reassociate-iterate-automorphism-ℤᵉ (inlᵉ xᵉ) eᵉ ·rᵉ map-inv-equivᵉ eᵉ)
  reassociate-iterate-automorphism-ℤᵉ (inrᵉ (inlᵉ _)) eᵉ = refl-htpyᵉ
  reassociate-iterate-automorphism-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) eᵉ = refl-htpyᵉ
  reassociate-iterate-automorphism-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) eᵉ =
    ( iterate-automorphism-succ-ℤᵉ (inrᵉ (inrᵉ xᵉ)) eᵉ) ∙hᵉ
    ( reassociate-iterate-automorphism-ℤᵉ (inrᵉ (inrᵉ xᵉ)) eᵉ ·rᵉ map-equivᵉ eᵉ)
```

### Iterating an automorphism `k+l` times

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  iterate-automorphism-add-ℤᵉ :
    (kᵉ lᵉ : ℤᵉ) (eᵉ : Autᵉ Xᵉ) →
    htpy-equivᵉ
      ( iterate-automorphism-ℤᵉ (kᵉ +ℤᵉ lᵉ) eᵉ)
      ( iterate-automorphism-ℤᵉ kᵉ eᵉ ∘eᵉ iterate-automorphism-ℤᵉ lᵉ eᵉ)
  iterate-automorphism-add-ℤᵉ (inlᵉ zero-ℕᵉ) lᵉ eᵉ = iterate-automorphism-pred-ℤ'ᵉ lᵉ eᵉ
  iterate-automorphism-add-ℤᵉ (inlᵉ (succ-ℕᵉ kᵉ)) lᵉ eᵉ =
    ( iterate-automorphism-pred-ℤ'ᵉ ((inlᵉ kᵉ) +ℤᵉ lᵉ) eᵉ) ∙hᵉ
    ( map-inv-equivᵉ eᵉ ·lᵉ iterate-automorphism-add-ℤᵉ (inlᵉ kᵉ) lᵉ eᵉ)
  iterate-automorphism-add-ℤᵉ (inrᵉ (inlᵉ _)) lᵉ eᵉ = refl-htpyᵉ
  iterate-automorphism-add-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) lᵉ eᵉ =
    iterate-automorphism-succ-ℤ'ᵉ lᵉ eᵉ
  iterate-automorphism-add-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) lᵉ eᵉ =
    ( iterate-automorphism-succ-ℤ'ᵉ ((inrᵉ (inrᵉ xᵉ)) +ℤᵉ lᵉ) eᵉ) ∙hᵉ
    ( map-equivᵉ eᵉ ·lᵉ iterate-automorphism-add-ℤᵉ (inrᵉ (inrᵉ xᵉ)) lᵉ eᵉ)
```