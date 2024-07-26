# Radicals of ideals of commutative rings

```agda
module commutative-algebra.radicals-of-ideals-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.binomial-theorem-commutative-ringsᵉ
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.ideals-commutative-ringsᵉ
open import commutative-algebra.poset-of-ideals-commutative-ringsᵉ
open import commutative-algebra.poset-of-radical-ideals-commutative-ringsᵉ
open import commutative-algebra.powers-of-elements-commutative-ringsᵉ
open import commutative-algebra.radical-ideals-commutative-ringsᵉ
open import commutative-algebra.subsets-commutative-ringsᵉ

open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.galois-connections-large-posetsᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
open import order-theory.order-preserving-maps-large-preordersᵉ
open import order-theory.reflective-galois-connections-large-posetsᵉ
```

</details>

## Idea

Theᵉ **radical**ᵉ `√ᵉ I`ᵉ ofᵉ anᵉ idealᵉ `I`ᵉ in aᵉ commutativeᵉ ringᵉ `A`ᵉ isᵉ theᵉ leastᵉ
[radicalᵉ ideal](commutative-algebra.radical-ideals-commutative-rings.mdᵉ) ofᵉ `A`ᵉ
containingᵉ `I`.ᵉ Theᵉ radicalᵉ `√ᵉ I`ᵉ isᵉ constructedᵉ asᵉ theᵉ idealᵉ consistingᵉ ofᵉ allᵉ
elementsᵉ `f`ᵉ forᵉ whichᵉ thereᵉ existsᵉ anᵉ `n`ᵉ suchᵉ thatᵉ `fⁿᵉ ∈ᵉ I`.ᵉ

Theᵉ operationᵉ `Iᵉ ↦ᵉ √ᵉ I`ᵉ isᵉ aᵉ
[reflectiveᵉ Galoisᵉ connection](order-theory.reflective-galois-connections-large-posets.mdᵉ)
fromᵉ theᵉ [largeᵉ poset](order-theory.large-posets.mdᵉ) ofᵉ
[ideals](commutative-algebra.ideals-commutative-rings.mdᵉ) in `A`ᵉ intoᵉ theᵉ largeᵉ
posetᵉ ofᵉ radicalᵉ idealsᵉ in `A`.ᵉ

## Definitions

### The condition of being the radical of an ideal

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  (Jᵉ : radical-ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  (Hᵉ :
    leq-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ))
  where

  is-radical-of-ideal-Commutative-Ringᵉ : UUωᵉ
  is-radical-of-ideal-Commutative-Ringᵉ =
    {l4ᵉ : Level} (Kᵉ : radical-ideal-Commutative-Ringᵉ l4ᵉ Aᵉ) →
    leq-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Kᵉ) →
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Kᵉ)
```

### The radical Galois connection on ideals of a commutative ring

#### The radical of an ideal

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  where

  subset-radical-of-ideal-Commutative-Ringᵉ : type-Commutative-Ringᵉ Aᵉ → Propᵉ l2ᵉ
  subset-radical-of-ideal-Commutative-Ringᵉ fᵉ =
    ∃ᵉ ℕᵉ (λ nᵉ → subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (power-Commutative-Ringᵉ Aᵉ nᵉ fᵉ))

  is-in-radical-of-ideal-Commutative-Ringᵉ : type-Commutative-Ringᵉ Aᵉ → UUᵉ l2ᵉ
  is-in-radical-of-ideal-Commutative-Ringᵉ =
    is-in-subtypeᵉ subset-radical-of-ideal-Commutative-Ringᵉ

  contains-ideal-radical-of-ideal-Commutative-Ringᵉ :
    (fᵉ : type-Commutative-Ringᵉ Aᵉ) →
    is-in-ideal-Commutative-Ringᵉ Aᵉ Iᵉ fᵉ →
    is-in-radical-of-ideal-Commutative-Ringᵉ fᵉ
  contains-ideal-radical-of-ideal-Commutative-Ringᵉ fᵉ Hᵉ = intro-existsᵉ 1 Hᵉ

  contains-zero-radical-of-ideal-Commutative-Ringᵉ :
    is-in-radical-of-ideal-Commutative-Ringᵉ (zero-Commutative-Ringᵉ Aᵉ)
  contains-zero-radical-of-ideal-Commutative-Ringᵉ =
    contains-ideal-radical-of-ideal-Commutative-Ringᵉ
      ( zero-Commutative-Ringᵉ Aᵉ)
      ( contains-zero-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)

  is-closed-under-addition-radical-of-ideal-Commutative-Ringᵉ :
    is-closed-under-addition-subset-Commutative-Ringᵉ Aᵉ
      ( subset-radical-of-ideal-Commutative-Ringᵉ)
  is-closed-under-addition-radical-of-ideal-Commutative-Ringᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( subset-radical-of-ideal-Commutative-Ringᵉ (add-Commutative-Ringᵉ Aᵉ xᵉ yᵉ))
      ( λ (nᵉ ,ᵉ pᵉ) →
        apply-universal-property-trunc-Propᵉ Kᵉ
          ( subset-radical-of-ideal-Commutative-Ringᵉ
            ( add-Commutative-Ringᵉ Aᵉ xᵉ yᵉ))
          ( λ (mᵉ ,ᵉ qᵉ) →
            intro-existsᵉ
              ( nᵉ +ℕᵉ mᵉ)
              ( is-closed-under-eq-ideal-Commutative-Ring'ᵉ Aᵉ Iᵉ
                ( is-closed-under-addition-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
                  ( is-closed-under-right-multiplication-ideal-Commutative-Ringᵉ
                    ( Aᵉ)
                    ( Iᵉ)
                    ( _)
                    ( _)
                    ( qᵉ))
                  ( is-closed-under-right-multiplication-ideal-Commutative-Ringᵉ
                    ( Aᵉ)
                    ( Iᵉ)
                    ( _)
                    ( _)
                    ( pᵉ)))
                ( is-linear-combination-power-add-Commutative-Ringᵉ Aᵉ nᵉ mᵉ xᵉ yᵉ))))

  is-closed-under-negatives-radical-of-ideal-Commutative-Ringᵉ :
    is-closed-under-negatives-subset-Commutative-Ringᵉ Aᵉ
      ( subset-radical-of-ideal-Commutative-Ringᵉ)
  is-closed-under-negatives-radical-of-ideal-Commutative-Ringᵉ {xᵉ} Hᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( subset-radical-of-ideal-Commutative-Ringᵉ (neg-Commutative-Ringᵉ Aᵉ xᵉ))
      ( λ (nᵉ ,ᵉ pᵉ) →
        intro-existsᵉ nᵉ
          ( is-closed-under-eq-ideal-Commutative-Ring'ᵉ Aᵉ Iᵉ
            ( is-closed-under-left-multiplication-ideal-Commutative-Ringᵉ Aᵉ Iᵉ _
              ( power-Commutative-Ringᵉ Aᵉ nᵉ xᵉ)
              ( pᵉ))
            ( power-neg-Commutative-Ringᵉ Aᵉ nᵉ xᵉ)))

  is-closed-under-right-multiplication-radical-of-ideal-Commutative-Ringᵉ :
    is-closed-under-right-multiplication-subset-Commutative-Ringᵉ Aᵉ
      ( subset-radical-of-ideal-Commutative-Ringᵉ)
  is-closed-under-right-multiplication-radical-of-ideal-Commutative-Ringᵉ xᵉ yᵉ Hᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( subset-radical-of-ideal-Commutative-Ringᵉ (mul-Commutative-Ringᵉ Aᵉ xᵉ yᵉ))
      ( λ (nᵉ ,ᵉ pᵉ) →
        intro-existsᵉ nᵉ
          ( is-closed-under-eq-ideal-Commutative-Ring'ᵉ Aᵉ Iᵉ
            ( is-closed-under-right-multiplication-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
              ( power-Commutative-Ringᵉ Aᵉ nᵉ xᵉ)
              ( power-Commutative-Ringᵉ Aᵉ nᵉ yᵉ)
              ( pᵉ))
            ( distributive-power-mul-Commutative-Ringᵉ Aᵉ nᵉ xᵉ yᵉ)))

  is-closed-under-left-multiplication-radical-of-ideal-Commutative-Ringᵉ :
    is-closed-under-left-multiplication-subset-Commutative-Ringᵉ Aᵉ
      ( subset-radical-of-ideal-Commutative-Ringᵉ)
  is-closed-under-left-multiplication-radical-of-ideal-Commutative-Ringᵉ xᵉ yᵉ Hᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( subset-radical-of-ideal-Commutative-Ringᵉ (mul-Commutative-Ringᵉ Aᵉ xᵉ yᵉ))
      ( λ (nᵉ ,ᵉ pᵉ) →
        intro-existsᵉ nᵉ
          ( is-closed-under-eq-ideal-Commutative-Ring'ᵉ Aᵉ Iᵉ
            ( is-closed-under-left-multiplication-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
              ( power-Commutative-Ringᵉ Aᵉ nᵉ xᵉ)
              ( power-Commutative-Ringᵉ Aᵉ nᵉ yᵉ)
              ( pᵉ))
            ( distributive-power-mul-Commutative-Ringᵉ Aᵉ nᵉ xᵉ yᵉ)))

  ideal-radical-of-ideal-Commutative-Ringᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ
  ideal-radical-of-ideal-Commutative-Ringᵉ =
    ideal-right-ideal-Commutative-Ringᵉ Aᵉ
      subset-radical-of-ideal-Commutative-Ringᵉ
      contains-zero-radical-of-ideal-Commutative-Ringᵉ
      is-closed-under-addition-radical-of-ideal-Commutative-Ringᵉ
      is-closed-under-negatives-radical-of-ideal-Commutative-Ringᵉ
      is-closed-under-right-multiplication-radical-of-ideal-Commutative-Ringᵉ

  is-radical-radical-of-ideal-Commutative-Ringᵉ :
    is-radical-ideal-Commutative-Ringᵉ Aᵉ ideal-radical-of-ideal-Commutative-Ringᵉ
  is-radical-radical-of-ideal-Commutative-Ringᵉ xᵉ nᵉ Hᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( subset-radical-of-ideal-Commutative-Ringᵉ xᵉ)
      ( λ (mᵉ ,ᵉ Kᵉ) →
        intro-existsᵉ
          ( mul-ℕᵉ nᵉ mᵉ)
          ( is-closed-under-eq-ideal-Commutative-Ring'ᵉ Aᵉ Iᵉ Kᵉ
            ( power-mul-Commutative-Ringᵉ Aᵉ nᵉ mᵉ)))

  radical-of-ideal-Commutative-Ringᵉ :
    radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ
  pr1ᵉ radical-of-ideal-Commutative-Ringᵉ =
    ideal-radical-of-ideal-Commutative-Ringᵉ
  pr2ᵉ radical-of-ideal-Commutative-Ringᵉ =
    is-radical-radical-of-ideal-Commutative-Ringᵉ

  is-radical-of-ideal-radical-of-ideal-Commutative-Ringᵉ :
    is-radical-of-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
      ( radical-of-ideal-Commutative-Ringᵉ)
      ( contains-ideal-radical-of-ideal-Commutative-Ringᵉ)
  is-radical-of-ideal-radical-of-ideal-Commutative-Ringᵉ Jᵉ Hᵉ xᵉ Kᵉ =
    apply-universal-property-trunc-Propᵉ Kᵉ
      ( subset-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ xᵉ)
      ( λ (nᵉ ,ᵉ Lᵉ) →
        is-radical-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ xᵉ nᵉ
          ( Hᵉ (power-Commutative-Ringᵉ Aᵉ nᵉ xᵉ) Lᵉ))
```

#### The operation `I ↦ √ I` as an order preserving map

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  where

  preserves-order-radical-of-ideal-Commutative-Ringᵉ :
    {l2ᵉ l3ᵉ : Level}
    (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) (Jᵉ : ideal-Commutative-Ringᵉ l3ᵉ Aᵉ) →
    leq-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ →
    leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( radical-of-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
  preserves-order-radical-of-ideal-Commutative-Ringᵉ Iᵉ Jᵉ Hᵉ =
    is-radical-of-ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
      ( radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
      ( transitive-leq-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ
        ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
        ( contains-ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
        ( Hᵉ))

  radical-of-ideal-hom-large-poset-Commutative-Ringᵉ :
    hom-Large-Posetᵉ
      ( λ lᵉ → lᵉ)
      ( ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
      ( radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
  map-hom-Large-Preorderᵉ
    radical-of-ideal-hom-large-poset-Commutative-Ringᵉ =
    radical-of-ideal-Commutative-Ringᵉ Aᵉ
  preserves-order-hom-Large-Preorderᵉ
    radical-of-ideal-hom-large-poset-Commutative-Ringᵉ =
    preserves-order-radical-of-ideal-Commutative-Ringᵉ
```

#### The radical Galois connection

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  where

  adjoint-relation-radical-of-ideal-Commutative-Ringᵉ :
    {l2ᵉ l3ᵉ : Level}
    (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
    (Jᵉ : radical-ideal-Commutative-Ringᵉ l3ᵉ Aᵉ) →
    leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( radical-of-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( Jᵉ) ↔ᵉ
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( Iᵉ)
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
  pr1ᵉ (adjoint-relation-radical-of-ideal-Commutative-Ringᵉ Iᵉ Jᵉ) Hᵉ =
    transitive-leq-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
      ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
      ( Hᵉ)
      ( contains-ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
  pr2ᵉ (adjoint-relation-radical-of-ideal-Commutative-Ringᵉ Iᵉ Jᵉ) =
    is-radical-of-ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ

  radical-of-ideal-galois-connection-Commutative-Ringᵉ :
    galois-connection-Large-Posetᵉ (λ lᵉ → lᵉ) (λ lᵉ → lᵉ)
      ( ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
      ( radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
  lower-adjoint-galois-connection-Large-Posetᵉ
    radical-of-ideal-galois-connection-Commutative-Ringᵉ =
    radical-of-ideal-hom-large-poset-Commutative-Ringᵉ Aᵉ
  upper-adjoint-galois-connection-Large-Posetᵉ
    radical-of-ideal-galois-connection-Commutative-Ringᵉ =
    ideal-radical-ideal-hom-large-poset-Commutative-Ringᵉ Aᵉ
  adjoint-relation-galois-connection-Large-Posetᵉ
    radical-of-ideal-galois-connection-Commutative-Ringᵉ =
    adjoint-relation-radical-of-ideal-Commutative-Ringᵉ
```

#### The radical reflective Galois connection

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  where

  is-reflective-radical-of-ideal-Commutative-Ringᵉ :
    is-reflective-galois-connection-Large-Posetᵉ
      ( ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
      ( radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
      ( radical-of-ideal-galois-connection-Commutative-Ringᵉ Aᵉ)
  pr1ᵉ (is-reflective-radical-of-ideal-Commutative-Ringᵉ Iᵉ) =
    is-radical-of-ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( Iᵉ)
      ( refl-leq-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
  pr2ᵉ (is-reflective-radical-of-ideal-Commutative-Ringᵉ Iᵉ) =
    contains-ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)

  radical-of-ideal-reflective-galois-connection-Commutative-Ringᵉ :
    reflective-galois-connection-Large-Posetᵉ
      ( ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
      ( radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
  galois-connection-reflective-galois-connection-Large-Posetᵉ
    radical-of-ideal-reflective-galois-connection-Commutative-Ringᵉ =
    radical-of-ideal-galois-connection-Commutative-Ringᵉ Aᵉ
  is-reflective-reflective-galois-connection-Large-Posetᵉ
    radical-of-ideal-reflective-galois-connection-Commutative-Ringᵉ =
    is-reflective-radical-of-ideal-Commutative-Ringᵉ
```