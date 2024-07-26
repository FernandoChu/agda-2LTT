# Polynomial endofunctors

```agda
module trees.polynomial-endofunctorsᵉ where
```

<details><summary>Imports</summary>

```agda
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
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Givenᵉ aᵉ typeᵉ `A`ᵉ equippedᵉ with aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`,ᵉ theᵉ **polynomialᵉ
endofunctor**ᵉ `Pᵉ Aᵉ B`ᵉ isᵉ definedᵉ byᵉ

```text
  Xᵉ ↦ᵉ Σᵉ (xᵉ : A),ᵉ (Bᵉ xᵉ → Xᵉ)
```

Polynomialᵉ endofunctorsᵉ areᵉ importantᵉ in theᵉ studyᵉ ofᵉ W-types,ᵉ andᵉ alsoᵉ in theᵉ
studyᵉ ofᵉ combinatorialᵉ species.ᵉ

## Definitions

### The action on types of a polynomial endofunctor

```agda
type-polynomial-endofunctorᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Xᵉ : UUᵉ l3ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
type-polynomial-endofunctorᵉ Aᵉ Bᵉ Xᵉ = Σᵉ Aᵉ (λ xᵉ → Bᵉ xᵉ → Xᵉ)
```

### The identity type of `type-polynomial-endofunctor`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  where

  Eq-type-polynomial-endofunctorᵉ :
    (xᵉ yᵉ : type-polynomial-endofunctorᵉ Aᵉ Bᵉ Xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  Eq-type-polynomial-endofunctorᵉ xᵉ yᵉ =
    Σᵉ (pr1ᵉ xᵉ ＝ᵉ pr1ᵉ yᵉ) (λ pᵉ → (pr2ᵉ xᵉ) ~ᵉ ((pr2ᵉ yᵉ) ∘ᵉ (trᵉ Bᵉ pᵉ)))

  refl-Eq-type-polynomial-endofunctorᵉ :
    (xᵉ : type-polynomial-endofunctorᵉ Aᵉ Bᵉ Xᵉ) →
    Eq-type-polynomial-endofunctorᵉ xᵉ xᵉ
  refl-Eq-type-polynomial-endofunctorᵉ (pairᵉ xᵉ αᵉ) = pairᵉ reflᵉ refl-htpyᵉ

  is-torsorial-Eq-type-polynomial-endofunctorᵉ :
    (xᵉ : type-polynomial-endofunctorᵉ Aᵉ Bᵉ Xᵉ) →
    is-torsorialᵉ (Eq-type-polynomial-endofunctorᵉ xᵉ)
  is-torsorial-Eq-type-polynomial-endofunctorᵉ (pairᵉ xᵉ αᵉ) =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-Idᵉ xᵉ)
      ( pairᵉ xᵉ reflᵉ)
      ( is-torsorial-htpyᵉ αᵉ)

  Eq-type-polynomial-endofunctor-eqᵉ :
    (xᵉ yᵉ : type-polynomial-endofunctorᵉ Aᵉ Bᵉ Xᵉ) →
    xᵉ ＝ᵉ yᵉ → Eq-type-polynomial-endofunctorᵉ xᵉ yᵉ
  Eq-type-polynomial-endofunctor-eqᵉ xᵉ .xᵉ reflᵉ =
    refl-Eq-type-polynomial-endofunctorᵉ xᵉ

  is-equiv-Eq-type-polynomial-endofunctor-eqᵉ :
    (xᵉ yᵉ : type-polynomial-endofunctorᵉ Aᵉ Bᵉ Xᵉ) →
    is-equivᵉ (Eq-type-polynomial-endofunctor-eqᵉ xᵉ yᵉ)
  is-equiv-Eq-type-polynomial-endofunctor-eqᵉ xᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-Eq-type-polynomial-endofunctorᵉ xᵉ)
      ( Eq-type-polynomial-endofunctor-eqᵉ xᵉ)

  eq-Eq-type-polynomial-endofunctorᵉ :
    (xᵉ yᵉ : type-polynomial-endofunctorᵉ Aᵉ Bᵉ Xᵉ) →
    Eq-type-polynomial-endofunctorᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  eq-Eq-type-polynomial-endofunctorᵉ xᵉ yᵉ =
    map-inv-is-equivᵉ (is-equiv-Eq-type-polynomial-endofunctor-eqᵉ xᵉ yᵉ)

  is-retraction-eq-Eq-type-polynomial-endofunctorᵉ :
    (xᵉ yᵉ : type-polynomial-endofunctorᵉ Aᵉ Bᵉ Xᵉ) →
    ( ( eq-Eq-type-polynomial-endofunctorᵉ xᵉ yᵉ) ∘ᵉ
      ( Eq-type-polynomial-endofunctor-eqᵉ xᵉ yᵉ)) ~ᵉ idᵉ
  is-retraction-eq-Eq-type-polynomial-endofunctorᵉ xᵉ yᵉ =
    is-retraction-map-inv-is-equivᵉ
      ( is-equiv-Eq-type-polynomial-endofunctor-eqᵉ xᵉ yᵉ)

  coh-refl-eq-Eq-type-polynomial-endofunctorᵉ :
    (xᵉ : type-polynomial-endofunctorᵉ Aᵉ Bᵉ Xᵉ) →
    ( eq-Eq-type-polynomial-endofunctorᵉ xᵉ xᵉ
      ( refl-Eq-type-polynomial-endofunctorᵉ xᵉ)) ＝ᵉ reflᵉ
  coh-refl-eq-Eq-type-polynomial-endofunctorᵉ xᵉ =
    is-retraction-eq-Eq-type-polynomial-endofunctorᵉ xᵉ xᵉ reflᵉ
```

### The action on morphisms of the polynomial endofunctor

```agda
map-polynomial-endofunctorᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Xᵉ → Yᵉ) →
  type-polynomial-endofunctorᵉ Aᵉ Bᵉ Xᵉ → type-polynomial-endofunctorᵉ Aᵉ Bᵉ Yᵉ
map-polynomial-endofunctorᵉ Aᵉ Bᵉ fᵉ = totᵉ (λ xᵉ αᵉ → fᵉ ∘ᵉ αᵉ)
```

### The action on homotopies of the polynomial endofunctor

```agda
htpy-polynomial-endofunctorᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  {fᵉ gᵉ : Xᵉ → Yᵉ} →
  fᵉ ~ᵉ gᵉ → map-polynomial-endofunctorᵉ Aᵉ Bᵉ fᵉ ~ᵉ map-polynomial-endofunctorᵉ Aᵉ Bᵉ gᵉ
htpy-polynomial-endofunctorᵉ Aᵉ Bᵉ {Xᵉ = Xᵉ} {Yᵉ} {fᵉ} {gᵉ} Hᵉ (pairᵉ xᵉ αᵉ) =
  eq-Eq-type-polynomial-endofunctorᵉ
    ( map-polynomial-endofunctorᵉ Aᵉ Bᵉ fᵉ (pairᵉ xᵉ αᵉ))
    ( map-polynomial-endofunctorᵉ Aᵉ Bᵉ gᵉ (pairᵉ xᵉ αᵉ))
    ( pairᵉ reflᵉ (Hᵉ ·rᵉ αᵉ))

coh-refl-htpy-polynomial-endofunctorᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Xᵉ → Yᵉ) →
  htpy-polynomial-endofunctorᵉ Aᵉ Bᵉ (refl-htpyᵉ {fᵉ = fᵉ}) ~ᵉ refl-htpyᵉ
coh-refl-htpy-polynomial-endofunctorᵉ Aᵉ Bᵉ {Xᵉ = Xᵉ} {Yᵉ} fᵉ (pairᵉ xᵉ αᵉ) =
  coh-refl-eq-Eq-type-polynomial-endofunctorᵉ
    ( map-polynomial-endofunctorᵉ Aᵉ Bᵉ fᵉ (pairᵉ xᵉ αᵉ))
```