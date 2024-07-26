# Modules over rings

```agda
module ring-theory.modules-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.addition-homomorphisms-abelian-groupsᵉ
open import group-theory.endomorphism-rings-abelian-groupsᵉ
open import group-theory.homomorphisms-abelian-groupsᵉ

open import ring-theory.homomorphisms-ringsᵉ
open import ring-theory.opposite-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Aᵉ (leftᵉ) module `M`ᵉ overᵉ aᵉ ringᵉ `R`ᵉ consistsᵉ ofᵉ anᵉ abelianᵉ groupᵉ `M`ᵉ equippedᵉ
with anᵉ actionᵉ `Rᵉ → Mᵉ → M`ᵉ suchᵉ

```text
  r(x+yᵉ) = rxᵉ +ᵉ ryᵉ
      r0ᵉ = 0
   r(-xᵉ) = -(rxᵉ)
  (r+s)xᵉ = rxᵉ +ᵉ sxᵉ
      0xᵉ = 0
   (-r)xᵉ = -(rxᵉ)
   (sr)xᵉ = s(rxᵉ)
      1xᵉ = xᵉ
```

Inᵉ otherᵉ words,ᵉ aᵉ leftᵉ module `M`ᵉ overᵉ aᵉ ringᵉ `R`ᵉ consistsᵉ ofᵉ anᵉ abelianᵉ groupᵉ
`M`ᵉ equippedᵉ with aᵉ ringᵉ homomorphismᵉ `Rᵉ → endomorphism-ring-Abᵉ M`.ᵉ Aᵉ rightᵉ
module overᵉ `R`ᵉ consistsᵉ ofᵉ anᵉ abelianᵉ groupᵉ `M`ᵉ equippedᵉ with aᵉ ringᵉ
homomorphismᵉ `Rᵉ → opposite-Ringᵉ (endomorphism-ring-Abᵉ M)`.ᵉ

## Definitions

### Left modules over rings

```agda
left-module-Ringᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Rᵉ : Ringᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
left-module-Ringᵉ l2ᵉ Rᵉ =
  Σᵉ (Abᵉ l2ᵉ) (λ Aᵉ → hom-Ringᵉ Rᵉ (endomorphism-ring-Abᵉ Aᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Mᵉ : left-module-Ringᵉ l2ᵉ Rᵉ)
  where

  ab-left-module-Ringᵉ : Abᵉ l2ᵉ
  ab-left-module-Ringᵉ = pr1ᵉ Mᵉ

  set-left-module-Ringᵉ : Setᵉ l2ᵉ
  set-left-module-Ringᵉ = set-Abᵉ ab-left-module-Ringᵉ

  type-left-module-Ringᵉ : UUᵉ l2ᵉ
  type-left-module-Ringᵉ = type-Abᵉ ab-left-module-Ringᵉ

  add-left-module-Ringᵉ :
    (xᵉ yᵉ : type-left-module-Ringᵉ) → type-left-module-Ringᵉ
  add-left-module-Ringᵉ = add-Abᵉ ab-left-module-Ringᵉ

  zero-left-module-Ringᵉ : type-left-module-Ringᵉ
  zero-left-module-Ringᵉ = zero-Abᵉ ab-left-module-Ringᵉ

  neg-left-module-Ringᵉ : type-left-module-Ringᵉ → type-left-module-Ringᵉ
  neg-left-module-Ringᵉ = neg-Abᵉ ab-left-module-Ringᵉ

  associative-add-left-module-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-left-module-Ringᵉ) →
    Idᵉ
      ( add-left-module-Ringᵉ (add-left-module-Ringᵉ xᵉ yᵉ) zᵉ)
      ( add-left-module-Ringᵉ xᵉ (add-left-module-Ringᵉ yᵉ zᵉ))
  associative-add-left-module-Ringᵉ =
    associative-add-Abᵉ ab-left-module-Ringᵉ

  left-unit-law-add-left-module-Ringᵉ :
    (xᵉ : type-left-module-Ringᵉ) →
    Idᵉ (add-left-module-Ringᵉ zero-left-module-Ringᵉ xᵉ) xᵉ
  left-unit-law-add-left-module-Ringᵉ =
    left-unit-law-add-Abᵉ ab-left-module-Ringᵉ

  right-unit-law-add-left-module-Ringᵉ :
    (xᵉ : type-left-module-Ringᵉ) →
    Idᵉ (add-left-module-Ringᵉ xᵉ zero-left-module-Ringᵉ) xᵉ
  right-unit-law-add-left-module-Ringᵉ =
    right-unit-law-add-Abᵉ ab-left-module-Ringᵉ

  left-inverse-law-add-left-module-Ringᵉ :
    (xᵉ : type-left-module-Ringᵉ) →
    Idᵉ
      ( add-left-module-Ringᵉ (neg-left-module-Ringᵉ xᵉ) xᵉ)
      ( zero-left-module-Ringᵉ)
  left-inverse-law-add-left-module-Ringᵉ =
    left-inverse-law-add-Abᵉ ab-left-module-Ringᵉ

  right-inverse-law-add-left-module-Ringᵉ :
    (xᵉ : type-left-module-Ringᵉ) →
    Idᵉ
      ( add-left-module-Ringᵉ xᵉ (neg-left-module-Ringᵉ xᵉ))
      ( zero-left-module-Ringᵉ)
  right-inverse-law-add-left-module-Ringᵉ =
    right-inverse-law-add-Abᵉ ab-left-module-Ringᵉ

  endomorphism-ring-ab-left-module-Ringᵉ : Ringᵉ l2ᵉ
  endomorphism-ring-ab-left-module-Ringᵉ =
    endomorphism-ring-Abᵉ ab-left-module-Ringᵉ

  mul-hom-left-module-Ringᵉ :
    hom-Ringᵉ Rᵉ endomorphism-ring-ab-left-module-Ringᵉ
  mul-hom-left-module-Ringᵉ = pr2ᵉ Mᵉ

  mul-left-module-Ringᵉ :
    type-Ringᵉ Rᵉ → type-left-module-Ringᵉ → type-left-module-Ringᵉ
  mul-left-module-Ringᵉ xᵉ =
    map-hom-Abᵉ
      ( ab-left-module-Ringᵉ)
      ( ab-left-module-Ringᵉ)
      ( map-hom-Ringᵉ Rᵉ
        ( endomorphism-ring-Abᵉ ab-left-module-Ringᵉ)
        ( mul-hom-left-module-Ringᵉ)
        ( xᵉ))

  left-unit-law-mul-left-module-Ringᵉ :
    (xᵉ : type-left-module-Ringᵉ) →
    Idᵉ ( mul-left-module-Ringᵉ (one-Ringᵉ Rᵉ) xᵉ) xᵉ
  left-unit-law-mul-left-module-Ringᵉ =
    htpy-eq-hom-Abᵉ
      ( ab-left-module-Ringᵉ)
      ( ab-left-module-Ringᵉ)
      ( map-hom-Ringᵉ Rᵉ
        ( endomorphism-ring-ab-left-module-Ringᵉ)
        ( mul-hom-left-module-Ringᵉ)
        ( one-Ringᵉ Rᵉ))
      ( id-hom-Abᵉ ab-left-module-Ringᵉ)
      ( preserves-one-hom-Ringᵉ Rᵉ
        ( endomorphism-ring-ab-left-module-Ringᵉ)
        ( mul-hom-left-module-Ringᵉ))

  left-distributive-mul-add-left-module-Ringᵉ :
    (rᵉ : type-Ringᵉ Rᵉ) (xᵉ yᵉ : type-left-module-Ringᵉ) →
    Idᵉ
      ( mul-left-module-Ringᵉ rᵉ (add-left-module-Ringᵉ xᵉ yᵉ))
      ( add-left-module-Ringᵉ
        ( mul-left-module-Ringᵉ rᵉ xᵉ)
        ( mul-left-module-Ringᵉ rᵉ yᵉ))
  left-distributive-mul-add-left-module-Ringᵉ rᵉ xᵉ yᵉ =
    preserves-add-hom-Abᵉ
      ( ab-left-module-Ringᵉ)
      ( ab-left-module-Ringᵉ)
      ( map-hom-Ringᵉ Rᵉ
          endomorphism-ring-ab-left-module-Ringᵉ
          mul-hom-left-module-Ringᵉ
          rᵉ)

  right-distributive-mul-add-left-module-Ringᵉ :
    (rᵉ sᵉ : type-Ringᵉ Rᵉ) (xᵉ : type-left-module-Ringᵉ) →
    Idᵉ
      ( mul-left-module-Ringᵉ (add-Ringᵉ Rᵉ rᵉ sᵉ) xᵉ)
      ( add-left-module-Ringᵉ
        ( mul-left-module-Ringᵉ rᵉ xᵉ)
        ( mul-left-module-Ringᵉ sᵉ xᵉ))
  right-distributive-mul-add-left-module-Ringᵉ rᵉ sᵉ =
    htpy-eq-hom-Abᵉ
      ( ab-left-module-Ringᵉ)
      ( ab-left-module-Ringᵉ)
      ( map-hom-Ringᵉ Rᵉ
        ( endomorphism-ring-ab-left-module-Ringᵉ)
        ( mul-hom-left-module-Ringᵉ)
        ( add-Ringᵉ Rᵉ rᵉ sᵉ))
      ( add-hom-Abᵉ
        ( ab-left-module-Ringᵉ)
        ( ab-left-module-Ringᵉ)
        ( map-hom-Ringᵉ Rᵉ
          ( endomorphism-ring-ab-left-module-Ringᵉ)
          ( mul-hom-left-module-Ringᵉ)
          ( rᵉ))
        ( map-hom-Ringᵉ Rᵉ
          ( endomorphism-ring-ab-left-module-Ringᵉ)
          ( mul-hom-left-module-Ringᵉ)
          ( sᵉ)))
      ( preserves-add-hom-Ringᵉ Rᵉ
        ( endomorphism-ring-ab-left-module-Ringᵉ)
        ( mul-hom-left-module-Ringᵉ))

  associative-mul-left-module-Ringᵉ :
    (rᵉ sᵉ : type-Ringᵉ Rᵉ) (xᵉ : type-left-module-Ringᵉ) →
    Idᵉ
      ( mul-left-module-Ringᵉ (mul-Ringᵉ Rᵉ rᵉ sᵉ) xᵉ)
      ( mul-left-module-Ringᵉ rᵉ (mul-left-module-Ringᵉ sᵉ xᵉ))
  associative-mul-left-module-Ringᵉ rᵉ sᵉ =
    htpy-eq-hom-Abᵉ
      ( ab-left-module-Ringᵉ)
      ( ab-left-module-Ringᵉ)
      ( map-hom-Ringᵉ Rᵉ
        ( endomorphism-ring-ab-left-module-Ringᵉ)
        ( mul-hom-left-module-Ringᵉ)
        ( mul-Ringᵉ Rᵉ rᵉ sᵉ))
      ( comp-hom-Abᵉ
        ( ab-left-module-Ringᵉ)
        ( ab-left-module-Ringᵉ)
        ( ab-left-module-Ringᵉ)
        ( map-hom-Ringᵉ Rᵉ
          ( endomorphism-ring-ab-left-module-Ringᵉ)
          ( mul-hom-left-module-Ringᵉ)
          ( rᵉ))
        ( map-hom-Ringᵉ Rᵉ
          ( endomorphism-ring-ab-left-module-Ringᵉ)
          ( mul-hom-left-module-Ringᵉ)
          ( sᵉ)))
      ( preserves-mul-hom-Ringᵉ Rᵉ
        ( endomorphism-ring-ab-left-module-Ringᵉ)
        ( mul-hom-left-module-Ringᵉ))

  left-zero-law-mul-left-module-Ringᵉ :
    (xᵉ : type-left-module-Ringᵉ) →
    Idᵉ ( mul-left-module-Ringᵉ (zero-Ringᵉ Rᵉ) xᵉ) zero-left-module-Ringᵉ
  left-zero-law-mul-left-module-Ringᵉ =
    htpy-eq-hom-Abᵉ
      ( ab-left-module-Ringᵉ)
      ( ab-left-module-Ringᵉ)
      ( map-hom-Ringᵉ Rᵉ
        ( endomorphism-ring-ab-left-module-Ringᵉ)
        ( mul-hom-left-module-Ringᵉ)
        ( zero-Ringᵉ Rᵉ))
      ( zero-hom-Abᵉ ab-left-module-Ringᵉ ab-left-module-Ringᵉ)
      ( preserves-zero-hom-Ringᵉ Rᵉ
        ( endomorphism-ring-ab-left-module-Ringᵉ)
        ( mul-hom-left-module-Ringᵉ))

  right-zero-law-mul-left-module-Ringᵉ :
    (rᵉ : type-Ringᵉ Rᵉ) →
    Idᵉ ( mul-left-module-Ringᵉ rᵉ zero-left-module-Ringᵉ) zero-left-module-Ringᵉ
  right-zero-law-mul-left-module-Ringᵉ rᵉ =
    preserves-zero-hom-Abᵉ
      ( ab-left-module-Ringᵉ)
      ( ab-left-module-Ringᵉ)
      ( map-hom-Ringᵉ Rᵉ
        ( endomorphism-ring-ab-left-module-Ringᵉ)
        ( mul-hom-left-module-Ringᵉ)
        ( rᵉ))

  left-negative-law-mul-left-module-Ringᵉ :
    (rᵉ : type-Ringᵉ Rᵉ) (xᵉ : type-left-module-Ringᵉ) →
    Idᵉ
      ( mul-left-module-Ringᵉ (neg-Ringᵉ Rᵉ rᵉ) xᵉ)
      ( neg-left-module-Ringᵉ (mul-left-module-Ringᵉ rᵉ xᵉ))
  left-negative-law-mul-left-module-Ringᵉ rᵉ =
    htpy-eq-hom-Abᵉ
      ( ab-left-module-Ringᵉ)
      ( ab-left-module-Ringᵉ)
      ( map-hom-Ringᵉ Rᵉ
        ( endomorphism-ring-ab-left-module-Ringᵉ)
        ( mul-hom-left-module-Ringᵉ)
        ( neg-Ringᵉ Rᵉ rᵉ))
      ( neg-hom-Abᵉ
        ( ab-left-module-Ringᵉ)
        ( ab-left-module-Ringᵉ)
        ( map-hom-Ringᵉ Rᵉ
          ( endomorphism-ring-ab-left-module-Ringᵉ)
          ( mul-hom-left-module-Ringᵉ)
          ( rᵉ)))
      ( preserves-neg-hom-Ringᵉ Rᵉ
        ( endomorphism-ring-ab-left-module-Ringᵉ)
        ( mul-hom-left-module-Ringᵉ))

  right-negative-law-mul-left-module-Ringᵉ :
    (rᵉ : type-Ringᵉ Rᵉ) (xᵉ : type-left-module-Ringᵉ) →
    Idᵉ
      ( mul-left-module-Ringᵉ rᵉ (neg-left-module-Ringᵉ xᵉ))
      ( neg-left-module-Ringᵉ (mul-left-module-Ringᵉ rᵉ xᵉ))
  right-negative-law-mul-left-module-Ringᵉ rᵉ xᵉ =
    preserves-negatives-hom-Abᵉ
      ( ab-left-module-Ringᵉ)
      ( ab-left-module-Ringᵉ)
      ( map-hom-Ringᵉ Rᵉ
        ( endomorphism-ring-ab-left-module-Ringᵉ)
        ( mul-hom-left-module-Ringᵉ)
        ( rᵉ))
```

### Right modules over rings

```agda
right-module-Ringᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Rᵉ : Ringᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
right-module-Ringᵉ l2ᵉ Rᵉ =
  Σᵉ (Abᵉ l2ᵉ) (λ Aᵉ → hom-Ringᵉ Rᵉ (op-Ringᵉ (endomorphism-ring-Abᵉ Aᵉ)))

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Mᵉ : right-module-Ringᵉ l2ᵉ Rᵉ)
  where

  ab-right-module-Ringᵉ : Abᵉ l2ᵉ
  ab-right-module-Ringᵉ = pr1ᵉ Mᵉ

  set-right-module-Ringᵉ : Setᵉ l2ᵉ
  set-right-module-Ringᵉ = set-Abᵉ ab-right-module-Ringᵉ

  type-right-module-Ringᵉ : UUᵉ l2ᵉ
  type-right-module-Ringᵉ = type-Abᵉ ab-right-module-Ringᵉ

  add-right-module-Ringᵉ :
    (xᵉ yᵉ : type-right-module-Ringᵉ) → type-right-module-Ringᵉ
  add-right-module-Ringᵉ = add-Abᵉ ab-right-module-Ringᵉ

  zero-right-module-Ringᵉ : type-right-module-Ringᵉ
  zero-right-module-Ringᵉ = zero-Abᵉ ab-right-module-Ringᵉ

  neg-right-module-Ringᵉ : type-right-module-Ringᵉ → type-right-module-Ringᵉ
  neg-right-module-Ringᵉ = neg-Abᵉ ab-right-module-Ringᵉ

  associative-add-right-module-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-right-module-Ringᵉ) →
    Idᵉ
      ( add-right-module-Ringᵉ (add-right-module-Ringᵉ xᵉ yᵉ) zᵉ)
      ( add-right-module-Ringᵉ xᵉ (add-right-module-Ringᵉ yᵉ zᵉ))
  associative-add-right-module-Ringᵉ =
    associative-add-Abᵉ ab-right-module-Ringᵉ

  left-unit-law-add-right-module-Ringᵉ :
    (xᵉ : type-right-module-Ringᵉ) →
    Idᵉ (add-right-module-Ringᵉ zero-right-module-Ringᵉ xᵉ) xᵉ
  left-unit-law-add-right-module-Ringᵉ =
    left-unit-law-add-Abᵉ ab-right-module-Ringᵉ

  right-unit-law-add-right-module-Ringᵉ :
    (xᵉ : type-right-module-Ringᵉ) →
    Idᵉ (add-right-module-Ringᵉ xᵉ zero-right-module-Ringᵉ) xᵉ
  right-unit-law-add-right-module-Ringᵉ =
    right-unit-law-add-Abᵉ ab-right-module-Ringᵉ

  left-inverse-law-add-right-module-Ringᵉ :
    (xᵉ : type-right-module-Ringᵉ) →
    Idᵉ
      ( add-right-module-Ringᵉ (neg-right-module-Ringᵉ xᵉ) xᵉ)
      ( zero-right-module-Ringᵉ)
  left-inverse-law-add-right-module-Ringᵉ =
    left-inverse-law-add-Abᵉ ab-right-module-Ringᵉ

  right-inverse-law-add-right-module-Ringᵉ :
    (xᵉ : type-right-module-Ringᵉ) →
    Idᵉ
      ( add-right-module-Ringᵉ xᵉ (neg-right-module-Ringᵉ xᵉ))
      ( zero-right-module-Ringᵉ)
  right-inverse-law-add-right-module-Ringᵉ =
    right-inverse-law-add-Abᵉ ab-right-module-Ringᵉ

  endomorphism-ring-ab-right-module-Ringᵉ : Ringᵉ l2ᵉ
  endomorphism-ring-ab-right-module-Ringᵉ =
    endomorphism-ring-Abᵉ ab-right-module-Ringᵉ

  mul-hom-right-module-Ringᵉ :
    hom-Ringᵉ Rᵉ (op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
  mul-hom-right-module-Ringᵉ = pr2ᵉ Mᵉ

  mul-right-module-Ringᵉ :
    type-Ringᵉ Rᵉ → type-right-module-Ringᵉ → type-right-module-Ringᵉ
  mul-right-module-Ringᵉ xᵉ =
    map-hom-Abᵉ
      ( ab-right-module-Ringᵉ)
      ( ab-right-module-Ringᵉ)
      ( map-hom-Ringᵉ Rᵉ
        ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
        ( mul-hom-right-module-Ringᵉ)
        ( xᵉ))

  left-unit-law-mul-right-module-Ringᵉ :
    (xᵉ : type-right-module-Ringᵉ) →
    Idᵉ ( mul-right-module-Ringᵉ (one-Ringᵉ Rᵉ) xᵉ) xᵉ
  left-unit-law-mul-right-module-Ringᵉ =
    htpy-eq-hom-Abᵉ
      ( ab-right-module-Ringᵉ)
      ( ab-right-module-Ringᵉ)
      ( map-hom-Ringᵉ Rᵉ
        ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
        ( mul-hom-right-module-Ringᵉ)
        ( one-Ringᵉ Rᵉ))
      ( id-hom-Abᵉ ab-right-module-Ringᵉ)
      ( preserves-one-hom-Ringᵉ Rᵉ
        ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
        ( mul-hom-right-module-Ringᵉ))

  left-distributive-mul-add-right-module-Ringᵉ :
    (rᵉ : type-Ringᵉ Rᵉ) (xᵉ yᵉ : type-right-module-Ringᵉ) →
    Idᵉ
      ( mul-right-module-Ringᵉ rᵉ (add-right-module-Ringᵉ xᵉ yᵉ))
      ( add-right-module-Ringᵉ
        ( mul-right-module-Ringᵉ rᵉ xᵉ)
        ( mul-right-module-Ringᵉ rᵉ yᵉ))
  left-distributive-mul-add-right-module-Ringᵉ rᵉ xᵉ yᵉ =
    preserves-add-hom-Abᵉ
      ( ab-right-module-Ringᵉ)
      ( ab-right-module-Ringᵉ)
      ( map-hom-Ringᵉ Rᵉ
        ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
        ( mul-hom-right-module-Ringᵉ)
        ( rᵉ))

  right-distributive-mul-add-right-module-Ringᵉ :
    (rᵉ sᵉ : type-Ringᵉ Rᵉ) (xᵉ : type-right-module-Ringᵉ) →
    Idᵉ
      ( mul-right-module-Ringᵉ (add-Ringᵉ Rᵉ rᵉ sᵉ) xᵉ)
      ( add-right-module-Ringᵉ
        ( mul-right-module-Ringᵉ rᵉ xᵉ)
        ( mul-right-module-Ringᵉ sᵉ xᵉ))
  right-distributive-mul-add-right-module-Ringᵉ rᵉ sᵉ =
    htpy-eq-hom-Abᵉ
      ( ab-right-module-Ringᵉ)
      ( ab-right-module-Ringᵉ)
      ( map-hom-Ringᵉ Rᵉ
        ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
        ( mul-hom-right-module-Ringᵉ)
        ( add-Ringᵉ Rᵉ rᵉ sᵉ))
      ( add-hom-Abᵉ
        ( ab-right-module-Ringᵉ)
        ( ab-right-module-Ringᵉ)
        ( map-hom-Ringᵉ Rᵉ
          ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
          ( mul-hom-right-module-Ringᵉ)
          ( rᵉ))
        ( map-hom-Ringᵉ Rᵉ
          ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
          ( mul-hom-right-module-Ringᵉ)
          ( sᵉ)))
      ( preserves-add-hom-Ringᵉ Rᵉ
        ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
        ( mul-hom-right-module-Ringᵉ))

  associative-mul-right-module-Ringᵉ :
    (rᵉ sᵉ : type-Ringᵉ Rᵉ) (xᵉ : type-right-module-Ringᵉ) →
    Idᵉ
      ( mul-right-module-Ringᵉ (mul-Ringᵉ Rᵉ rᵉ sᵉ) xᵉ)
      ( mul-right-module-Ringᵉ sᵉ (mul-right-module-Ringᵉ rᵉ xᵉ))
  associative-mul-right-module-Ringᵉ rᵉ sᵉ =
    htpy-eq-hom-Abᵉ
      ( ab-right-module-Ringᵉ)
      ( ab-right-module-Ringᵉ)
      ( map-hom-Ringᵉ Rᵉ
        ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
        ( mul-hom-right-module-Ringᵉ)
        ( mul-Ringᵉ Rᵉ rᵉ sᵉ))
      ( comp-hom-Abᵉ
        ( ab-right-module-Ringᵉ)
        ( ab-right-module-Ringᵉ)
        ( ab-right-module-Ringᵉ)
        ( map-hom-Ringᵉ Rᵉ
          ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
          ( mul-hom-right-module-Ringᵉ)
          ( sᵉ))
        ( map-hom-Ringᵉ Rᵉ
          ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
          ( mul-hom-right-module-Ringᵉ)
          ( rᵉ)))
      ( preserves-mul-hom-Ringᵉ Rᵉ
        ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
        ( mul-hom-right-module-Ringᵉ))

  left-zero-law-mul-right-module-Ringᵉ :
    (xᵉ : type-right-module-Ringᵉ) →
    Idᵉ ( mul-right-module-Ringᵉ (zero-Ringᵉ Rᵉ) xᵉ) zero-right-module-Ringᵉ
  left-zero-law-mul-right-module-Ringᵉ =
    htpy-eq-hom-Abᵉ
      ( ab-right-module-Ringᵉ)
      ( ab-right-module-Ringᵉ)
      ( map-hom-Ringᵉ Rᵉ
        ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
        ( mul-hom-right-module-Ringᵉ)
        ( zero-Ringᵉ Rᵉ))
      ( zero-hom-Abᵉ ab-right-module-Ringᵉ ab-right-module-Ringᵉ)
      ( preserves-zero-hom-Ringᵉ Rᵉ
        ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
        ( mul-hom-right-module-Ringᵉ))

  right-zero-law-mul-right-module-Ringᵉ :
    (rᵉ : type-Ringᵉ Rᵉ) →
    Idᵉ ( mul-right-module-Ringᵉ rᵉ zero-right-module-Ringᵉ) zero-right-module-Ringᵉ
  right-zero-law-mul-right-module-Ringᵉ rᵉ =
    preserves-zero-hom-Abᵉ
      ( ab-right-module-Ringᵉ)
      ( ab-right-module-Ringᵉ)
      ( map-hom-Ringᵉ Rᵉ
        ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
        ( mul-hom-right-module-Ringᵉ)
        ( rᵉ))

  left-negative-law-mul-right-module-Ringᵉ :
    (rᵉ : type-Ringᵉ Rᵉ) (xᵉ : type-right-module-Ringᵉ) →
    Idᵉ
      ( mul-right-module-Ringᵉ (neg-Ringᵉ Rᵉ rᵉ) xᵉ)
      ( neg-right-module-Ringᵉ (mul-right-module-Ringᵉ rᵉ xᵉ))
  left-negative-law-mul-right-module-Ringᵉ rᵉ =
    htpy-eq-hom-Abᵉ
      ( ab-right-module-Ringᵉ)
      ( ab-right-module-Ringᵉ)
      ( map-hom-Ringᵉ Rᵉ
        ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
        ( mul-hom-right-module-Ringᵉ)
        ( neg-Ringᵉ Rᵉ rᵉ))
      ( neg-hom-Abᵉ
        ( ab-right-module-Ringᵉ)
        ( ab-right-module-Ringᵉ)
        ( map-hom-Ringᵉ Rᵉ
          ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
          ( mul-hom-right-module-Ringᵉ)
          ( rᵉ)))
      ( preserves-neg-hom-Ringᵉ Rᵉ
        ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
        ( mul-hom-right-module-Ringᵉ))

  right-negative-law-mul-right-module-Ringᵉ :
    (rᵉ : type-Ringᵉ Rᵉ) (xᵉ : type-right-module-Ringᵉ) →
    Idᵉ
      ( mul-right-module-Ringᵉ rᵉ (neg-right-module-Ringᵉ xᵉ))
      ( neg-right-module-Ringᵉ (mul-right-module-Ringᵉ rᵉ xᵉ))
  right-negative-law-mul-right-module-Ringᵉ rᵉ xᵉ =
    preserves-negatives-hom-Abᵉ
      ( ab-right-module-Ringᵉ)
      ( ab-right-module-Ringᵉ)
      ( map-hom-Ringᵉ Rᵉ
        ( op-Ringᵉ endomorphism-ring-ab-right-module-Ringᵉ)
        ( mul-hom-right-module-Ringᵉ)
        ( rᵉ))
```