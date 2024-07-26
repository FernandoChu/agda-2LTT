# Transporting commutative ring structures along isomorphisms of abelian groups

```agda
module
  commutative-algebra.transporting-commutative-ring-structure-isomorphisms-abelian-groupsᵉ
  where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.homomorphisms-commutative-ringsᵉ
open import commutative-algebra.isomorphisms-commutative-ringsᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unital-binary-operationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.isomorphisms-abelian-groupsᵉ
open import group-theory.semigroupsᵉ

open import ring-theory.homomorphisms-ringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.transporting-ring-structure-along-isomorphisms-abelian-groupsᵉ
```

</details>

## Idea

Ifᵉ `A`ᵉ isᵉ aᵉ [commutativeᵉ ring](commutative-algebra.commutative-rings.mdᵉ) andᵉ `B`ᵉ
isᵉ anᵉ [abelianᵉ group](group-theory.abelian-groups.mdᵉ) equippedᵉ with anᵉ
[isomorphism](group-theory.isomorphisms-abelian-groups.mdᵉ) `Aᵉ ≅ᵉ B`ᵉ fromᵉ theᵉ
additiveᵉ abelianᵉ groupᵉ ofᵉ `A`ᵉ to `B`,ᵉ thenᵉ theᵉ multiplicativeᵉ structureᵉ ofᵉ `A`ᵉ
canᵉ beᵉ transportedᵉ alongᵉ theᵉ isomorphismᵉ to obtainᵉ aᵉ ringᵉ structureᵉ onᵉ `B`.ᵉ

Noteᵉ thatᵉ thisᵉ structureᵉ canᵉ beᵉ transportedᵉ byᵉ
[univalence](foundation.univalence.md).ᵉ However,ᵉ weᵉ willᵉ giveᵉ explicitᵉ
definitions,ᵉ sinceᵉ univalenceᵉ isᵉ notᵉ strictlyᵉ necessaryᵉ to obtainᵉ thisᵉ
transportedᵉ ringᵉ structure.ᵉ

## Definitions

### Transporting the multiplicative structure of a commutative ring along an isomorphism of abelian groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  (fᵉ : iso-Abᵉ (ab-Commutative-Ringᵉ Aᵉ) Bᵉ)
  where

  ring-transport-commutative-ring-structure-iso-Abᵉ : Ringᵉ l2ᵉ
  ring-transport-commutative-ring-structure-iso-Abᵉ =
    transport-ring-structure-iso-Abᵉ (ring-Commutative-Ringᵉ Aᵉ) Bᵉ fᵉ

  one-transport-commutative-ring-structure-iso-Abᵉ : type-Abᵉ Bᵉ
  one-transport-commutative-ring-structure-iso-Abᵉ =
    one-transport-ring-structure-iso-Abᵉ (ring-Commutative-Ringᵉ Aᵉ) Bᵉ fᵉ

  mul-transport-commutative-ring-structure-iso-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Bᵉ) → type-Abᵉ Bᵉ
  mul-transport-commutative-ring-structure-iso-Abᵉ =
    mul-transport-ring-structure-iso-Abᵉ (ring-Commutative-Ringᵉ Aᵉ) Bᵉ fᵉ

  private
    oneᵉ = one-transport-commutative-ring-structure-iso-Abᵉ
    mulᵉ = mul-transport-commutative-ring-structure-iso-Abᵉ
    map-fᵉ = map-iso-Abᵉ (ab-Commutative-Ringᵉ Aᵉ) Bᵉ fᵉ
    map-inv-fᵉ = map-inv-iso-Abᵉ (ab-Commutative-Ringᵉ Aᵉ) Bᵉ fᵉ

  associative-mul-transport-commutative-ring-structure-iso-Abᵉ :
    (xᵉ yᵉ zᵉ : type-Abᵉ Bᵉ) → mulᵉ (mulᵉ xᵉ yᵉ) zᵉ ＝ᵉ mulᵉ xᵉ (mulᵉ yᵉ zᵉ)
  associative-mul-transport-commutative-ring-structure-iso-Abᵉ =
    associative-mul-transport-ring-structure-iso-Abᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Bᵉ)
      ( fᵉ)

  left-unit-law-mul-transport-commutative-ring-structure-iso-Abᵉ :
    (xᵉ : type-Abᵉ Bᵉ) → mulᵉ oneᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-transport-commutative-ring-structure-iso-Abᵉ =
    left-unit-law-mul-transport-ring-structure-iso-Abᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Bᵉ)
      ( fᵉ)

  right-unit-law-mul-transport-commutative-ring-structure-iso-Abᵉ :
    (xᵉ : type-Abᵉ Bᵉ) → mulᵉ xᵉ oneᵉ ＝ᵉ xᵉ
  right-unit-law-mul-transport-commutative-ring-structure-iso-Abᵉ =
    right-unit-law-mul-transport-ring-structure-iso-Abᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Bᵉ)
      ( fᵉ)

  left-distributive-mul-add-transport-commutative-ring-structure-iso-Abᵉ :
    (xᵉ yᵉ zᵉ : type-Abᵉ Bᵉ) → mulᵉ xᵉ (add-Abᵉ Bᵉ yᵉ zᵉ) ＝ᵉ add-Abᵉ Bᵉ (mulᵉ xᵉ yᵉ) (mulᵉ xᵉ zᵉ)
  left-distributive-mul-add-transport-commutative-ring-structure-iso-Abᵉ =
    left-distributive-mul-add-transport-ring-structure-iso-Abᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Bᵉ)
      ( fᵉ)

  right-distributive-mul-add-transport-commutative-ring-structure-iso-Abᵉ :
    (xᵉ yᵉ zᵉ : type-Abᵉ Bᵉ) → mulᵉ (add-Abᵉ Bᵉ xᵉ yᵉ) zᵉ ＝ᵉ add-Abᵉ Bᵉ (mulᵉ xᵉ zᵉ) (mulᵉ yᵉ zᵉ)
  right-distributive-mul-add-transport-commutative-ring-structure-iso-Abᵉ =
    right-distributive-mul-add-transport-ring-structure-iso-Abᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Bᵉ)
      ( fᵉ)

  commutative-mul-transport-commutative-ring-structure-iso-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Bᵉ) → mulᵉ xᵉ yᵉ ＝ᵉ mulᵉ yᵉ xᵉ
  commutative-mul-transport-commutative-ring-structure-iso-Abᵉ xᵉ yᵉ =
    apᵉ map-fᵉ (commutative-mul-Commutative-Ringᵉ Aᵉ _ _)

  transport-commutative-ring-structure-iso-Abᵉ :
    Commutative-Ringᵉ l2ᵉ
  pr1ᵉ transport-commutative-ring-structure-iso-Abᵉ =
    ring-transport-commutative-ring-structure-iso-Abᵉ
  pr2ᵉ transport-commutative-ring-structure-iso-Abᵉ =
    commutative-mul-transport-commutative-ring-structure-iso-Abᵉ

  preserves-mul-transport-commutative-ring-structure-iso-Abᵉ :
    preserves-mul-hom-Abᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-transport-commutative-ring-structure-iso-Abᵉ)
      ( hom-iso-Abᵉ (ab-Commutative-Ringᵉ Aᵉ) Bᵉ fᵉ)
  preserves-mul-transport-commutative-ring-structure-iso-Abᵉ =
    preserves-mul-transport-ring-structure-iso-Abᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Bᵉ)
      ( fᵉ)

  hom-iso-transport-commutative-ring-structure-iso-Abᵉ :
    hom-Commutative-Ringᵉ Aᵉ transport-commutative-ring-structure-iso-Abᵉ
  hom-iso-transport-commutative-ring-structure-iso-Abᵉ =
    hom-iso-transport-ring-structure-iso-Abᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Bᵉ)
      ( fᵉ)

  is-iso-iso-transport-commutative-ring-structure-iso-Abᵉ :
    is-iso-Commutative-Ringᵉ
      ( Aᵉ)
      ( transport-commutative-ring-structure-iso-Abᵉ)
      ( hom-iso-transport-commutative-ring-structure-iso-Abᵉ)
  is-iso-iso-transport-commutative-ring-structure-iso-Abᵉ =
    is-iso-iso-transport-ring-structure-iso-Abᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Bᵉ)
      ( fᵉ)

  iso-transport-commutative-ring-structure-iso-Abᵉ :
    iso-Commutative-Ringᵉ Aᵉ transport-commutative-ring-structure-iso-Abᵉ
  iso-transport-commutative-ring-structure-iso-Abᵉ =
    iso-transport-ring-structure-iso-Abᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Bᵉ)
      ( fᵉ)
```