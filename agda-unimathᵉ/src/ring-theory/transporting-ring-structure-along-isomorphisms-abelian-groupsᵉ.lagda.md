# Transporting ring structures along isomorphisms of abelian groups

```agda
module
  ring-theory.transporting-ring-structure-along-isomorphisms-abelian-groupsᵉ
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unital-binary-operationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.isomorphisms-abelian-groupsᵉ
open import group-theory.semigroupsᵉ

open import ring-theory.homomorphisms-ringsᵉ
open import ring-theory.isomorphisms-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Ifᵉ `R`ᵉ isᵉ aᵉ [ring](ring-theory.rings.mdᵉ) andᵉ `A`ᵉ isᵉ anᵉ
[abelianᵉ group](group-theory.abelian-groups.mdᵉ) equippedᵉ with anᵉ
[isomorphism](group-theory.isomorphisms-abelian-groups.mdᵉ) `Rᵉ ≅ᵉ A`ᵉ fromᵉ theᵉ
additiveᵉ abelianᵉ groupᵉ ofᵉ `R`ᵉ to `A`,ᵉ thenᵉ theᵉ multiplicativeᵉ structureᵉ ofᵉ `R`ᵉ
canᵉ beᵉ transportedᵉ alongᵉ theᵉ isomorphismᵉ to obtainᵉ aᵉ ringᵉ structureᵉ onᵉ `A`.ᵉ

Noteᵉ thatᵉ thisᵉ structureᵉ canᵉ beᵉ transportedᵉ byᵉ
[univalence](foundation.univalence.md).ᵉ However,ᵉ weᵉ willᵉ giveᵉ explicitᵉ
definitions,ᵉ sinceᵉ univalenceᵉ isᵉ notᵉ strictlyᵉ necessaryᵉ to obtainᵉ thisᵉ
transportedᵉ ringᵉ structure.ᵉ

## Definitions

### Transporting the multiplicative structure of a ring along an isomorphism of abelian groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Aᵉ : Abᵉ l2ᵉ)
  (fᵉ : iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ)
  where

  one-transport-ring-structure-iso-Abᵉ : type-Abᵉ Aᵉ
  one-transport-ring-structure-iso-Abᵉ =
    map-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ (one-Ringᵉ Rᵉ)

  mul-transport-ring-structure-iso-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) → type-Abᵉ Aᵉ
  mul-transport-ring-structure-iso-Abᵉ xᵉ yᵉ =
    map-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ
      ( mul-Ringᵉ Rᵉ
        ( map-inv-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ xᵉ)
        ( map-inv-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ yᵉ))

  private
    oneᵉ = one-transport-ring-structure-iso-Abᵉ
    mulᵉ = mul-transport-ring-structure-iso-Abᵉ
    map-fᵉ = map-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ
    map-inv-fᵉ = map-inv-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ

  associative-mul-transport-ring-structure-iso-Abᵉ :
    (xᵉ yᵉ zᵉ : type-Abᵉ Aᵉ) → mulᵉ (mulᵉ xᵉ yᵉ) zᵉ ＝ᵉ mulᵉ xᵉ (mulᵉ yᵉ zᵉ)
  associative-mul-transport-ring-structure-iso-Abᵉ xᵉ yᵉ zᵉ =
    apᵉ
      ( map-fᵉ)
      ( ( apᵉ (mul-Ring'ᵉ Rᵉ _) (is-retraction-map-inv-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ _)) ∙ᵉ
        ( ( associative-mul-Ringᵉ Rᵉ _ _ _) ∙ᵉ
          ( invᵉ
            ( apᵉ
              ( mul-Ringᵉ Rᵉ _)
              ( is-retraction-map-inv-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ _)))))

  left-unit-law-mul-transport-ring-structure-iso-Abᵉ :
    (xᵉ : type-Abᵉ Aᵉ) → mulᵉ oneᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-transport-ring-structure-iso-Abᵉ xᵉ =
    ( apᵉ
      ( map-fᵉ)
      ( ( apᵉ (mul-Ring'ᵉ Rᵉ _) (is-retraction-map-inv-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ _)) ∙ᵉ
        ( left-unit-law-mul-Ringᵉ Rᵉ _))) ∙ᵉ
    ( is-section-map-inv-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ xᵉ)

  right-unit-law-mul-transport-ring-structure-iso-Abᵉ :
    (xᵉ : type-Abᵉ Aᵉ) → mulᵉ xᵉ oneᵉ ＝ᵉ xᵉ
  right-unit-law-mul-transport-ring-structure-iso-Abᵉ xᵉ =
    ( apᵉ
      ( map-fᵉ)
      ( ( apᵉ (mul-Ringᵉ Rᵉ _) (is-retraction-map-inv-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ _)) ∙ᵉ
        ( right-unit-law-mul-Ringᵉ Rᵉ _))) ∙ᵉ
    ( is-section-map-inv-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ xᵉ)

  left-distributive-mul-add-transport-ring-structure-iso-Abᵉ :
    (xᵉ yᵉ zᵉ : type-Abᵉ Aᵉ) → mulᵉ xᵉ (add-Abᵉ Aᵉ yᵉ zᵉ) ＝ᵉ add-Abᵉ Aᵉ (mulᵉ xᵉ yᵉ) (mulᵉ xᵉ zᵉ)
  left-distributive-mul-add-transport-ring-structure-iso-Abᵉ
    xᵉ yᵉ zᵉ =
    ( apᵉ
      ( map-fᵉ)
      ( ( apᵉ (mul-Ringᵉ Rᵉ _) (preserves-add-inv-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ)) ∙ᵉ
        ( left-distributive-mul-add-Ringᵉ Rᵉ _ _ _))) ∙ᵉ
    ( preserves-add-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ)

  right-distributive-mul-add-transport-ring-structure-iso-Abᵉ :
    (xᵉ yᵉ zᵉ : type-Abᵉ Aᵉ) → mulᵉ (add-Abᵉ Aᵉ xᵉ yᵉ) zᵉ ＝ᵉ add-Abᵉ Aᵉ (mulᵉ xᵉ zᵉ) (mulᵉ yᵉ zᵉ)
  right-distributive-mul-add-transport-ring-structure-iso-Abᵉ
    xᵉ yᵉ zᵉ =
    ( apᵉ
      ( map-fᵉ)
      ( ( apᵉ (mul-Ring'ᵉ Rᵉ _) (preserves-add-inv-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ)) ∙ᵉ
        ( right-distributive-mul-add-Ringᵉ Rᵉ _ _ _))) ∙ᵉ
    ( preserves-add-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ)

  has-associative-mul-transport-ring-structure-iso-Abᵉ :
    has-associative-mul-Setᵉ (set-Abᵉ Aᵉ)
  pr1ᵉ has-associative-mul-transport-ring-structure-iso-Abᵉ =
    mulᵉ
  pr2ᵉ has-associative-mul-transport-ring-structure-iso-Abᵉ =
    associative-mul-transport-ring-structure-iso-Abᵉ

  is-unital-transport-ring-structure-iso-Abᵉ :
    is-unitalᵉ mulᵉ
  pr1ᵉ is-unital-transport-ring-structure-iso-Abᵉ = oneᵉ
  pr1ᵉ (pr2ᵉ is-unital-transport-ring-structure-iso-Abᵉ) =
    left-unit-law-mul-transport-ring-structure-iso-Abᵉ
  pr2ᵉ (pr2ᵉ is-unital-transport-ring-structure-iso-Abᵉ) =
    right-unit-law-mul-transport-ring-structure-iso-Abᵉ

  transport-ring-structure-iso-Abᵉ : Ringᵉ l2ᵉ
  pr1ᵉ transport-ring-structure-iso-Abᵉ = Aᵉ
  pr1ᵉ (pr2ᵉ transport-ring-structure-iso-Abᵉ) =
    has-associative-mul-transport-ring-structure-iso-Abᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ transport-ring-structure-iso-Abᵉ)) =
    is-unital-transport-ring-structure-iso-Abᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ transport-ring-structure-iso-Abᵉ))) =
    left-distributive-mul-add-transport-ring-structure-iso-Abᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ transport-ring-structure-iso-Abᵉ))) =
    right-distributive-mul-add-transport-ring-structure-iso-Abᵉ

  preserves-mul-transport-ring-structure-iso-Abᵉ :
    preserves-mul-hom-Abᵉ
      ( Rᵉ)
      ( transport-ring-structure-iso-Abᵉ)
      ( hom-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ)
  preserves-mul-transport-ring-structure-iso-Abᵉ {xᵉ} {yᵉ} =
    apᵉ map-fᵉ
      ( ap-mul-Ringᵉ Rᵉ
        ( invᵉ (is-retraction-map-inv-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ xᵉ))
        ( invᵉ (is-retraction-map-inv-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ yᵉ)))

  hom-iso-transport-ring-structure-iso-Abᵉ :
    hom-Ringᵉ Rᵉ transport-ring-structure-iso-Abᵉ
  pr1ᵉ hom-iso-transport-ring-structure-iso-Abᵉ =
    hom-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ
  pr1ᵉ (pr2ᵉ hom-iso-transport-ring-structure-iso-Abᵉ) =
    preserves-mul-transport-ring-structure-iso-Abᵉ
  pr2ᵉ (pr2ᵉ hom-iso-transport-ring-structure-iso-Abᵉ) =
    reflᵉ

  is-iso-iso-transport-ring-structure-iso-Abᵉ :
    is-iso-Ringᵉ
      ( Rᵉ)
      ( transport-ring-structure-iso-Abᵉ)
      ( hom-iso-transport-ring-structure-iso-Abᵉ)
  is-iso-iso-transport-ring-structure-iso-Abᵉ =
    is-iso-ring-is-iso-Abᵉ
      ( Rᵉ)
      ( transport-ring-structure-iso-Abᵉ)
      ( hom-iso-transport-ring-structure-iso-Abᵉ)
      ( is-iso-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ)

  iso-transport-ring-structure-iso-Abᵉ :
    iso-Ringᵉ Rᵉ transport-ring-structure-iso-Abᵉ
  pr1ᵉ (pr1ᵉ iso-transport-ring-structure-iso-Abᵉ) = hom-iso-Abᵉ (ab-Ringᵉ Rᵉ) Aᵉ fᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ iso-transport-ring-structure-iso-Abᵉ)) =
    preserves-mul-transport-ring-structure-iso-Abᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ iso-transport-ring-structure-iso-Abᵉ)) =
    reflᵉ
  pr2ᵉ iso-transport-ring-structure-iso-Abᵉ =
    is-iso-iso-transport-ring-structure-iso-Abᵉ
```