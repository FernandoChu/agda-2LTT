# Conjugation in groups

```agda
module group-theory.conjugationᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.subtypesᵉ
open import foundation.transposition-identifications-along-retractionsᵉ
open import foundation.transposition-identifications-along-sectionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.group-actionsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.integer-powers-of-elements-groupsᵉ
open import group-theory.isomorphisms-groupsᵉ
open import group-theory.subsets-groupsᵉ
```

</details>

## Idea

**Conjugation**ᵉ byᵉ anᵉ elementᵉ `x`ᵉ ofᵉ aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ isᵉ
theᵉ mapᵉ `yᵉ ↦ᵉ (xy)x⁻¹`.ᵉ Thisᵉ canᵉ beᵉ seenᵉ asᵉ aᵉ homomorphismᵉ `Gᵉ → G`ᵉ asᵉ wellᵉ asᵉ aᵉ
groupᵉ actionᵉ ofᵉ `G`ᵉ ontoᵉ itself.ᵉ

Theᵉ deloopingᵉ ofᵉ theᵉ conjugationᵉ homomorphismᵉ isᵉ definedᵉ in
[`structured-types.conjugation-pointed-types.md`](structured-types.conjugation-pointed-types.md)`.ᵉ

## Definitions

### Conjugation

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  equiv-conjugation-Groupᵉ : (xᵉ : type-Groupᵉ Gᵉ) → type-Groupᵉ Gᵉ ≃ᵉ type-Groupᵉ Gᵉ
  equiv-conjugation-Groupᵉ xᵉ =
    equiv-mul-Group'ᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ) ∘eᵉ equiv-mul-Groupᵉ Gᵉ xᵉ

  conjugation-Groupᵉ : (xᵉ : type-Groupᵉ Gᵉ) → type-Groupᵉ Gᵉ → type-Groupᵉ Gᵉ
  conjugation-Groupᵉ xᵉ = map-equivᵉ (equiv-conjugation-Groupᵉ xᵉ)

  equiv-conjugation-Group'ᵉ : (xᵉ : type-Groupᵉ Gᵉ) → type-Groupᵉ Gᵉ ≃ᵉ type-Groupᵉ Gᵉ
  equiv-conjugation-Group'ᵉ xᵉ =
    equiv-mul-Group'ᵉ Gᵉ xᵉ ∘eᵉ equiv-mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ)

  conjugation-Group'ᵉ : (xᵉ : type-Groupᵉ Gᵉ) → type-Groupᵉ Gᵉ → type-Groupᵉ Gᵉ
  conjugation-Group'ᵉ xᵉ = map-equivᵉ (equiv-conjugation-Group'ᵉ xᵉ)
```

### The conjugation action of a group on itself

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  conjugation-action-Groupᵉ : action-Groupᵉ Gᵉ l1ᵉ
  pr1ᵉ conjugation-action-Groupᵉ = set-Groupᵉ Gᵉ
  pr1ᵉ (pr2ᵉ conjugation-action-Groupᵉ) gᵉ = equiv-conjugation-Groupᵉ Gᵉ gᵉ
  pr2ᵉ (pr2ᵉ conjugation-action-Groupᵉ) {gᵉ} {hᵉ} =
    eq-htpy-equivᵉ
      ( λ xᵉ →
        ( ap-mul-Groupᵉ Gᵉ
          ( associative-mul-Groupᵉ Gᵉ gᵉ hᵉ xᵉ)
          ( distributive-inv-mul-Groupᵉ Gᵉ)) ∙ᵉ
        ( invᵉ
          ( associative-mul-Groupᵉ Gᵉ
            ( mul-Groupᵉ Gᵉ gᵉ (mul-Groupᵉ Gᵉ hᵉ xᵉ))
            ( inv-Groupᵉ Gᵉ hᵉ)
            ( inv-Groupᵉ Gᵉ gᵉ))) ∙ᵉ
        ( apᵉ
          ( mul-Group'ᵉ Gᵉ (inv-Groupᵉ Gᵉ gᵉ))
          ( associative-mul-Groupᵉ Gᵉ gᵉ
            ( mul-Groupᵉ Gᵉ hᵉ xᵉ)
            ( inv-Groupᵉ Gᵉ hᵉ))))
```

### The predicate on subsets of groups of being closed under conjugation

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Sᵉ : subset-Groupᵉ l2ᵉ Gᵉ)
  where

  is-closed-under-conjugation-subset-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-conjugation-subset-Groupᵉ =
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    is-in-subtypeᵉ Sᵉ yᵉ → is-in-subtypeᵉ Sᵉ (conjugation-Groupᵉ Gᵉ xᵉ yᵉ)
```

## Properties

### Laws for conjugation and multiplication

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  conjugation-unit-Groupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) → conjugation-Groupᵉ Gᵉ xᵉ (unit-Groupᵉ Gᵉ) ＝ᵉ unit-Groupᵉ Gᵉ
  conjugation-unit-Groupᵉ xᵉ =
    ( apᵉ (mul-Group'ᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ)) (right-unit-law-mul-Groupᵉ Gᵉ xᵉ)) ∙ᵉ
    ( right-inverse-law-mul-Groupᵉ Gᵉ xᵉ)

  compute-conjugation-unit-Groupᵉ :
    conjugation-Groupᵉ Gᵉ (unit-Groupᵉ Gᵉ) ~ᵉ idᵉ
  compute-conjugation-unit-Groupᵉ xᵉ =
    ( ap-mul-Groupᵉ Gᵉ (left-unit-law-mul-Groupᵉ Gᵉ xᵉ) (inv-unit-Groupᵉ Gᵉ)) ∙ᵉ
    ( right-unit-law-mul-Groupᵉ Gᵉ xᵉ)

  compute-conjugation-mul-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    conjugation-Groupᵉ Gᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ) ~ᵉ
    (conjugation-Groupᵉ Gᵉ xᵉ ∘ᵉ conjugation-Groupᵉ Gᵉ yᵉ)
  compute-conjugation-mul-Groupᵉ xᵉ yᵉ zᵉ =
    ( ap-mul-Groupᵉ Gᵉ
      ( associative-mul-Groupᵉ Gᵉ xᵉ yᵉ zᵉ)
      ( distributive-inv-mul-Groupᵉ Gᵉ)) ∙ᵉ
    ( invᵉ
      ( associative-mul-Groupᵉ Gᵉ
        ( mul-Groupᵉ Gᵉ xᵉ (mul-Groupᵉ Gᵉ yᵉ zᵉ))
        ( inv-Groupᵉ Gᵉ yᵉ)
        ( inv-Groupᵉ Gᵉ xᵉ))) ∙ᵉ
    ( apᵉ
      ( mul-Group'ᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ))
      ( associative-mul-Groupᵉ Gᵉ xᵉ (mul-Groupᵉ Gᵉ yᵉ zᵉ) (inv-Groupᵉ Gᵉ yᵉ)))

  compute-conjugation-mul-Group'ᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    conjugation-Group'ᵉ Gᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ) ~ᵉ
    ( conjugation-Group'ᵉ Gᵉ yᵉ ∘ᵉ conjugation-Group'ᵉ Gᵉ xᵉ)
  compute-conjugation-mul-Group'ᵉ xᵉ yᵉ zᵉ =
    ( apᵉ
      ( mul-Group'ᵉ Gᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ))
      ( ( apᵉ (mul-Group'ᵉ Gᵉ zᵉ) (distributive-inv-mul-Groupᵉ Gᵉ)) ∙ᵉ
        ( associative-mul-Groupᵉ Gᵉ
          ( inv-Groupᵉ Gᵉ yᵉ)
          ( inv-Groupᵉ Gᵉ xᵉ)
          ( zᵉ)))) ∙ᵉ
    ( associative-mul-Groupᵉ Gᵉ
      ( inv-Groupᵉ Gᵉ yᵉ)
      ( left-div-Groupᵉ Gᵉ xᵉ zᵉ)
      ( mul-Groupᵉ Gᵉ xᵉ yᵉ)) ∙ᵉ
    ( apᵉ
      ( left-div-Groupᵉ Gᵉ yᵉ)
      ( invᵉ (associative-mul-Groupᵉ Gᵉ (left-div-Groupᵉ Gᵉ xᵉ zᵉ) xᵉ yᵉ))) ∙ᵉ
    ( invᵉ
      ( associative-mul-Groupᵉ Gᵉ
        ( inv-Groupᵉ Gᵉ yᵉ)
        ( conjugation-Group'ᵉ Gᵉ xᵉ zᵉ)
        ( yᵉ)))

  htpy-conjugation-Groupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) →
    conjugation-Group'ᵉ Gᵉ xᵉ ~ᵉ conjugation-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ)
  htpy-conjugation-Groupᵉ xᵉ yᵉ =
    apᵉ
      ( mul-Groupᵉ Gᵉ (mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ) yᵉ))
      ( invᵉ (inv-inv-Groupᵉ Gᵉ xᵉ))

  htpy-conjugation-Group'ᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) →
    conjugation-Groupᵉ Gᵉ xᵉ ~ᵉ conjugation-Group'ᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ)
  htpy-conjugation-Group'ᵉ xᵉ yᵉ =
    apᵉ
      ( mul-Group'ᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ))
      ( apᵉ (mul-Group'ᵉ Gᵉ yᵉ) (invᵉ (inv-inv-Groupᵉ Gᵉ xᵉ)))

  right-conjugation-law-mul-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ) (conjugation-Groupᵉ Gᵉ xᵉ yᵉ) ＝ᵉ
    right-div-Groupᵉ Gᵉ yᵉ xᵉ
  right-conjugation-law-mul-Groupᵉ xᵉ yᵉ =
    invᵉ
      ( transpose-eq-mul-Group'ᵉ Gᵉ
        ( invᵉ (associative-mul-Groupᵉ Gᵉ xᵉ yᵉ (inv-Groupᵉ Gᵉ xᵉ))))

  right-conjugation-law-mul-Group'ᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    mul-Groupᵉ Gᵉ xᵉ (conjugation-Group'ᵉ Gᵉ xᵉ yᵉ) ＝ᵉ
    mul-Groupᵉ Gᵉ yᵉ xᵉ
  right-conjugation-law-mul-Group'ᵉ xᵉ yᵉ =
    ( apᵉ
      ( mul-Groupᵉ Gᵉ xᵉ)
      ( associative-mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ) yᵉ xᵉ)) ∙ᵉ
    ( is-section-left-div-Groupᵉ Gᵉ xᵉ (mul-Groupᵉ Gᵉ yᵉ xᵉ))

  left-conjugation-law-mul-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    mul-Groupᵉ Gᵉ (conjugation-Groupᵉ Gᵉ xᵉ yᵉ) xᵉ ＝ᵉ mul-Groupᵉ Gᵉ xᵉ yᵉ
  left-conjugation-law-mul-Groupᵉ xᵉ yᵉ =
    ( associative-mul-Groupᵉ Gᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ) (inv-Groupᵉ Gᵉ xᵉ) xᵉ) ∙ᵉ
    ( apᵉ
      ( mul-Groupᵉ Gᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ))
      ( left-inverse-law-mul-Groupᵉ Gᵉ xᵉ)) ∙ᵉ
    ( right-unit-law-mul-Groupᵉ Gᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ))

  left-conjugation-law-mul-Group'ᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    mul-Groupᵉ Gᵉ (conjugation-Group'ᵉ Gᵉ xᵉ yᵉ) (inv-Groupᵉ Gᵉ xᵉ) ＝ᵉ
    left-div-Groupᵉ Gᵉ xᵉ yᵉ
  left-conjugation-law-mul-Group'ᵉ xᵉ yᵉ =
    is-retraction-right-div-Groupᵉ Gᵉ xᵉ (mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ) yᵉ)

  distributive-conjugation-mul-Groupᵉ :
    (xᵉ yᵉ zᵉ : type-Groupᵉ Gᵉ) →
    conjugation-Groupᵉ Gᵉ xᵉ (mul-Groupᵉ Gᵉ yᵉ zᵉ) ＝ᵉ
    mul-Groupᵉ Gᵉ (conjugation-Groupᵉ Gᵉ xᵉ yᵉ) (conjugation-Groupᵉ Gᵉ xᵉ zᵉ)
  distributive-conjugation-mul-Groupᵉ xᵉ yᵉ zᵉ =
    ( apᵉ
      ( mul-Group'ᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ))
      ( ( invᵉ (associative-mul-Groupᵉ Gᵉ xᵉ yᵉ zᵉ)) ∙ᵉ
        ( apᵉ
          ( mul-Group'ᵉ Gᵉ zᵉ)
          ( invᵉ (is-section-right-div-Groupᵉ Gᵉ xᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ)))) ∙ᵉ
        ( associative-mul-Groupᵉ Gᵉ
          ( conjugation-Groupᵉ Gᵉ xᵉ yᵉ)
          ( xᵉ)
          ( zᵉ)))) ∙ᵉ
    ( associative-mul-Groupᵉ Gᵉ
      ( conjugation-Groupᵉ Gᵉ xᵉ yᵉ)
      ( mul-Groupᵉ Gᵉ xᵉ zᵉ)
      ( inv-Groupᵉ Gᵉ xᵉ))

  conjugation-inv-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    conjugation-Groupᵉ Gᵉ xᵉ (inv-Groupᵉ Gᵉ yᵉ) ＝ᵉ
    inv-Groupᵉ Gᵉ (conjugation-Groupᵉ Gᵉ xᵉ yᵉ)
  conjugation-inv-Groupᵉ xᵉ yᵉ =
    ( invᵉ (inv-inv-Groupᵉ Gᵉ (conjugation-Groupᵉ Gᵉ xᵉ (inv-Groupᵉ Gᵉ yᵉ)))) ∙ᵉ
    ( apᵉ
      ( inv-Groupᵉ Gᵉ)
      ( ( distributive-inv-mul-Groupᵉ Gᵉ) ∙ᵉ
        ( ap-mul-Groupᵉ Gᵉ
          ( inv-inv-Groupᵉ Gᵉ xᵉ)
          ( ( distributive-inv-mul-Groupᵉ Gᵉ) ∙ᵉ
            ( apᵉ
              ( mul-Group'ᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ))
              ( inv-inv-Groupᵉ Gᵉ yᵉ)))) ∙ᵉ
        ( invᵉ (associative-mul-Groupᵉ Gᵉ xᵉ yᵉ ( inv-Groupᵉ Gᵉ xᵉ)))))

  conjugation-inv-Group'ᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    conjugation-Group'ᵉ Gᵉ xᵉ (inv-Groupᵉ Gᵉ yᵉ) ＝ᵉ
    inv-Groupᵉ Gᵉ (conjugation-Group'ᵉ Gᵉ xᵉ yᵉ)
  conjugation-inv-Group'ᵉ xᵉ yᵉ =
    ( apᵉ (mul-Group'ᵉ Gᵉ xᵉ) (invᵉ (distributive-inv-mul-Groupᵉ Gᵉ))) ∙ᵉ
    ( apᵉ
      ( mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ (mul-Groupᵉ Gᵉ yᵉ xᵉ)))
      ( invᵉ (inv-inv-Groupᵉ Gᵉ xᵉ))) ∙ᵉ
    ( invᵉ
      ( distributive-inv-mul-Groupᵉ Gᵉ)) ∙ᵉ
    ( apᵉ
      ( inv-Groupᵉ Gᵉ)
      ( invᵉ (associative-mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ) yᵉ xᵉ)))

  conjugation-left-div-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    conjugation-Groupᵉ Gᵉ xᵉ (left-div-Groupᵉ Gᵉ xᵉ yᵉ) ＝ᵉ
    right-div-Groupᵉ Gᵉ yᵉ xᵉ
  conjugation-left-div-Groupᵉ xᵉ yᵉ =
    apᵉ (λ yᵉ → right-div-Groupᵉ Gᵉ yᵉ xᵉ) (is-section-left-div-Groupᵉ Gᵉ xᵉ yᵉ)

  conjugation-left-div-Group'ᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    conjugation-Groupᵉ Gᵉ yᵉ (left-div-Groupᵉ Gᵉ xᵉ yᵉ) ＝ᵉ
    right-div-Groupᵉ Gᵉ yᵉ xᵉ
  conjugation-left-div-Group'ᵉ xᵉ yᵉ =
    ( apᵉ
      ( λ zᵉ → right-div-Groupᵉ Gᵉ zᵉ yᵉ)
      ( invᵉ (associative-mul-Groupᵉ Gᵉ yᵉ (inv-Groupᵉ Gᵉ xᵉ) yᵉ))) ∙ᵉ
    ( is-retraction-right-div-Groupᵉ Gᵉ yᵉ (right-div-Groupᵉ Gᵉ yᵉ xᵉ))

  conjugation-right-div-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    conjugation-Group'ᵉ Gᵉ yᵉ (right-div-Groupᵉ Gᵉ xᵉ yᵉ) ＝ᵉ
    left-div-Groupᵉ Gᵉ yᵉ xᵉ
  conjugation-right-div-Groupᵉ xᵉ yᵉ =
    ( associative-mul-Groupᵉ Gᵉ
      ( inv-Groupᵉ Gᵉ yᵉ)
      ( right-div-Groupᵉ Gᵉ xᵉ yᵉ)
      ( yᵉ)) ∙ᵉ
    ( apᵉ (left-div-Groupᵉ Gᵉ yᵉ) (is-section-right-div-Groupᵉ Gᵉ yᵉ xᵉ))

  conjugation-right-div-Group'ᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    conjugation-Group'ᵉ Gᵉ xᵉ (right-div-Groupᵉ Gᵉ xᵉ yᵉ) ＝ᵉ
    left-div-Groupᵉ Gᵉ yᵉ xᵉ
  conjugation-right-div-Group'ᵉ xᵉ yᵉ =
    apᵉ (mul-Group'ᵉ Gᵉ xᵉ) (is-retraction-left-div-Groupᵉ Gᵉ xᵉ (inv-Groupᵉ Gᵉ yᵉ))

  is-section-conjugation-inv-Groupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) →
    ( conjugation-Groupᵉ Gᵉ xᵉ ∘ᵉ conjugation-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ)) ~ᵉ idᵉ
  is-section-conjugation-inv-Groupᵉ xᵉ yᵉ =
    ( apᵉ
      ( mul-Group'ᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ))
      ( ( apᵉ (mul-Groupᵉ Gᵉ xᵉ) (associative-mul-Groupᵉ Gᵉ _ _ _)) ∙ᵉ
        ( is-section-left-div-Groupᵉ Gᵉ xᵉ
          ( right-div-Groupᵉ Gᵉ yᵉ (inv-Groupᵉ Gᵉ xᵉ))))) ∙ᵉ
    ( is-section-right-div-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ) yᵉ)

  is-retraction-conjugation-inv-Groupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) →
    ( conjugation-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ) ∘ᵉ conjugation-Groupᵉ Gᵉ xᵉ) ~ᵉ idᵉ
  is-retraction-conjugation-inv-Groupᵉ xᵉ yᵉ =
    ( apᵉ
      ( mul-Group'ᵉ Gᵉ (inv-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ)))
      ( ( apᵉ (mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ)) (associative-mul-Groupᵉ Gᵉ _ _ _)) ∙ᵉ
        ( is-retraction-left-div-Groupᵉ Gᵉ xᵉ
          ( right-div-Groupᵉ Gᵉ yᵉ xᵉ)))) ∙ᵉ
    ( is-retraction-right-div-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ) yᵉ)

  transpose-eq-conjugation-Groupᵉ :
    {xᵉ yᵉ zᵉ : type-Groupᵉ Gᵉ} →
    yᵉ ＝ᵉ conjugation-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ) zᵉ → conjugation-Groupᵉ Gᵉ xᵉ yᵉ ＝ᵉ zᵉ
  transpose-eq-conjugation-Groupᵉ {xᵉ} {yᵉ} {zᵉ} =
    eq-transpose-is-sectionᵉ
      ( conjugation-Groupᵉ Gᵉ xᵉ)
      ( conjugation-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ))
      ( is-section-conjugation-inv-Groupᵉ xᵉ)

  transpose-eq-conjugation-Group'ᵉ :
    {xᵉ yᵉ zᵉ : type-Groupᵉ Gᵉ} →
    conjugation-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ) yᵉ ＝ᵉ zᵉ → yᵉ ＝ᵉ conjugation-Groupᵉ Gᵉ xᵉ zᵉ
  transpose-eq-conjugation-Group'ᵉ {xᵉ} {yᵉ} {zᵉ} =
    eq-transpose-is-section'ᵉ
      ( conjugation-Groupᵉ Gᵉ xᵉ)
      ( conjugation-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ))
      ( is-section-conjugation-inv-Groupᵉ xᵉ)

  transpose-eq-conjugation-inv-Groupᵉ :
    {xᵉ yᵉ zᵉ : type-Groupᵉ Gᵉ} →
    yᵉ ＝ᵉ conjugation-Groupᵉ Gᵉ xᵉ zᵉ → conjugation-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ) yᵉ ＝ᵉ zᵉ
  transpose-eq-conjugation-inv-Groupᵉ {xᵉ} {yᵉ} {zᵉ} =
    eq-transpose-is-retractionᵉ
      ( conjugation-Groupᵉ Gᵉ xᵉ)
      ( conjugation-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ))
      ( is-retraction-conjugation-inv-Groupᵉ xᵉ)

  transpose-eq-conjugation-inv-Group'ᵉ :
    {xᵉ yᵉ zᵉ : type-Groupᵉ Gᵉ} →
    conjugation-Groupᵉ Gᵉ xᵉ yᵉ ＝ᵉ zᵉ → yᵉ ＝ᵉ conjugation-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ) zᵉ
  transpose-eq-conjugation-inv-Group'ᵉ {xᵉ} {yᵉ} {zᵉ} =
    eq-transpose-is-retraction'ᵉ
      ( conjugation-Groupᵉ Gᵉ xᵉ)
      ( conjugation-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ))
      ( is-retraction-conjugation-inv-Groupᵉ xᵉ)
```

### Conjugation by `x` is an automorphism of `G`

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  conjugation-hom-Groupᵉ : type-Groupᵉ Gᵉ → hom-Groupᵉ Gᵉ Gᵉ
  pr1ᵉ (conjugation-hom-Groupᵉ xᵉ) = conjugation-Groupᵉ Gᵉ xᵉ
  pr2ᵉ (conjugation-hom-Groupᵉ xᵉ) = distributive-conjugation-mul-Groupᵉ Gᵉ xᵉ _ _

  conjugation-equiv-Groupᵉ : type-Groupᵉ Gᵉ → equiv-Groupᵉ Gᵉ Gᵉ
  pr1ᵉ (conjugation-equiv-Groupᵉ xᵉ) = equiv-conjugation-Groupᵉ Gᵉ xᵉ
  pr2ᵉ (conjugation-equiv-Groupᵉ xᵉ) = distributive-conjugation-mul-Groupᵉ Gᵉ xᵉ _ _

  conjugation-iso-Groupᵉ : type-Groupᵉ Gᵉ → iso-Groupᵉ Gᵉ Gᵉ
  conjugation-iso-Groupᵉ xᵉ = iso-equiv-Groupᵉ Gᵉ Gᵉ (conjugation-equiv-Groupᵉ xᵉ)

  preserves-integer-powers-conjugation-Groupᵉ :
    (kᵉ : ℤᵉ) (gᵉ xᵉ : type-Groupᵉ Gᵉ) →
    conjugation-Groupᵉ Gᵉ gᵉ (integer-power-Groupᵉ Gᵉ kᵉ xᵉ) ＝ᵉ
    integer-power-Groupᵉ Gᵉ kᵉ (conjugation-Groupᵉ Gᵉ gᵉ xᵉ)
  preserves-integer-powers-conjugation-Groupᵉ kᵉ gᵉ =
    preserves-integer-powers-hom-Groupᵉ Gᵉ Gᵉ (conjugation-hom-Groupᵉ gᵉ) kᵉ
```

### Any group homomorphism preserves conjugation

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  preserves-conjugation-hom-Groupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (conjugation-Groupᵉ Gᵉ xᵉ yᵉ) ＝ᵉ
    conjugation-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ) (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ yᵉ)
  preserves-conjugation-hom-Groupᵉ =
    ( preserves-right-div-hom-Groupᵉ Gᵉ Hᵉ fᵉ) ∙ᵉ
    ( apᵉ (mul-Group'ᵉ Hᵉ _) (preserves-mul-hom-Groupᵉ Gᵉ Hᵉ fᵉ))
```