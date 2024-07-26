# The dihedral group construction

```agda
module group-theory.dihedral-group-constructionᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-coproduct-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Whenᵉ `A`ᵉ isᵉ anᵉ abelianᵉ group,ᵉ weᵉ canᵉ putᵉ aᵉ groupᵉ structureᵉ onᵉ theᵉ disjointᵉ unionᵉ
`A+A`,ᵉ whichᵉ specializesᵉ to theᵉ dihedralᵉ groupsᵉ whenᵉ weᵉ takeᵉ `Aᵉ :=ᵉ ℤ/k`.ᵉ

## Definitions

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  set-dihedral-group-Abᵉ : Setᵉ lᵉ
  set-dihedral-group-Abᵉ = coproduct-Setᵉ (set-Abᵉ Aᵉ) (set-Abᵉ Aᵉ)

  type-dihedral-group-Abᵉ : UUᵉ lᵉ
  type-dihedral-group-Abᵉ = type-Setᵉ set-dihedral-group-Abᵉ

  is-set-type-dihedral-group-Abᵉ : is-setᵉ type-dihedral-group-Abᵉ
  is-set-type-dihedral-group-Abᵉ = is-set-type-Setᵉ set-dihedral-group-Abᵉ

  unit-dihedral-group-Abᵉ : type-dihedral-group-Abᵉ
  unit-dihedral-group-Abᵉ = inlᵉ (zero-Abᵉ Aᵉ)

  mul-dihedral-group-Abᵉ :
    (xᵉ yᵉ : type-dihedral-group-Abᵉ) → type-dihedral-group-Abᵉ
  mul-dihedral-group-Abᵉ (inlᵉ xᵉ) (inlᵉ yᵉ) = inlᵉ (add-Abᵉ Aᵉ xᵉ yᵉ)
  mul-dihedral-group-Abᵉ (inlᵉ xᵉ) (inrᵉ yᵉ) = inrᵉ (add-Abᵉ Aᵉ (neg-Abᵉ Aᵉ xᵉ) yᵉ)
  mul-dihedral-group-Abᵉ (inrᵉ xᵉ) (inlᵉ yᵉ) = inrᵉ (add-Abᵉ Aᵉ xᵉ yᵉ)
  mul-dihedral-group-Abᵉ (inrᵉ xᵉ) (inrᵉ yᵉ) = inlᵉ (add-Abᵉ Aᵉ (neg-Abᵉ Aᵉ xᵉ) yᵉ)

  inv-dihedral-group-Abᵉ : type-dihedral-group-Abᵉ → type-dihedral-group-Abᵉ
  inv-dihedral-group-Abᵉ (inlᵉ xᵉ) = inlᵉ (neg-Abᵉ Aᵉ xᵉ)
  inv-dihedral-group-Abᵉ (inrᵉ xᵉ) = inrᵉ xᵉ

  associative-mul-dihedral-group-Abᵉ :
    (xᵉ yᵉ zᵉ : type-dihedral-group-Abᵉ) →
    (mul-dihedral-group-Abᵉ (mul-dihedral-group-Abᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    (mul-dihedral-group-Abᵉ xᵉ (mul-dihedral-group-Abᵉ yᵉ zᵉ))
  associative-mul-dihedral-group-Abᵉ (inlᵉ xᵉ) (inlᵉ yᵉ) (inlᵉ zᵉ) =
    apᵉ inlᵉ (associative-add-Abᵉ Aᵉ xᵉ yᵉ zᵉ)
  associative-mul-dihedral-group-Abᵉ (inlᵉ xᵉ) (inlᵉ yᵉ) (inrᵉ zᵉ) =
    apᵉ
      ( inrᵉ)
      ( ( apᵉ (add-Ab'ᵉ Aᵉ zᵉ) (distributive-neg-add-Abᵉ Aᵉ xᵉ yᵉ)) ∙ᵉ
        ( associative-add-Abᵉ Aᵉ (neg-Abᵉ Aᵉ xᵉ) (neg-Abᵉ Aᵉ yᵉ) zᵉ))
  associative-mul-dihedral-group-Abᵉ (inlᵉ xᵉ) (inrᵉ yᵉ) (inlᵉ zᵉ) =
    apᵉ inrᵉ (associative-add-Abᵉ Aᵉ (neg-Abᵉ Aᵉ xᵉ) yᵉ zᵉ)
  associative-mul-dihedral-group-Abᵉ (inlᵉ xᵉ) (inrᵉ yᵉ) (inrᵉ zᵉ) =
    apᵉ
      ( inlᵉ)
      ( ( apᵉ
          ( add-Ab'ᵉ Aᵉ zᵉ)
          ( ( distributive-neg-add-Abᵉ Aᵉ (neg-Abᵉ Aᵉ xᵉ) yᵉ) ∙ᵉ
            ( apᵉ (add-Ab'ᵉ Aᵉ (neg-Abᵉ Aᵉ yᵉ)) (neg-neg-Abᵉ Aᵉ xᵉ)))) ∙ᵉ
        ( associative-add-Abᵉ Aᵉ xᵉ (neg-Abᵉ Aᵉ yᵉ) zᵉ))
  associative-mul-dihedral-group-Abᵉ (inrᵉ xᵉ) (inlᵉ yᵉ) (inlᵉ zᵉ) =
    apᵉ inrᵉ (associative-add-Abᵉ Aᵉ xᵉ yᵉ zᵉ)
  associative-mul-dihedral-group-Abᵉ (inrᵉ xᵉ) (inlᵉ yᵉ) (inrᵉ zᵉ) =
    apᵉ
      ( inlᵉ)
      ( ( apᵉ (add-Ab'ᵉ Aᵉ zᵉ) (distributive-neg-add-Abᵉ Aᵉ xᵉ yᵉ)) ∙ᵉ
        ( associative-add-Abᵉ Aᵉ (neg-Abᵉ Aᵉ xᵉ) (neg-Abᵉ Aᵉ yᵉ) zᵉ))
  associative-mul-dihedral-group-Abᵉ (inrᵉ xᵉ) (inrᵉ yᵉ) (inlᵉ zᵉ) =
    apᵉ inlᵉ (associative-add-Abᵉ Aᵉ (neg-Abᵉ Aᵉ xᵉ) yᵉ zᵉ)
  associative-mul-dihedral-group-Abᵉ (inrᵉ xᵉ) (inrᵉ yᵉ) (inrᵉ zᵉ) =
    apᵉ
      ( inrᵉ)
      ( ( apᵉ
          ( add-Ab'ᵉ Aᵉ zᵉ)
          ( ( distributive-neg-add-Abᵉ Aᵉ (neg-Abᵉ Aᵉ xᵉ) yᵉ) ∙ᵉ
            ( apᵉ (add-Ab'ᵉ Aᵉ (neg-Abᵉ Aᵉ yᵉ)) (neg-neg-Abᵉ Aᵉ xᵉ)))) ∙ᵉ
        ( associative-add-Abᵉ Aᵉ xᵉ (neg-Abᵉ Aᵉ yᵉ) zᵉ))

  left-unit-law-mul-dihedral-group-Abᵉ :
    (xᵉ : type-dihedral-group-Abᵉ) →
    (mul-dihedral-group-Abᵉ unit-dihedral-group-Abᵉ xᵉ) ＝ᵉ xᵉ
  left-unit-law-mul-dihedral-group-Abᵉ (inlᵉ xᵉ) =
    apᵉ inlᵉ (left-unit-law-add-Abᵉ Aᵉ xᵉ)
  left-unit-law-mul-dihedral-group-Abᵉ (inrᵉ xᵉ) =
    apᵉ inrᵉ (apᵉ (add-Ab'ᵉ Aᵉ xᵉ) (neg-zero-Abᵉ Aᵉ) ∙ᵉ left-unit-law-add-Abᵉ Aᵉ xᵉ)

  right-unit-law-mul-dihedral-group-Abᵉ :
    (xᵉ : type-dihedral-group-Abᵉ) →
    (mul-dihedral-group-Abᵉ xᵉ unit-dihedral-group-Abᵉ) ＝ᵉ xᵉ
  right-unit-law-mul-dihedral-group-Abᵉ (inlᵉ xᵉ) =
    apᵉ inlᵉ (right-unit-law-add-Abᵉ Aᵉ xᵉ)
  right-unit-law-mul-dihedral-group-Abᵉ (inrᵉ xᵉ) =
    apᵉ inrᵉ (right-unit-law-add-Abᵉ Aᵉ xᵉ)

  left-inverse-law-mul-dihedral-group-Abᵉ :
    (xᵉ : type-dihedral-group-Abᵉ) →
    ( mul-dihedral-group-Abᵉ (inv-dihedral-group-Abᵉ xᵉ) xᵉ) ＝ᵉ
    ( unit-dihedral-group-Abᵉ)
  left-inverse-law-mul-dihedral-group-Abᵉ (inlᵉ xᵉ) =
    apᵉ inlᵉ (left-inverse-law-add-Abᵉ Aᵉ xᵉ)
  left-inverse-law-mul-dihedral-group-Abᵉ (inrᵉ xᵉ) =
    apᵉ inlᵉ (left-inverse-law-add-Abᵉ Aᵉ xᵉ)

  right-inverse-law-mul-dihedral-group-Abᵉ :
    (xᵉ : type-dihedral-group-Abᵉ) →
    ( mul-dihedral-group-Abᵉ xᵉ (inv-dihedral-group-Abᵉ xᵉ)) ＝ᵉ
    ( unit-dihedral-group-Abᵉ)
  right-inverse-law-mul-dihedral-group-Abᵉ (inlᵉ xᵉ) =
    apᵉ inlᵉ (right-inverse-law-add-Abᵉ Aᵉ xᵉ)
  right-inverse-law-mul-dihedral-group-Abᵉ (inrᵉ xᵉ) =
    apᵉ inlᵉ (left-inverse-law-add-Abᵉ Aᵉ xᵉ)

  semigroup-dihedral-group-Abᵉ : Semigroupᵉ lᵉ
  pr1ᵉ semigroup-dihedral-group-Abᵉ = set-dihedral-group-Abᵉ
  pr1ᵉ (pr2ᵉ semigroup-dihedral-group-Abᵉ) = mul-dihedral-group-Abᵉ
  pr2ᵉ (pr2ᵉ semigroup-dihedral-group-Abᵉ) = associative-mul-dihedral-group-Abᵉ

  monoid-dihedral-group-Abᵉ : Monoidᵉ lᵉ
  pr1ᵉ monoid-dihedral-group-Abᵉ = semigroup-dihedral-group-Abᵉ
  pr1ᵉ (pr2ᵉ monoid-dihedral-group-Abᵉ) = unit-dihedral-group-Abᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ monoid-dihedral-group-Abᵉ)) = left-unit-law-mul-dihedral-group-Abᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ monoid-dihedral-group-Abᵉ)) =
    right-unit-law-mul-dihedral-group-Abᵉ

  dihedral-group-Abᵉ : Groupᵉ lᵉ
  pr1ᵉ dihedral-group-Abᵉ = semigroup-dihedral-group-Abᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ dihedral-group-Abᵉ)) = unit-dihedral-group-Abᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ dihedral-group-Abᵉ))) = left-unit-law-mul-dihedral-group-Abᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ dihedral-group-Abᵉ))) = right-unit-law-mul-dihedral-group-Abᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ dihedral-group-Abᵉ)) = inv-dihedral-group-Abᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ dihedral-group-Abᵉ))) =
    left-inverse-law-mul-dihedral-group-Abᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ dihedral-group-Abᵉ))) =
    right-inverse-law-mul-dihedral-group-Abᵉ
```