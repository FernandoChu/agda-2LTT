# The initial pointed type equipped with an automorphism

```agda
module structured-types.initial-pointed-type-equipped-with-automorphismᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterating-automorphismsᵉ
open import foundation.transposition-identifications-along-equivalencesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-types-equipped-with-automorphismsᵉ
```

</details>

## Idea

Weᵉ showᵉ thatᵉ ℤᵉ isᵉ theᵉ initialᵉ pointedᵉ typeᵉ equippedᵉ with anᵉ automorphismᵉ

## Definition

### The type of integers is the intial type equipped with a point and an automorphism

#### The type of integers is a type equipped with a point and an automorphism

```agda
ℤ-Pointed-Type-With-Autᵉ : Pointed-Type-With-Autᵉ lzero
pr1ᵉ (pr1ᵉ ℤ-Pointed-Type-With-Autᵉ) = ℤᵉ
pr2ᵉ (pr1ᵉ ℤ-Pointed-Type-With-Autᵉ) = zero-ℤᵉ
pr2ᵉ ℤ-Pointed-Type-With-Autᵉ = equiv-succ-ℤᵉ
```

#### Construction of a map from ℤ into any type with a point and an automorphism

```agda
map-ℤ-Pointed-Type-With-Autᵉ :
  {lᵉ : Level} (Xᵉ : Pointed-Type-With-Autᵉ lᵉ) →
  ℤᵉ → type-Pointed-Type-With-Autᵉ Xᵉ
map-ℤ-Pointed-Type-With-Autᵉ Xᵉ kᵉ =
  map-iterate-automorphism-ℤᵉ kᵉ
    ( aut-Pointed-Type-With-Autᵉ Xᵉ)
    ( point-Pointed-Type-With-Autᵉ Xᵉ)

preserves-point-map-ℤ-Pointed-Type-With-Autᵉ :
  {lᵉ : Level} (Xᵉ : Pointed-Type-With-Autᵉ lᵉ) →
  ( map-ℤ-Pointed-Type-With-Autᵉ Xᵉ zero-ℤᵉ) ＝ᵉ
  ( point-Pointed-Type-With-Autᵉ Xᵉ)
preserves-point-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ = reflᵉ

preserves-aut-map-ℤ-Pointed-Type-With-Autᵉ :
  {lᵉ : Level} (Xᵉ : Pointed-Type-With-Autᵉ lᵉ) (kᵉ : ℤᵉ) →
  ( map-ℤ-Pointed-Type-With-Autᵉ Xᵉ (succ-ℤᵉ kᵉ)) ＝ᵉ
  ( map-aut-Pointed-Type-With-Autᵉ Xᵉ
    ( map-ℤ-Pointed-Type-With-Autᵉ Xᵉ kᵉ))
preserves-aut-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ kᵉ =
  iterate-automorphism-succ-ℤ'ᵉ kᵉ
    ( aut-Pointed-Type-With-Autᵉ Xᵉ)
    ( point-Pointed-Type-With-Autᵉ Xᵉ)

hom-ℤ-Pointed-Type-With-Autᵉ :
  {lᵉ : Level} (Xᵉ : Pointed-Type-With-Autᵉ lᵉ) →
  hom-Pointed-Type-With-Autᵉ ℤ-Pointed-Type-With-Autᵉ Xᵉ
hom-ℤ-Pointed-Type-With-Autᵉ Xᵉ =
  pairᵉ
    ( map-ℤ-Pointed-Type-With-Autᵉ Xᵉ)
    ( pairᵉ
      ( preserves-point-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ)
      ( preserves-aut-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ))
```

#### The map previously constructed is unique

```agda
htpy-map-ℤ-Pointed-Type-With-Autᵉ :
  {lᵉ : Level} (Xᵉ : Pointed-Type-With-Autᵉ lᵉ)
  (hᵉ : hom-Pointed-Type-With-Autᵉ ℤ-Pointed-Type-With-Autᵉ Xᵉ) →
  map-ℤ-Pointed-Type-With-Autᵉ Xᵉ ~ᵉ
  map-hom-Pointed-Type-With-Autᵉ ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ
htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inlᵉ zero-ℕᵉ) =
  map-eq-transpose-equiv-invᵉ
    ( aut-Pointed-Type-With-Autᵉ Xᵉ)
    ( ( invᵉ
        ( preserves-point-map-hom-Pointed-Type-With-Autᵉ ℤ-Pointed-Type-With-Autᵉ
          Xᵉ hᵉ)) ∙ᵉ
      ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ ℤ-Pointed-Type-With-Autᵉ
        Xᵉ hᵉ neg-one-ℤᵉ))
htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inlᵉ (succ-ℕᵉ kᵉ)) =
  map-eq-transpose-equiv-invᵉ
    ( aut-Pointed-Type-With-Autᵉ Xᵉ)
    ( ( htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inlᵉ kᵉ)) ∙ᵉ
      ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ ℤ-Pointed-Type-With-Autᵉ
        Xᵉ hᵉ (inlᵉ (succ-ℕᵉ kᵉ))))
htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inrᵉ (inlᵉ starᵉ)) =
  invᵉ
    ( preserves-point-map-hom-Pointed-Type-With-Autᵉ ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ)
htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) =
  ( apᵉ
    ( map-aut-Pointed-Type-With-Autᵉ Xᵉ)
    ( htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inrᵉ (inlᵉ starᵉ)))) ∙ᵉ
  ( invᵉ
    ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ ℤ-Pointed-Type-With-Autᵉ
      Xᵉ hᵉ (inrᵉ (inlᵉ starᵉ))))
htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ))) =
  ( apᵉ
    ( map-aut-Pointed-Type-With-Autᵉ Xᵉ)
    ( htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inrᵉ (inrᵉ kᵉ)))) ∙ᵉ
  ( invᵉ
    ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ
      ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inrᵉ (inrᵉ kᵉ))))

coh-point-htpy-map-ℤ-Pointed-Type-With-Autᵉ :
  {lᵉ : Level} (Xᵉ : Pointed-Type-With-Autᵉ lᵉ)
  (hᵉ : hom-Pointed-Type-With-Autᵉ ℤ-Pointed-Type-With-Autᵉ Xᵉ) →
  ( preserves-point-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ) ＝ᵉ
  ( ( htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ zero-ℤᵉ) ∙ᵉ
    ( preserves-point-map-hom-Pointed-Type-With-Autᵉ
      ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ))
coh-point-htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ =
  invᵉ
    ( left-invᵉ
      ( preserves-point-map-hom-Pointed-Type-With-Autᵉ
        ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ))

coh-aut-htpy-map-ℤ-Pointed-Type-With-Autᵉ :
  {lᵉ : Level} (Xᵉ : Pointed-Type-With-Autᵉ lᵉ)
  (hᵉ : hom-Pointed-Type-With-Autᵉ ℤ-Pointed-Type-With-Autᵉ Xᵉ)
  (kᵉ : ℤᵉ) →
  ( ( preserves-aut-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ kᵉ) ∙ᵉ
    ( apᵉ
      ( map-aut-Pointed-Type-With-Autᵉ Xᵉ)
      ( htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ kᵉ))) ＝ᵉ
  ( ( htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (succ-ℤᵉ kᵉ)) ∙ᵉ
    ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ
      ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ kᵉ))
coh-aut-htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inlᵉ zero-ℕᵉ) =
  invᵉ
    ( left-transpose-eq-concatᵉ
      ( is-section-map-inv-equivᵉ
        ( aut-Pointed-Type-With-Autᵉ Xᵉ)
        ( point-Pointed-Type-With-Autᵉ Xᵉ))
      ( ( htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ zero-ℤᵉ) ∙ᵉ
        ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ
          ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ neg-one-ℤᵉ))
      ( apᵉ
        ( map-equivᵉ (aut-Pointed-Type-With-Autᵉ Xᵉ))
        ( htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ neg-one-ℤᵉ))
      ( triangle-eq-transpose-equiv-invᵉ
        ( aut-Pointed-Type-With-Autᵉ Xᵉ)
        ( ( invᵉ
            ( preserves-point-map-hom-Pointed-Type-With-Autᵉ
              ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ)) ∙ᵉ
          ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ
            ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ neg-one-ℤᵉ))))
coh-aut-htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inlᵉ (succ-ℕᵉ kᵉ)) =
  invᵉ
    ( left-transpose-eq-concatᵉ
      ( is-section-map-inv-equivᵉ
        ( aut-Pointed-Type-With-Autᵉ Xᵉ)
        ( map-ℤ-Pointed-Type-With-Autᵉ Xᵉ (inlᵉ kᵉ)))
      ( ( htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inlᵉ kᵉ)) ∙ᵉ
        ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ
          ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inlᵉ (succ-ℕᵉ kᵉ))))
      ( apᵉ
        ( map-equivᵉ (aut-Pointed-Type-With-Autᵉ Xᵉ))
        ( htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inlᵉ (succ-ℕᵉ kᵉ))))
      ( triangle-eq-transpose-equiv-invᵉ
        ( aut-Pointed-Type-With-Autᵉ Xᵉ)
        ( ( htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inlᵉ kᵉ)) ∙ᵉ
          ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ
            ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inlᵉ (succ-ℕᵉ kᵉ))))))
coh-aut-htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inrᵉ (inlᵉ starᵉ)) =
  ( invᵉ right-unitᵉ) ∙ᵉ
  ( ( apᵉ
      ( concatᵉ
        ( apᵉ
          ( map-aut-Pointed-Type-With-Autᵉ Xᵉ)
          ( htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ zero-ℤᵉ))
        ( map-aut-Pointed-Type-With-Autᵉ Xᵉ
          ( map-hom-Pointed-Type-With-Autᵉ
            ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ zero-ℤᵉ)))
      ( invᵉ (left-invᵉ
        ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ
          ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ zero-ℤᵉ)))) ∙ᵉ
    ( invᵉ
      ( assocᵉ
        ( apᵉ
          ( map-aut-Pointed-Type-With-Autᵉ Xᵉ)
          ( htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ zero-ℤᵉ))
        ( invᵉ
          ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ
            ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ zero-ℤᵉ))
        ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ
          ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ zero-ℤᵉ))))
coh-aut-htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) =
  ( invᵉ right-unitᵉ) ∙ᵉ
  ( ( apᵉ
      ( concatᵉ
        ( apᵉ
          ( map-aut-Pointed-Type-With-Autᵉ Xᵉ)
          ( htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ one-ℤᵉ))
        ( map-aut-Pointed-Type-With-Autᵉ Xᵉ
          ( map-hom-Pointed-Type-With-Autᵉ
            ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ one-ℤᵉ)))
      ( invᵉ (left-invᵉ
        ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ
          ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ one-ℤᵉ)))) ∙ᵉ
    ( invᵉ
      ( assocᵉ
        ( apᵉ
          ( map-aut-Pointed-Type-With-Autᵉ Xᵉ)
          ( htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ one-ℤᵉ))
        ( invᵉ
          ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ
            ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ one-ℤᵉ))
        ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ
          ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ one-ℤᵉ))))
coh-aut-htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ))) =
  ( invᵉ right-unitᵉ) ∙ᵉ
  ( ( apᵉ
      ( concatᵉ
        ( apᵉ
          ( map-aut-Pointed-Type-With-Autᵉ Xᵉ)
          ( htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ)))))
        ( map-aut-Pointed-Type-With-Autᵉ Xᵉ
          ( map-hom-Pointed-Type-With-Autᵉ
            ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ))))))
      ( invᵉ (left-invᵉ
        ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ
          ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ))))))) ∙ᵉ
    ( invᵉ
      ( assocᵉ
        ( apᵉ
          ( map-aut-Pointed-Type-With-Autᵉ Xᵉ)
          ( htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ)))))
        ( invᵉ
          ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ
            ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ)))))
        ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ
          ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ (inrᵉ (inrᵉ (succ-ℕᵉ kᵉ)))))))

htpy-hom-ℤ-Pointed-Type-With-Autᵉ :
  {lᵉ : Level} (Xᵉ : Pointed-Type-With-Autᵉ lᵉ) →
  (hᵉ : hom-Pointed-Type-With-Autᵉ ℤ-Pointed-Type-With-Autᵉ Xᵉ) →
  htpy-hom-Pointed-Type-With-Autᵉ ℤ-Pointed-Type-With-Autᵉ Xᵉ
    (hom-ℤ-Pointed-Type-With-Autᵉ Xᵉ) hᵉ
htpy-hom-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ =
  pairᵉ
    ( htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ)
    ( pairᵉ
      ( coh-point-htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ)
      ( coh-aut-htpy-map-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ))

is-initial-ℤ-Pointed-Type-With-Autᵉ :
  {lᵉ : Level} (Xᵉ : Pointed-Type-With-Autᵉ lᵉ) →
  is-contrᵉ (hom-Pointed-Type-With-Autᵉ ℤ-Pointed-Type-With-Autᵉ Xᵉ)
is-initial-ℤ-Pointed-Type-With-Autᵉ Xᵉ =
  pairᵉ
    ( hom-ℤ-Pointed-Type-With-Autᵉ Xᵉ)
    ( λ hᵉ →
      eq-htpy-hom-Pointed-Type-With-Autᵉ ℤ-Pointed-Type-With-Autᵉ Xᵉ
        ( hom-ℤ-Pointed-Type-With-Autᵉ Xᵉ)
        ( hᵉ)
        ( htpy-hom-ℤ-Pointed-Type-With-Autᵉ Xᵉ hᵉ))
```