# Universal Property of suspensions of pointed types

```agda
module synthetic-homotopy-theory.universal-property-suspensions-of-pointed-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-equivalencesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.functoriality-loop-spacesᵉ
open import synthetic-homotopy-theory.loop-spacesᵉ
open import synthetic-homotopy-theory.suspensions-of-pointed-typesᵉ
open import synthetic-homotopy-theory.suspensions-of-typesᵉ
```

</details>

## Idea

Theᵉ [suspension](synthetic-homotopy-theory.suspensions-of-types.mdᵉ) ofᵉ aᵉ
[pointedᵉ type](structured-types.pointed-types.mdᵉ) enjoysᵉ anᵉ additionalᵉ universalᵉ
property,ᵉ onᵉ topᵉ ofᵉ
[theᵉ universalᵉ propertyᵉ associtatedᵉ with beingᵉ aᵉ suspension](synthetic-homotopy-theory.universal-property-suspensions.md).ᵉ
Thisᵉ universalᵉ propertyᵉ isᵉ packagedᵉ in anᵉ adjunctionᵉ: theᵉ suspensionᵉ
constructionᵉ onᵉ pointedᵉ typesᵉ isᵉ leftᵉ adjointᵉ to theᵉ loopᵉ spaceᵉ construction.ᵉ

#### The unit and counit of the adjunction

```agda
module _
  {l1ᵉ : Level} (Xᵉ : Pointed-Typeᵉ l1ᵉ)
  where

  pointed-equiv-loop-pointed-identity-suspensionᵉ :
    ( pairᵉ
      ( north-suspensionᵉ ＝ᵉ south-suspensionᵉ)
      ( meridian-suspensionᵉ (point-Pointed-Typeᵉ Xᵉ))) ≃∗ᵉ
    ( Ωᵉ (suspension-Pointed-Typeᵉ Xᵉ))
  pointed-equiv-loop-pointed-identity-suspensionᵉ =
    pointed-equiv-loop-pointed-identityᵉ
      ( suspension-Pointed-Typeᵉ Xᵉ)
      ( meridian-suspensionᵉ (point-Pointed-Typeᵉ Xᵉ))

  pointed-map-loop-pointed-identity-suspensionᵉ :
    ( pairᵉ
      ( north-suspensionᵉ ＝ᵉ south-suspensionᵉ)
      ( meridian-suspensionᵉ (point-Pointed-Typeᵉ Xᵉ))) →∗ᵉ
    Ωᵉ (suspension-Pointed-Typeᵉ Xᵉ)
  pointed-map-loop-pointed-identity-suspensionᵉ =
    pointed-map-pointed-equivᵉ
      ( pointed-equiv-loop-pointed-identity-suspensionᵉ)

  pointed-map-concat-meridian-suspensionᵉ :
    Xᵉ →∗ᵉ
    ( pairᵉ
      ( north-suspensionᵉ ＝ᵉ south-suspensionᵉ)
      ( meridian-suspensionᵉ (point-Pointed-Typeᵉ Xᵉ)))
  pr1ᵉ pointed-map-concat-meridian-suspensionᵉ = meridian-suspensionᵉ
  pr2ᵉ pointed-map-concat-meridian-suspensionᵉ = reflᵉ

  pointed-map-unit-suspension-loop-adjunctionᵉ :
    Xᵉ →∗ᵉ Ωᵉ (suspension-Pointed-Typeᵉ Xᵉ)
  pointed-map-unit-suspension-loop-adjunctionᵉ =
    pointed-map-loop-pointed-identity-suspensionᵉ ∘∗ᵉ
    pointed-map-concat-meridian-suspensionᵉ

  map-unit-suspension-loop-adjunctionᵉ :
    type-Pointed-Typeᵉ Xᵉ → type-Ωᵉ (suspension-Pointed-Typeᵉ Xᵉ)
  map-unit-suspension-loop-adjunctionᵉ =
    map-pointed-mapᵉ pointed-map-unit-suspension-loop-adjunctionᵉ

  map-counit-suspension-loop-adjunctionᵉ :
    suspensionᵉ (type-Ωᵉ Xᵉ) → type-Pointed-Typeᵉ Xᵉ
  map-counit-suspension-loop-adjunctionᵉ =
    map-inv-is-equivᵉ
      ( up-suspensionᵉ (type-Pointed-Typeᵉ Xᵉ))
      ( point-Pointed-Typeᵉ Xᵉ ,ᵉ point-Pointed-Typeᵉ Xᵉ ,ᵉ idᵉ)

  pointed-map-counit-suspension-loop-adjunctionᵉ :
    pairᵉ (suspensionᵉ (type-Ωᵉ Xᵉ)) (north-suspensionᵉ) →∗ᵉ Xᵉ
  pr1ᵉ pointed-map-counit-suspension-loop-adjunctionᵉ =
    map-counit-suspension-loop-adjunctionᵉ
  pr2ᵉ pointed-map-counit-suspension-loop-adjunctionᵉ =
    compute-north-cogap-suspensionᵉ
      ( point-Pointed-Typeᵉ Xᵉ ,ᵉ point-Pointed-Typeᵉ Xᵉ ,ᵉ idᵉ)
```

#### The transposing maps of the adjunction

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Pointed-Typeᵉ l1ᵉ) (Yᵉ : Pointed-Typeᵉ l2ᵉ)
  where

  transpose-suspension-loop-adjunctionᵉ :
    (suspension-Pointed-Typeᵉ Xᵉ →∗ᵉ Yᵉ) → (Xᵉ →∗ᵉ Ωᵉ Yᵉ)
  transpose-suspension-loop-adjunctionᵉ f∗ᵉ =
    pointed-map-Ωᵉ f∗ᵉ ∘∗ᵉ pointed-map-unit-suspension-loop-adjunctionᵉ Xᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Pointed-Typeᵉ l1ᵉ) (Yᵉ : Pointed-Typeᵉ l2ᵉ)
  where

  inv-transpose-suspension-loop-adjunctionᵉ :
    (Xᵉ →∗ᵉ Ωᵉ Yᵉ) → (suspension-Pointed-Typeᵉ Xᵉ →∗ᵉ Yᵉ)
  pr1ᵉ (inv-transpose-suspension-loop-adjunctionᵉ f∗ᵉ) =
    cogap-suspensionᵉ
      ( suspension-structure-map-into-Ωᵉ
        ( type-Pointed-Typeᵉ Xᵉ)
        ( Yᵉ)
        ( map-pointed-mapᵉ f∗ᵉ))
  pr2ᵉ (inv-transpose-suspension-loop-adjunctionᵉ f∗ᵉ) =
    compute-north-cogap-suspensionᵉ
      ( suspension-structure-map-into-Ωᵉ
        ( type-Pointed-Typeᵉ Xᵉ)
        ( Yᵉ)
        ( map-pointed-mapᵉ f∗ᵉ))
```

Weᵉ nowᵉ showᵉ theseᵉ mapsᵉ areᵉ inversesᵉ ofᵉ eachᵉ other.ᵉ

#### The transposing equivalence between pointed maps out of the suspension of `X` and pointed maps into the loop space of `Y`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Pointed-Typeᵉ l1ᵉ) (Yᵉ : Pointed-Typeᵉ l2ᵉ)
  where

  equiv-transpose-suspension-loop-adjunctionᵉ :
    (suspension-Pointed-Typeᵉ Xᵉ →∗ᵉ Yᵉ) ≃ᵉ (Xᵉ →∗ᵉ Ωᵉ Yᵉ)
  equiv-transpose-suspension-loop-adjunctionᵉ =
    ( left-unit-law-Σ-is-contrᵉ
      ( is-torsorial-Idᵉ (point-Pointed-Typeᵉ Yᵉ))
      ( point-Pointed-Typeᵉ Yᵉ ,ᵉ reflᵉ)) ∘eᵉ
    ( inv-associative-Σᵉ
      ( type-Pointed-Typeᵉ Yᵉ)
      ( λ zᵉ → point-Pointed-Typeᵉ Yᵉ ＝ᵉ zᵉ)
      ( λ tᵉ →
        Σᵉ ( type-Pointed-Typeᵉ Xᵉ → point-Pointed-Typeᵉ Yᵉ ＝ᵉ pr1ᵉ tᵉ)
          ( λ fᵉ → fᵉ (point-Pointed-Typeᵉ Xᵉ) ＝ᵉ pr2ᵉ tᵉ))) ∘eᵉ
    ( equiv-totᵉ (λ y1ᵉ → equiv-left-swap-Σᵉ)) ∘eᵉ
    ( associative-Σᵉ
      ( type-Pointed-Typeᵉ Yᵉ)
      ( λ y1ᵉ → type-Pointed-Typeᵉ Xᵉ → point-Pointed-Typeᵉ Yᵉ ＝ᵉ y1ᵉ)
      ( λ zᵉ →
        Σᵉ ( point-Pointed-Typeᵉ Yᵉ ＝ᵉ pr1ᵉ zᵉ)
          ( λ xᵉ → pr2ᵉ zᵉ (point-Pointed-Typeᵉ Xᵉ) ＝ᵉ xᵉ))) ∘eᵉ
    ( inv-right-unit-law-Σ-is-contrᵉ
      ( λ zᵉ → is-torsorial-Idᵉ (pr2ᵉ zᵉ (point-Pointed-Typeᵉ Xᵉ)))) ∘eᵉ
    ( left-unit-law-Σ-is-contrᵉ
      ( is-torsorial-Id'ᵉ (point-Pointed-Typeᵉ Yᵉ))
      ( point-Pointed-Typeᵉ Yᵉ ,ᵉ reflᵉ)) ∘eᵉ
    ( equiv-right-swap-Σᵉ) ∘eᵉ
    ( equiv-Σ-equiv-baseᵉ
      ( λ cᵉ → pr1ᵉ cᵉ ＝ᵉ point-Pointed-Typeᵉ Yᵉ)
      ( equiv-up-suspensionᵉ))
```

#### The equivalence in the suspension-loop space adjunction is pointed

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#702](https://github.com/UniMath/agda-unimath/issues/702ᵉ)