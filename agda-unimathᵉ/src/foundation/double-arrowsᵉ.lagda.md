# Double arrows

```agda
module foundation.double-arrowsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "doubleᵉ arrow"ᵉ Disambiguation="betweenᵉ types"ᵉ Agda=double-arrowᵉ}}
isᵉ aᵉ [pair](foundation.dependent-pair-types.mdᵉ) ofᵉ typesᵉ `A`,ᵉ `B`ᵉ
[equipped](foundation.structure.mdᵉ) with aᵉ pairᵉ ofᵉ
[maps](foundation.function-types.mdᵉ) `f,ᵉ gᵉ : Aᵉ → B`.ᵉ

Weᵉ drawᵉ aᵉ doubleᵉ arrowᵉ asᵉ

```text
     Aᵉ
    | |
  fᵉ | | gᵉ
    | |
    ∨ᵉ ∨ᵉ
     Bᵉ
```

where `f`ᵉ isᵉ theᵉ firstᵉ mapᵉ in theᵉ structureᵉ andᵉ `g`ᵉ isᵉ theᵉ secondᵉ mapᵉ in theᵉ
structure.ᵉ Weᵉ alsoᵉ callᵉ `f`ᵉ theᵉ _leftᵉ mapᵉ_ andᵉ `g`ᵉ theᵉ _rightᵉ map_.ᵉ Byᵉ
convention,ᵉ [homotopies](foundation-core.homotopies.mdᵉ) goᵉ fromᵉ leftᵉ to right.ᵉ

## Definitions

### Double arrows

```agda
double-arrowᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
double-arrowᵉ l1ᵉ l2ᵉ = Σᵉ (UUᵉ l1ᵉ) (λ Aᵉ → Σᵉ (UUᵉ l2ᵉ) (λ Bᵉ → (Aᵉ → Bᵉ) ×ᵉ (Aᵉ → Bᵉ)))

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Aᵉ → Bᵉ)
  where

  make-double-arrowᵉ : double-arrowᵉ l1ᵉ l2ᵉ
  make-double-arrowᵉ = (Aᵉ ,ᵉ Bᵉ ,ᵉ fᵉ ,ᵉ gᵉ)

  {-# INLINE make-double-arrowᵉ #-}
```

### Components of a double arrow

```agda
module _
  {l1ᵉ l2ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ)
  where

  domain-double-arrowᵉ : UUᵉ l1ᵉ
  domain-double-arrowᵉ = pr1ᵉ aᵉ

  codomain-double-arrowᵉ : UUᵉ l2ᵉ
  codomain-double-arrowᵉ = pr1ᵉ (pr2ᵉ aᵉ)

  left-map-double-arrowᵉ : domain-double-arrowᵉ → codomain-double-arrowᵉ
  left-map-double-arrowᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ aᵉ))

  right-map-double-arrowᵉ : domain-double-arrowᵉ → codomain-double-arrowᵉ
  right-map-double-arrowᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ aᵉ))
```

## See also

-ᵉ Colimitsᵉ ofᵉ doubleᵉ arrowsᵉ areᵉ
  [coequalizers](synthetic-homotopy-theory.coequalizers.mdᵉ)