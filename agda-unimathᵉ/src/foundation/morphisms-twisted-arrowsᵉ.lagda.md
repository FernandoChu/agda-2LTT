# Morphisms of twisted arrows

```agda
module foundation.morphisms-twisted-arrowsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
```

</details>

## Idea

Aᵉ **morphismᵉ ofᵉ twistedᵉ arrows**ᵉ fromᵉ `fᵉ : Aᵉ → B`ᵉ to `gᵉ : Xᵉ → Y`ᵉ isᵉ aᵉ tripleᵉ
`(iᵉ ,ᵉ jᵉ ,ᵉ H)`ᵉ consistingᵉ ofᵉ

-ᵉ aᵉ mapᵉ `iᵉ : Xᵉ → A`ᵉ
-ᵉ aᵉ mapᵉ `jᵉ : Bᵉ → Y`,ᵉ andᵉ
-ᵉ aᵉ [homotopy](foundation-core.homotopies.mdᵉ) `Hᵉ : jᵉ ∘ᵉ fᵉ ∘ᵉ iᵉ ~ᵉ g`ᵉ witnessingᵉ
  thatᵉ theᵉ squareᵉ

  ```text
           iᵉ
      Aᵉ <-----ᵉ Xᵉ
      |        |
    fᵉ |        | gᵉ
      ∨ᵉ        ∨ᵉ
      Bᵉ ----->ᵉ Yᵉ
          jᵉ
  ```

  commutes.ᵉ

Thus,ᵉ aᵉ morphismᵉ ofᵉ twistedᵉ arrowsᵉ canᵉ alsoᵉ beᵉ understoodᵉ asᵉ _aᵉ factorizationᵉ ofᵉ
`g`ᵉ throughᵉ `f`_.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  coherence-hom-twisted-arrowᵉ :
    (Xᵉ → Aᵉ) → (Bᵉ → Yᵉ) → UUᵉ (l3ᵉ ⊔ l4ᵉ)
  coherence-hom-twisted-arrowᵉ iᵉ jᵉ = jᵉ ∘ᵉ fᵉ ∘ᵉ iᵉ ~ᵉ gᵉ

  hom-twisted-arrowᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-twisted-arrowᵉ =
    Σᵉ (Xᵉ → Aᵉ) (λ iᵉ → Σᵉ (Bᵉ → Yᵉ) (coherence-hom-twisted-arrowᵉ iᵉ))

  module _
    (αᵉ : hom-twisted-arrowᵉ)
    where

    map-domain-hom-twisted-arrowᵉ : Xᵉ → Aᵉ
    map-domain-hom-twisted-arrowᵉ = pr1ᵉ αᵉ

    map-codomain-hom-twisted-arrowᵉ : Bᵉ → Yᵉ
    map-codomain-hom-twisted-arrowᵉ = pr1ᵉ (pr2ᵉ αᵉ)

    coh-hom-twisted-arrowᵉ :
      map-codomain-hom-twisted-arrowᵉ ∘ᵉ fᵉ ∘ᵉ map-domain-hom-twisted-arrowᵉ ~ᵉ gᵉ
    coh-hom-twisted-arrowᵉ = pr2ᵉ (pr2ᵉ αᵉ)
```

## See also

-ᵉ [Morphismsᵉ ofᵉ arrows](foundation.morphisms-arrows.md).ᵉ