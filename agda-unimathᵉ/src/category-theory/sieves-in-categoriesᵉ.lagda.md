# Sieves in categories

```agda
module category-theory.sieves-in-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ

open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **sieve**ᵉ `S`ᵉ onᵉ anᵉ objectᵉ `X`ᵉ in aᵉ categoryᵉ `C`ᵉ isᵉ aᵉ collectionᵉ ofᵉ morphismsᵉ
intoᵉ `X`ᵉ whichᵉ isᵉ closedᵉ underᵉ precompositionᵉ byᵉ arbitraryᵉ morphismsᵉ ofᵉ `C`.ᵉ Inᵉ
otherᵉ words,ᵉ forᵉ anyᵉ morphismᵉ `fᵉ : Yᵉ → X`ᵉ in `S`ᵉ andᵉ anyᵉ morphismᵉ `gᵉ : Zᵉ → Y`ᵉ in
`C`,ᵉ theᵉ morphismᵉ `fᵉ ∘ᵉ gᵉ : Zᵉ → X`ᵉ isᵉ in `S`.ᵉ

Theᵉ notionᵉ ofᵉ sieveᵉ generalizesᵉ simultaneouslyᵉ theᵉ notionᵉ ofᵉ rightᵉ idealᵉ in aᵉ
monoidᵉ (aᵉ one-objectᵉ categoryᵉ) andᵉ aᵉ lowerᵉ setᵉ in aᵉ posetᵉ (aᵉ categoryᵉ with atᵉ
mostᵉ oneᵉ morphismᵉ betweenᵉ anyᵉ twoᵉ objects).ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Aᵉ : obj-Categoryᵉ Cᵉ)
  where

  is-sieve-prop-Categoryᵉ :
    { l3ᵉ : Level}
    ( Sᵉ : (Xᵉ Yᵉ : obj-Categoryᵉ Cᵉ) →
    subtypeᵉ l3ᵉ (hom-Categoryᵉ Cᵉ Xᵉ Yᵉ)) → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-sieve-prop-Categoryᵉ Sᵉ =
    Π-Propᵉ
      ( obj-Categoryᵉ Cᵉ)
      ( λ Xᵉ →
        Π-Propᵉ
          ( obj-Categoryᵉ Cᵉ)
          ( λ Yᵉ →
            Π-Propᵉ
              ( obj-Categoryᵉ Cᵉ)
              ( λ Zᵉ →
                Π-Propᵉ
                  ( type-subtypeᵉ (Sᵉ Yᵉ Xᵉ))
                  ( λ fᵉ →
                    Π-Propᵉ
                      ( hom-Categoryᵉ Cᵉ Zᵉ Yᵉ)
                      ( λ gᵉ →
                        Sᵉ Zᵉ Xᵉ
                          ( comp-hom-Categoryᵉ
                              Cᵉ (inclusion-subtypeᵉ (Sᵉ Yᵉ Xᵉ) fᵉ) gᵉ))))))

  is-sieve-Categoryᵉ :
    { l3ᵉ : Level}
    ( Sᵉ : (Xᵉ Yᵉ : obj-Categoryᵉ Cᵉ) →
    subtypeᵉ l3ᵉ (hom-Categoryᵉ Cᵉ Xᵉ Yᵉ)) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-sieve-Categoryᵉ Sᵉ = type-Propᵉ (is-sieve-prop-Categoryᵉ Sᵉ)

  is-prop-is-sieve-Categoryᵉ :
    { l3ᵉ : Level}
    ( Sᵉ : (Xᵉ Yᵉ : obj-Categoryᵉ Cᵉ) → subtypeᵉ l3ᵉ (hom-Categoryᵉ Cᵉ Xᵉ Yᵉ)) →
    is-propᵉ (is-sieve-Categoryᵉ Sᵉ)
  is-prop-is-sieve-Categoryᵉ Sᵉ = is-prop-type-Propᵉ (is-sieve-prop-Categoryᵉ Sᵉ)
```