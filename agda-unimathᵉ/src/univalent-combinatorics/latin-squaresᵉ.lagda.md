# Latin squares

```agda
module univalent-combinatorics.latin-squaresᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-equivalencesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Latinᵉ squaresᵉ areᵉ multiplicationᵉ tablesᵉ in whichᵉ everyᵉ elementᵉ appearsᵉ in everyᵉ
rowᵉ andᵉ in everyᵉ columnᵉ exactlyᵉ once.ᵉ Latinᵉ squaresᵉ areᵉ consideredᵉ to beᵉ theᵉ
sameᵉ ifᵉ theyᵉ areᵉ isotopic.ᵉ Weᵉ thereforeᵉ defineᵉ theᵉ typeᵉ ofᵉ allᵉ Latinᵉ squaresᵉ to
beᵉ theᵉ typeᵉ ofᵉ allᵉ inhabitedᵉ typesᵉ A,ᵉ B,ᵉ andᵉ C,ᵉ equippedᵉ with aᵉ binaryᵉ
equivalenceᵉ fᵉ : Aᵉ → Bᵉ → C.ᵉ Theᵉ groupoidᵉ ofᵉ mainᵉ classesᵉ ofᵉ latinᵉ squaresᵉ isᵉ
definedᵉ in `main-classes-of-latin-squares`.ᵉ

## Definition

```agda
Latin-Squareᵉ : (l1ᵉ l2ᵉ l3ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
Latin-Squareᵉ l1ᵉ l2ᵉ l3ᵉ =
  Σᵉ ( Inhabited-Typeᵉ l1ᵉ)
    ( λ Aᵉ →
      Σᵉ ( Inhabited-Typeᵉ l2ᵉ)
        ( λ Bᵉ →
          Σᵉ ( Inhabited-Typeᵉ l3ᵉ)
            ( λ Cᵉ →
              Σᵉ ( type-Inhabited-Typeᵉ Aᵉ → type-Inhabited-Typeᵉ Bᵉ →
                  type-Inhabited-Typeᵉ Cᵉ)
                ( is-binary-equivᵉ))))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Lᵉ : Latin-Squareᵉ l1ᵉ l2ᵉ l3ᵉ)
  where

  inhabited-type-row-Latin-Squareᵉ : Inhabited-Typeᵉ l1ᵉ
  inhabited-type-row-Latin-Squareᵉ = pr1ᵉ Lᵉ

  row-Latin-Squareᵉ : UUᵉ l1ᵉ
  row-Latin-Squareᵉ = type-Inhabited-Typeᵉ inhabited-type-row-Latin-Squareᵉ

  inhabited-type-column-Latin-Squareᵉ : Inhabited-Typeᵉ l2ᵉ
  inhabited-type-column-Latin-Squareᵉ = pr1ᵉ (pr2ᵉ Lᵉ)

  column-Latin-Squareᵉ : UUᵉ l2ᵉ
  column-Latin-Squareᵉ = type-Inhabited-Typeᵉ inhabited-type-column-Latin-Squareᵉ

  inhabited-type-symbol-Latin-Squareᵉ : Inhabited-Typeᵉ l3ᵉ
  inhabited-type-symbol-Latin-Squareᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ Lᵉ))

  symbol-Latin-Squareᵉ : UUᵉ l3ᵉ
  symbol-Latin-Squareᵉ = type-Inhabited-Typeᵉ inhabited-type-symbol-Latin-Squareᵉ

  mul-Latin-Squareᵉ :
    row-Latin-Squareᵉ → column-Latin-Squareᵉ → symbol-Latin-Squareᵉ
  mul-Latin-Squareᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ Lᵉ)))

  mul-Latin-Square'ᵉ :
    column-Latin-Squareᵉ → row-Latin-Squareᵉ → symbol-Latin-Squareᵉ
  mul-Latin-Square'ᵉ xᵉ yᵉ = mul-Latin-Squareᵉ yᵉ xᵉ

  is-binary-equiv-mul-Latin-Squareᵉ :
    is-binary-equivᵉ mul-Latin-Squareᵉ
  is-binary-equiv-mul-Latin-Squareᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ Lᵉ)))
```