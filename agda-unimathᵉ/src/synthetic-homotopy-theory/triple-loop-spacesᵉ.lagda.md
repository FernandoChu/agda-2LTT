# Triple loop spaces

```agda
module synthetic-homotopy-theory.triple-loop-spacesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.path-algebraᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.double-loop-spacesᵉ
open import synthetic-homotopy-theory.iterated-loop-spacesᵉ
```

</details>

## Idea

Aᵉ **tripleᵉ loopᵉ space**ᵉ isᵉ aᵉ threeᵉ timesᵉ
[iteratedᵉ loopᵉ space](synthetic-homotopy-theory.iterated-loop-spaces.md).ᵉ

## Definition

```agda
module _
  {lᵉ : Level}
  where

  Ω³ᵉ : Pointed-Typeᵉ lᵉ → Pointed-Typeᵉ lᵉ
  Ω³ᵉ Aᵉ = iterated-loop-spaceᵉ 3 Aᵉ

  type-Ω³ᵉ : {Aᵉ : UUᵉ lᵉ} (aᵉ : Aᵉ) → UUᵉ lᵉ
  type-Ω³ᵉ aᵉ = Idᵉ (refl-Ω²ᵉ {aᵉ = aᵉ}) (refl-Ω²ᵉ {aᵉ = aᵉ})

  refl-Ω³ᵉ : {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} → type-Ω³ᵉ aᵉ
  refl-Ω³ᵉ = reflᵉ
```

## Operations

```agda
x-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} → type-Ω³ᵉ aᵉ → type-Ω³ᵉ aᵉ → type-Ω³ᵉ aᵉ
x-concat-Ω³ᵉ = x-concat-Id³ᵉ

y-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} → type-Ω³ᵉ aᵉ → type-Ω³ᵉ aᵉ → type-Ω³ᵉ aᵉ
y-concat-Ω³ᵉ = y-concat-Id³ᵉ

z-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} → type-Ω³ᵉ aᵉ → type-Ω³ᵉ aᵉ → type-Ω³ᵉ aᵉ
z-concat-Ω³ᵉ = z-concat-Id³ᵉ

ap-x-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} {αᵉ α'ᵉ βᵉ β'ᵉ : type-Ω³ᵉ aᵉ}
  (sᵉ : Idᵉ αᵉ α'ᵉ) (tᵉ : Idᵉ βᵉ β'ᵉ) → Idᵉ (x-concat-Ω³ᵉ αᵉ βᵉ) (x-concat-Ω³ᵉ α'ᵉ β'ᵉ)
ap-x-concat-Ω³ᵉ sᵉ tᵉ = ap-binaryᵉ x-concat-Ω³ᵉ sᵉ tᵉ

ap-y-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} {αᵉ α'ᵉ βᵉ β'ᵉ : type-Ω³ᵉ aᵉ}
  (sᵉ : Idᵉ αᵉ α'ᵉ) (tᵉ : Idᵉ βᵉ β'ᵉ) → Idᵉ (y-concat-Ω³ᵉ αᵉ βᵉ) (y-concat-Ω³ᵉ α'ᵉ β'ᵉ)
ap-y-concat-Ω³ᵉ sᵉ tᵉ = j-concat-Id⁴ᵉ sᵉ tᵉ

ap-z-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} {αᵉ α'ᵉ βᵉ β'ᵉ : type-Ω³ᵉ aᵉ}
  (sᵉ : Idᵉ αᵉ α'ᵉ) (tᵉ : Idᵉ βᵉ β'ᵉ) → Idᵉ (z-concat-Ω³ᵉ αᵉ βᵉ) (z-concat-Ω³ᵉ α'ᵉ β'ᵉ)
ap-z-concat-Ω³ᵉ sᵉ tᵉ = k-concat-Id⁴ᵉ sᵉ tᵉ
```

## Properties

### The unit laws for the three concatenations on Ω³

```agda
left-unit-law-x-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} (αᵉ : type-Ω³ᵉ aᵉ) →
  Idᵉ (x-concat-Ω³ᵉ refl-Ω³ᵉ αᵉ) αᵉ
left-unit-law-x-concat-Ω³ᵉ αᵉ = left-unitᵉ

right-unit-law-x-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} (αᵉ : type-Ω³ᵉ aᵉ) →
  Idᵉ (x-concat-Ω³ᵉ αᵉ refl-Ω³ᵉ) αᵉ
right-unit-law-x-concat-Ω³ᵉ αᵉ = right-unitᵉ

left-unit-law-y-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} (αᵉ : type-Ω³ᵉ aᵉ) →
  Idᵉ (y-concat-Ω³ᵉ refl-Ω³ᵉ αᵉ) αᵉ
left-unit-law-y-concat-Ω³ᵉ αᵉ = left-unit-law-horizontal-concat-Ω²ᵉ

right-unit-law-y-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} (αᵉ : type-Ω³ᵉ aᵉ) →
  Idᵉ (y-concat-Ω³ᵉ αᵉ refl-Ω³ᵉ) αᵉ
right-unit-law-y-concat-Ω³ᵉ αᵉ = right-unit-law-horizontal-concat-Ω²ᵉ

left-unit-law-z-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} (αᵉ : type-Ω³ᵉ aᵉ) →
  Idᵉ (z-concat-Ω³ᵉ refl-Ω³ᵉ αᵉ) αᵉ
left-unit-law-z-concat-Ω³ᵉ αᵉ =
  ( left-unit-law-z-concat-Id³ᵉ αᵉ) ∙ᵉ
  ( ( invᵉ right-unitᵉ) ∙ᵉ
    ( ( inv-nat-htpyᵉ (λ ωᵉ → compute-left-refl-horizontal-concat-Id²ᵉ ωᵉ) αᵉ) ∙ᵉ
      ( ( invᵉ right-unitᵉ) ∙ᵉ
        ( ( inv-nat-htpyᵉ ap-idᵉ αᵉ) ∙ᵉ
          ( ap-idᵉ αᵉ)))))

{-ᵉ
super-naturality-right-unitᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ qᵉ : Idᵉ xᵉ yᵉ} {αᵉ βᵉ : Idᵉ pᵉ qᵉ} (γᵉ : Idᵉ αᵉ βᵉ)
  (uᵉ : Idᵉ yᵉ zᵉ) →
  Idᵉ (apᵉ (λ ωᵉ → horizontal-concat-Id²ᵉ ωᵉ (reflᵉ {xᵉ = uᵉ})) γᵉ) {!!ᵉ}
super-naturality-right-unitᵉ αᵉ = {!!ᵉ}
-ᵉ}

{-ᵉ
right-unit-law-z-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} (αᵉ : type-Ω³ᵉ aᵉ) →
  Idᵉ (z-concat-Ω³ᵉ αᵉ refl-Ω³ᵉ) αᵉ
right-unit-law-z-concat-Ω³ᵉ αᵉ =
  ( right-unit-law-z-concat-Id³ᵉ αᵉ) ∙ᵉ
  {!!ᵉ}
-ᵉ}
{-ᵉ
  ( ( invᵉ right-unitᵉ) ∙ᵉ
    ( ( inv-nat-htpyᵉ (λ ωᵉ → compute-right-refl-horizontal-concat-Id²ᵉ ωᵉ) αᵉ) ∙ᵉ
      ( left-unitᵉ ∙ᵉ
        ( ( invᵉ right-unitᵉ) ∙ᵉ
          ( ( inv-nat-htpyᵉ
                ( λ zᵉ →
                  ( invᵉ right-unitᵉ) ∙ᵉ
                  ( inv-nat-htpyᵉ (λ ωᵉ → right-unitᵉ) zᵉ) ∙ᵉ ( ap-idᵉ zᵉ)) αᵉ) ∙ᵉ
            ( ap-idᵉ αᵉ))))))
-ᵉ}
```

### The interchange laws for Ω³

```agda
interchange-x-y-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} (αᵉ βᵉ γᵉ δᵉ : type-Ω³ᵉ aᵉ) →
  Idᵉ
    ( y-concat-Ω³ᵉ (x-concat-Ω³ᵉ αᵉ βᵉ) (x-concat-Ω³ᵉ γᵉ δᵉ))
    ( x-concat-Ω³ᵉ (y-concat-Ω³ᵉ αᵉ γᵉ) (y-concat-Ω³ᵉ βᵉ δᵉ))
interchange-x-y-concat-Ω³ᵉ = interchange-x-y-concat-Id³ᵉ

interchange-x-z-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} (αᵉ βᵉ γᵉ δᵉ : type-Ω³ᵉ aᵉ) →
  Idᵉ
    ( z-concat-Ω³ᵉ (x-concat-Ω³ᵉ αᵉ βᵉ) (x-concat-Ω³ᵉ γᵉ δᵉ))
    ( x-concat-Ω³ᵉ (z-concat-Ω³ᵉ αᵉ γᵉ) (z-concat-Ω³ᵉ βᵉ δᵉ))
interchange-x-z-concat-Ω³ᵉ = interchange-x-z-concat-Id³ᵉ

interchange-y-z-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} (αᵉ βᵉ γᵉ δᵉ : type-Ω³ᵉ aᵉ) →
  Idᵉ
    ( z-concat-Ω³ᵉ (y-concat-Ω³ᵉ αᵉ βᵉ) (y-concat-Ω³ᵉ γᵉ δᵉ))
    ( y-concat-Ω³ᵉ (z-concat-Ω³ᵉ αᵉ γᵉ) (z-concat-Ω³ᵉ βᵉ δᵉ))
interchange-y-z-concat-Ω³ᵉ αᵉ βᵉ γᵉ δᵉ =
  invᵉ right-unitᵉ ∙ᵉ interchange-y-z-concat-Id³ᵉ αᵉ βᵉ γᵉ δᵉ
```

### The Eckmann-Hilton connections in Ω³

```agda
outer-eckmann-hilton-connection-x-y-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} (αᵉ δᵉ : type-Ω³ᵉ aᵉ) →
  Idᵉ (y-concat-Ω³ᵉ αᵉ δᵉ) (x-concat-Ω³ᵉ αᵉ δᵉ)
outer-eckmann-hilton-connection-x-y-concat-Ω³ᵉ αᵉ δᵉ =
  ( j-concat-Id⁴ᵉ
    ( invᵉ (right-unit-law-x-concat-Ω³ᵉ αᵉ))
    ( invᵉ (left-unit-law-x-concat-Ω³ᵉ δᵉ))) ∙ᵉ
  ( ( interchange-x-y-concat-Ω³ᵉ αᵉ reflᵉ reflᵉ δᵉ) ∙ᵉ
    ( i-concat-Id⁴ᵉ
      ( right-unit-law-y-concat-Ω³ᵉ αᵉ)
      ( left-unit-law-y-concat-Ω³ᵉ δᵉ)))

inner-eckmann-hilton-connection-x-y-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} (βᵉ γᵉ : type-Ω³ᵉ aᵉ) →
  Idᵉ (y-concat-Ω³ᵉ βᵉ γᵉ) (x-concat-Ω³ᵉ γᵉ βᵉ)
inner-eckmann-hilton-connection-x-y-concat-Ω³ᵉ βᵉ γᵉ =
  ( j-concat-Id⁴ᵉ
    ( invᵉ (left-unit-law-x-concat-Ω³ᵉ βᵉ))
    ( invᵉ (right-unit-law-x-concat-Ω³ᵉ γᵉ))) ∙ᵉ
  ( ( interchange-x-y-concat-Ω³ᵉ reflᵉ βᵉ γᵉ reflᵉ) ∙ᵉ
    ( i-concat-Id⁴ᵉ
      ( left-unit-law-y-concat-Ω³ᵉ γᵉ)
      ( right-unit-law-y-concat-Ω³ᵉ βᵉ)))

{-ᵉ
outer-eckmann-hilton-connection-x-z-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} (αᵉ δᵉ : type-Ω³ᵉ aᵉ) →
  Idᵉ (z-concat-Ω³ᵉ αᵉ δᵉ) (x-concat-Ω³ᵉ αᵉ δᵉ)
outer-eckmann-hilton-connection-x-z-concat-Ω³ᵉ αᵉ δᵉ =
  ( k-concat-Id⁴ᵉ
    ( invᵉ (right-unit-law-x-concat-Ω³ᵉ αᵉ))
    ( invᵉ (left-unit-law-x-concat-Ω³ᵉ δᵉ))) ∙ᵉ
  ( ( interchange-x-z-concat-Ω³ᵉ αᵉ reflᵉ reflᵉ δᵉ) ∙ᵉ
    ( i-concat-Id⁴ᵉ
      ( right-unit-law-z-concat-Ω³ᵉ αᵉ)
      ( left-unit-law-z-concat-Ω³ᵉ δᵉ)))
-ᵉ}

{-ᵉ
inner-eckmann-hilton-connection-x-z-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} (βᵉ γᵉ : type-Ω³ᵉ aᵉ) →
  Idᵉ (z-concat-Ω³ᵉ βᵉ γᵉ) (x-concat-Ω³ᵉ γᵉ βᵉ)
inner-eckmann-hilton-connection-x-z-concat-Ω³ᵉ βᵉ γᵉ =
  ( k-concat-Id⁴ᵉ
    ( invᵉ (left-unit-law-x-concat-Ω³ᵉ βᵉ))
    ( invᵉ (right-unit-law-x-concat-Ω³ᵉ γᵉ))) ∙ᵉ
  ( ( interchange-x-z-concat-Ω³ᵉ reflᵉ βᵉ γᵉ reflᵉ) ∙ᵉ
    ( i-concat-Id⁴ᵉ
      ( left-unit-law-z-concat-Ω³ᵉ γᵉ)
      ( right-unit-law-z-concat-Ω³ᵉ βᵉ)))
-ᵉ}

{-ᵉ
outer-eckmann-hilton-connection-y-z-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} (αᵉ δᵉ : type-Ω³ᵉ aᵉ) →
  Idᵉ (z-concat-Ω³ᵉ αᵉ δᵉ) (y-concat-Ω³ᵉ αᵉ δᵉ)
outer-eckmann-hilton-connection-y-z-concat-Ω³ᵉ αᵉ δᵉ =
  ( k-concat-Id⁴ᵉ
    ( invᵉ (right-unit-law-y-concat-Ω³ᵉ αᵉ))
    ( invᵉ (left-unit-law-y-concat-Ω³ᵉ δᵉ))) ∙ᵉ
  ( ( interchange-y-z-concat-Ω³ᵉ αᵉ reflᵉ reflᵉ δᵉ) ∙ᵉ
    ( j-concat-Id⁴ᵉ
      ( right-unit-law-z-concat-Ω³ᵉ αᵉ)
      ( left-unit-law-z-concat-Ω³ᵉ δᵉ)))
-ᵉ}

{-ᵉ
inner-eckmann-hilton-connection-y-z-concat-Ω³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} (βᵉ γᵉ : type-Ω³ᵉ aᵉ) →
  Idᵉ (z-concat-Ω³ᵉ βᵉ γᵉ) (y-concat-Ω³ᵉ γᵉ βᵉ)
inner-eckmann-hilton-connection-y-z-concat-Ω³ᵉ βᵉ γᵉ =
  ( k-concat-Id⁴ᵉ
    ( invᵉ (left-unit-law-y-concat-Ω³ᵉ βᵉ))
    ( invᵉ (right-unit-law-y-concat-Ω³ᵉ γᵉ))) ∙ᵉ
  ( ( interchange-y-z-concat-Ω³ᵉ reflᵉ βᵉ γᵉ reflᵉ) ∙ᵉ
    ( j-concat-Id⁴ᵉ
      ( left-unit-law-z-concat-Ω³ᵉ γᵉ)
      ( right-unit-law-z-concat-Ω³ᵉ βᵉ)))
-ᵉ}
```