# Noncoherent H-spaces

```agda
module structured-types.noncoherent-h-spacesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unital-binary-operationsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Aᵉ **noncoherentᵉ H-space**ᵉ isᵉ aᵉ [pointedᵉ type](structured-types.pointed-types.mdᵉ)
`A`ᵉ [equipped](foundation.structure.mdᵉ) with aᵉ binaryᵉ operationᵉ `μ`ᵉ andᵉ
[homotopies](foundation-core.homotopies.mdᵉ) `(λᵉ xᵉ → μᵉ pointᵉ xᵉ) ~ᵉ id`ᵉ andᵉ
`λᵉ xᵉ → μᵉ xᵉ pointᵉ ~ᵉ id`.ᵉ Ifᵉ `A`ᵉ isᵉ aᵉ [connected](foundation.connected-types.mdᵉ)
H-space,ᵉ thenᵉ `λᵉ xᵉ → μᵉ aᵉ x`ᵉ andᵉ `λᵉ xᵉ → μᵉ xᵉ a`ᵉ areᵉ
[equivalences](foundation-core.equivalences.mdᵉ) forᵉ eachᵉ `aᵉ : A`.ᵉ

## Definitions

### Unital binary operations on pointed types

```agda
unit-laws-mul-Pointed-Typeᵉ :
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ)
  (μᵉ : (xᵉ yᵉ : type-Pointed-Typeᵉ Aᵉ) → type-Pointed-Typeᵉ Aᵉ) → UUᵉ lᵉ
unit-laws-mul-Pointed-Typeᵉ Aᵉ μᵉ = unit-lawsᵉ μᵉ (point-Pointed-Typeᵉ Aᵉ)

unital-mul-Pointed-Typeᵉ :
  {lᵉ : Level} → Pointed-Typeᵉ lᵉ → UUᵉ lᵉ
unital-mul-Pointed-Typeᵉ Aᵉ =
  Σᵉ ( type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ Aᵉ)
    ( unit-laws-mul-Pointed-Typeᵉ Aᵉ)
```

### Noncoherent H-Spaces

```agda
noncoherent-h-space-structureᵉ :
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ) → UUᵉ lᵉ
noncoherent-h-space-structureᵉ Aᵉ =
  Σᵉ ( (xᵉ yᵉ : type-Pointed-Typeᵉ Aᵉ) → type-Pointed-Typeᵉ Aᵉ)
    ( λ μᵉ → unit-lawsᵉ μᵉ (point-Pointed-Typeᵉ Aᵉ))

Noncoherent-H-Spaceᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Noncoherent-H-Spaceᵉ lᵉ = Σᵉ (Pointed-Typeᵉ lᵉ) (noncoherent-h-space-structureᵉ)

module _
  {lᵉ : Level} (Aᵉ : Noncoherent-H-Spaceᵉ lᵉ)
  where

  pointed-type-Noncoherent-H-Spaceᵉ : Pointed-Typeᵉ lᵉ
  pointed-type-Noncoherent-H-Spaceᵉ = pr1ᵉ Aᵉ

  type-Noncoherent-H-Spaceᵉ : UUᵉ lᵉ
  type-Noncoherent-H-Spaceᵉ = type-Pointed-Typeᵉ pointed-type-Noncoherent-H-Spaceᵉ

  point-Noncoherent-H-Spaceᵉ : type-Noncoherent-H-Spaceᵉ
  point-Noncoherent-H-Spaceᵉ =
    point-Pointed-Typeᵉ pointed-type-Noncoherent-H-Spaceᵉ

  mul-Noncoherent-H-Spaceᵉ :
    type-Noncoherent-H-Spaceᵉ →
    type-Noncoherent-H-Spaceᵉ →
    type-Noncoherent-H-Spaceᵉ
  mul-Noncoherent-H-Spaceᵉ = pr1ᵉ (pr2ᵉ Aᵉ)

  unit-laws-mul-Noncoherent-H-Spaceᵉ :
    unit-lawsᵉ mul-Noncoherent-H-Spaceᵉ point-Noncoherent-H-Spaceᵉ
  unit-laws-mul-Noncoherent-H-Spaceᵉ = pr2ᵉ (pr2ᵉ Aᵉ)

  left-unit-law-mul-Noncoherent-H-Spaceᵉ :
    (xᵉ : type-Noncoherent-H-Spaceᵉ) →
    mul-Noncoherent-H-Spaceᵉ point-Noncoherent-H-Spaceᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Noncoherent-H-Spaceᵉ = pr1ᵉ unit-laws-mul-Noncoherent-H-Spaceᵉ

  right-unit-law-mul-Noncoherent-H-Spaceᵉ :
    (xᵉ : type-Noncoherent-H-Spaceᵉ) →
    mul-Noncoherent-H-Spaceᵉ xᵉ point-Noncoherent-H-Spaceᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Noncoherent-H-Spaceᵉ = pr2ᵉ unit-laws-mul-Noncoherent-H-Spaceᵉ
```