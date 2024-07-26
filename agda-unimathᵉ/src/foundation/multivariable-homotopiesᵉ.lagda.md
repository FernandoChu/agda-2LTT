# Multivariable homotopies

```agda
module foundation.multivariable-homotopiesᵉ where

open import foundation.telescopesᵉ public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.implicit-function-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Givenᵉ anᵉ
[iteratedᵉ dependentᵉ product](foundation.iterated-dependent-product-types.mdᵉ) weᵉ
canᵉ considerᵉ [homotopies](foundation-core.homotopies.mdᵉ) ofᵉ itsᵉ elements.ᵉ Byᵉ
[functionᵉ extensionality](foundation.function-extensionality.md),ᵉ
**multivariableᵉ homotopies**ᵉ areᵉ [equivalent](foundation-core.equivalences.mdᵉ)
to [identifications](foundation-core.identity-types.md).ᵉ

## Definitions

### Multivariable homotopies

```agda
multivariable-htpyᵉ :
  {lᵉ : Level} {nᵉ : ℕᵉ} {{Aᵉ : telescopeᵉ lᵉ nᵉ}} (fᵉ gᵉ : iterated-Πᵉ Aᵉ) → UUᵉ lᵉ
multivariable-htpyᵉ {{base-telescopeᵉ Aᵉ}} fᵉ gᵉ = fᵉ ＝ᵉ gᵉ
multivariable-htpyᵉ {{cons-telescopeᵉ {Xᵉ = Xᵉ} Aᵉ}} fᵉ gᵉ =
  (xᵉ : Xᵉ) → multivariable-htpyᵉ {{Aᵉ xᵉ}} (fᵉ xᵉ) (gᵉ xᵉ)
```

### Multivariable homotopies between implicit functions

```agda
multivariable-htpy-implicitᵉ :
  {lᵉ : Level} {nᵉ : ℕᵉ} {{Aᵉ : telescopeᵉ lᵉ nᵉ}} (fᵉ gᵉ : iterated-implicit-Πᵉ Aᵉ) → UUᵉ lᵉ
multivariable-htpy-implicitᵉ {{base-telescopeᵉ Aᵉ}} fᵉ gᵉ = fᵉ ＝ᵉ gᵉ
multivariable-htpy-implicitᵉ {{cons-telescopeᵉ {Xᵉ = Xᵉ} Aᵉ}} fᵉ gᵉ =
  (xᵉ : Xᵉ) → multivariable-htpy-implicitᵉ {{Aᵉ xᵉ}} (fᵉ {xᵉ}) (gᵉ {xᵉ})
```

### Multivariable implicit homotopies between functions

```agda
multivariable-implicit-htpyᵉ :
  {lᵉ : Level} {nᵉ : ℕᵉ} {{Aᵉ : telescopeᵉ lᵉ nᵉ}} (fᵉ gᵉ : iterated-Πᵉ Aᵉ) → UUᵉ lᵉ
multivariable-implicit-htpyᵉ {{base-telescopeᵉ Aᵉ}} fᵉ gᵉ = fᵉ ＝ᵉ gᵉ
multivariable-implicit-htpyᵉ {{cons-telescopeᵉ {Xᵉ = Xᵉ} Aᵉ}} fᵉ gᵉ =
  {xᵉ : Xᵉ} → multivariable-implicit-htpyᵉ {{Aᵉ xᵉ}} (fᵉ xᵉ) (gᵉ xᵉ)
```

### Multivariable implicit homotopies between implicit functions

```agda
multivariable-implicit-htpy-implicitᵉ :
  {lᵉ : Level} {nᵉ : ℕᵉ} {{Aᵉ : telescopeᵉ lᵉ nᵉ}} (fᵉ gᵉ : iterated-implicit-Πᵉ Aᵉ) → UUᵉ lᵉ
multivariable-implicit-htpy-implicitᵉ {{base-telescopeᵉ Aᵉ}} fᵉ gᵉ = fᵉ ＝ᵉ gᵉ
multivariable-implicit-htpy-implicitᵉ {{cons-telescopeᵉ {Xᵉ = Xᵉ} Aᵉ}} fᵉ gᵉ =
  {xᵉ : Xᵉ} → multivariable-implicit-htpy-implicitᵉ {{Aᵉ xᵉ}} (fᵉ {xᵉ}) (gᵉ {xᵉ})
```

### Implicit multivariable homotopies are equivalent to explicit multivariable homotopies

```agda
equiv-multivariable-explicit-implicit-htpyᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} {fᵉ gᵉ : iterated-Πᵉ Aᵉ} →
  multivariable-implicit-htpyᵉ {{Aᵉ}} fᵉ gᵉ ≃ᵉ multivariable-htpyᵉ {{Aᵉ}} fᵉ gᵉ
equiv-multivariable-explicit-implicit-htpyᵉ .zero-ℕᵉ {{base-telescopeᵉ Aᵉ}} = id-equivᵉ
equiv-multivariable-explicit-implicit-htpyᵉ ._ {{cons-telescopeᵉ Aᵉ}} =
  ( equiv-Π-equiv-familyᵉ
    ( λ xᵉ → equiv-multivariable-explicit-implicit-htpyᵉ _ {{Aᵉ xᵉ}})) ∘eᵉ
  ( equiv-explicit-implicit-Πᵉ)

equiv-multivariable-implicit-explicit-htpyᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} {fᵉ gᵉ : iterated-Πᵉ Aᵉ} →
  multivariable-htpyᵉ {{Aᵉ}} fᵉ gᵉ ≃ᵉ multivariable-implicit-htpyᵉ {{Aᵉ}} fᵉ gᵉ
equiv-multivariable-implicit-explicit-htpyᵉ nᵉ {{Aᵉ}} =
  inv-equivᵉ (equiv-multivariable-explicit-implicit-htpyᵉ nᵉ {{Aᵉ}})

equiv-multivariable-explicit-implicit-htpy-implicitᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} {fᵉ gᵉ : iterated-implicit-Πᵉ Aᵉ} →
  ( multivariable-implicit-htpy-implicitᵉ {{Aᵉ}} fᵉ gᵉ) ≃ᵉ
  ( multivariable-htpy-implicitᵉ {{Aᵉ}} fᵉ gᵉ)
equiv-multivariable-explicit-implicit-htpy-implicitᵉ .zero-ℕᵉ {{base-telescopeᵉ Aᵉ}} =
  id-equivᵉ
equiv-multivariable-explicit-implicit-htpy-implicitᵉ ._ {{cons-telescopeᵉ Aᵉ}} =
  ( equiv-Π-equiv-familyᵉ
    ( λ xᵉ → equiv-multivariable-explicit-implicit-htpy-implicitᵉ _ {{Aᵉ xᵉ}})) ∘eᵉ
  ( equiv-explicit-implicit-Πᵉ)

equiv-multivariable-implicit-explicit-htpy-implicitᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} {fᵉ gᵉ : iterated-implicit-Πᵉ Aᵉ} →
  ( multivariable-htpy-implicitᵉ {{Aᵉ}} fᵉ gᵉ) ≃ᵉ
  ( multivariable-implicit-htpy-implicitᵉ {{Aᵉ}} fᵉ gᵉ)
equiv-multivariable-implicit-explicit-htpy-implicitᵉ nᵉ {{Aᵉ}} =
  inv-equivᵉ (equiv-multivariable-explicit-implicit-htpy-implicitᵉ nᵉ {{Aᵉ}})
```

### Iterated function extensionality

```agda
refl-multivariable-htpyᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}}
  {fᵉ : iterated-Πᵉ Aᵉ} → multivariable-htpyᵉ {{Aᵉ}} fᵉ fᵉ
refl-multivariable-htpyᵉ .zero-ℕᵉ {{base-telescopeᵉ Aᵉ}} = reflᵉ
refl-multivariable-htpyᵉ ._ {{cons-telescopeᵉ Aᵉ}} xᵉ =
  refl-multivariable-htpyᵉ _ {{Aᵉ xᵉ}}

multivariable-htpy-eqᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}}
  {fᵉ gᵉ : iterated-Πᵉ Aᵉ} → fᵉ ＝ᵉ gᵉ → multivariable-htpyᵉ {{Aᵉ}} fᵉ gᵉ
multivariable-htpy-eqᵉ .zero-ℕᵉ {{base-telescopeᵉ Aᵉ}} pᵉ = pᵉ
multivariable-htpy-eqᵉ ._ {{cons-telescopeᵉ Aᵉ}} pᵉ xᵉ =
  multivariable-htpy-eqᵉ _ {{Aᵉ xᵉ}} (htpy-eqᵉ pᵉ xᵉ)

eq-multivariable-htpyᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}}
  {fᵉ gᵉ : iterated-Πᵉ Aᵉ} → multivariable-htpyᵉ {{Aᵉ}} fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
eq-multivariable-htpyᵉ .zero-ℕᵉ {{base-telescopeᵉ Aᵉ}} Hᵉ = Hᵉ
eq-multivariable-htpyᵉ ._ {{cons-telescopeᵉ Aᵉ}} Hᵉ =
  eq-htpyᵉ (λ xᵉ → eq-multivariable-htpyᵉ _ {{Aᵉ xᵉ}} (Hᵉ xᵉ))

equiv-iterated-funextᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}}
  {fᵉ gᵉ : iterated-Πᵉ Aᵉ} → (fᵉ ＝ᵉ gᵉ) ≃ᵉ multivariable-htpyᵉ {{Aᵉ}} fᵉ gᵉ
equiv-iterated-funextᵉ .zero-ℕᵉ {{base-telescopeᵉ Aᵉ}} = id-equivᵉ
equiv-iterated-funextᵉ ._ {{cons-telescopeᵉ Aᵉ}} =
  equiv-Π-equiv-familyᵉ (λ xᵉ → equiv-iterated-funextᵉ _ {{Aᵉ xᵉ}}) ∘eᵉ equiv-funextᵉ

equiv-eq-multivariable-htpyᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}}
  {fᵉ gᵉ : iterated-Πᵉ Aᵉ} → multivariable-htpyᵉ {{Aᵉ}} fᵉ gᵉ ≃ᵉ (fᵉ ＝ᵉ gᵉ)
equiv-eq-multivariable-htpyᵉ nᵉ {{Aᵉ}} {fᵉ} {gᵉ} =
  inv-equivᵉ (equiv-iterated-funextᵉ nᵉ {{Aᵉ}} {fᵉ} {gᵉ})
```

### Iterated function extensionality for implicit functions

```agda
refl-multivariable-htpy-implicitᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} {fᵉ : iterated-implicit-Πᵉ Aᵉ} →
  multivariable-htpy-implicitᵉ {{Aᵉ}} fᵉ fᵉ
refl-multivariable-htpy-implicitᵉ .zero-ℕᵉ {{base-telescopeᵉ Aᵉ}} = reflᵉ
refl-multivariable-htpy-implicitᵉ ._ {{cons-telescopeᵉ Aᵉ}} xᵉ =
  refl-multivariable-htpy-implicitᵉ _ {{Aᵉ xᵉ}}

multivariable-htpy-eq-implicitᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} {fᵉ gᵉ : iterated-implicit-Πᵉ Aᵉ} →
  Idᵉ {Aᵉ = iterated-implicit-Πᵉ Aᵉ} fᵉ gᵉ → multivariable-htpy-implicitᵉ {{Aᵉ}} fᵉ gᵉ
multivariable-htpy-eq-implicitᵉ .zero-ℕᵉ {{base-telescopeᵉ Aᵉ}} pᵉ = pᵉ
multivariable-htpy-eq-implicitᵉ ._ {{cons-telescopeᵉ Aᵉ}} pᵉ xᵉ =
  multivariable-htpy-eq-implicitᵉ _ {{Aᵉ xᵉ}} (htpy-eq-implicitᵉ pᵉ xᵉ)

eq-multivariable-htpy-implicitᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} {fᵉ gᵉ : iterated-implicit-Πᵉ Aᵉ} →
  multivariable-htpy-implicitᵉ {{Aᵉ}} fᵉ gᵉ → Idᵉ {Aᵉ = iterated-implicit-Πᵉ Aᵉ} fᵉ gᵉ
eq-multivariable-htpy-implicitᵉ .zero-ℕᵉ {{base-telescopeᵉ Aᵉ}} Hᵉ = Hᵉ
eq-multivariable-htpy-implicitᵉ ._ {{cons-telescopeᵉ Aᵉ}} Hᵉ =
  eq-htpy-implicitᵉ (λ xᵉ → eq-multivariable-htpy-implicitᵉ _ {{Aᵉ xᵉ}} (Hᵉ xᵉ))

equiv-iterated-funext-implicitᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} {fᵉ gᵉ : iterated-implicit-Πᵉ Aᵉ} →
  (Idᵉ {Aᵉ = iterated-implicit-Πᵉ Aᵉ} fᵉ gᵉ) ≃ᵉ multivariable-htpy-implicitᵉ {{Aᵉ}} fᵉ gᵉ
equiv-iterated-funext-implicitᵉ .zero-ℕᵉ {{base-telescopeᵉ Aᵉ}} = id-equivᵉ
equiv-iterated-funext-implicitᵉ ._ {{cons-telescopeᵉ Aᵉ}} =
  ( equiv-Π-equiv-familyᵉ (λ xᵉ → equiv-iterated-funext-implicitᵉ _ {{Aᵉ xᵉ}})) ∘eᵉ
  ( equiv-funext-implicitᵉ)
```

### Torsoriality of multivariable homotopies

```agda
abstract
  is-torsorial-multivariable-htpyᵉ :
    {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} (fᵉ : iterated-Πᵉ Aᵉ) →
    is-torsorialᵉ (multivariable-htpyᵉ {{Aᵉ}} fᵉ)
  is-torsorial-multivariable-htpyᵉ .zero-ℕᵉ {{base-telescopeᵉ Aᵉ}} = is-torsorial-Idᵉ
  is-torsorial-multivariable-htpyᵉ ._ {{cons-telescopeᵉ Aᵉ}} fᵉ =
    is-torsorial-Eq-Πᵉ (λ xᵉ → is-torsorial-multivariable-htpyᵉ _ {{Aᵉ xᵉ}} (fᵉ xᵉ))

abstract
  is-torsorial-multivariable-htpy-implicitᵉ :
    {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} (fᵉ : iterated-implicit-Πᵉ Aᵉ) →
    is-torsorialᵉ (multivariable-htpy-implicitᵉ {{Aᵉ}} fᵉ)
  is-torsorial-multivariable-htpy-implicitᵉ ._ {{Aᵉ}} fᵉ =
    is-contr-equiv'ᵉ
      ( Σᵉ (iterated-implicit-Πᵉ Aᵉ) (Idᵉ {Aᵉ = iterated-implicit-Πᵉ Aᵉ} fᵉ))
      ( equiv-totᵉ (λ _ → equiv-iterated-funext-implicitᵉ _ {{Aᵉ}}))
      ( is-torsorial-Idᵉ {Aᵉ = iterated-implicit-Πᵉ Aᵉ} fᵉ)

abstract
  is-torsorial-multivariable-implicit-htpyᵉ :
    {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} (fᵉ : iterated-Πᵉ Aᵉ) →
    is-torsorialᵉ (multivariable-implicit-htpyᵉ {{Aᵉ}} fᵉ)
  is-torsorial-multivariable-implicit-htpyᵉ nᵉ {{Aᵉ}} fᵉ =
    is-contr-equivᵉ
      ( Σᵉ (iterated-Πᵉ Aᵉ) (multivariable-htpyᵉ {{Aᵉ}} fᵉ))
      ( equiv-totᵉ (λ _ → equiv-multivariable-explicit-implicit-htpyᵉ nᵉ {{Aᵉ}}))
      ( is-torsorial-multivariable-htpyᵉ nᵉ {{Aᵉ}} fᵉ)

abstract
  is-torsorial-multivariable-implicit-htpy-implicitᵉ :
    {lᵉ : Level} (nᵉ : ℕᵉ) {{Aᵉ : telescopeᵉ lᵉ nᵉ}} (fᵉ : iterated-implicit-Πᵉ Aᵉ) →
    is-torsorialᵉ (multivariable-implicit-htpy-implicitᵉ {{Aᵉ}} fᵉ)
  is-torsorial-multivariable-implicit-htpy-implicitᵉ nᵉ {{Aᵉ}} fᵉ =
    is-contr-equivᵉ
      ( Σᵉ (iterated-implicit-Πᵉ Aᵉ) (multivariable-htpy-implicitᵉ {{Aᵉ}} fᵉ))
      ( equiv-totᵉ
        ( λ _ → equiv-multivariable-explicit-implicit-htpy-implicitᵉ nᵉ {{Aᵉ}}))
      ( is-torsorial-multivariable-htpy-implicitᵉ nᵉ {{Aᵉ}} fᵉ)
```

## See also

-ᵉ [Binaryᵉ homotopies](foundation.binary-homotopies.mdᵉ) forᵉ once-iteratedᵉ
  homotopies.ᵉ
