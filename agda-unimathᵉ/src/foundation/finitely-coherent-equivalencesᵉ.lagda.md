# Finitely coherent equivalences

```agda
module foundation.finitely-coherent-equivalencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ conditionᵉ ofᵉ beingᵉ aᵉ
{{#conceptᵉ "finitelyᵉ coherentᵉ equivalence"ᵉ Agda=is-finitely-coherent-equivalenceᵉ}}
isᵉ introducedᵉ byᵉ inductionᵉ onᵉ theᵉ
[naturalᵉ numbers](elementary-number-theory.natural-numbers.md).ᵉ Inᵉ theᵉ baseᵉ
case,ᵉ weᵉ sayᵉ thatᵉ anyᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ aᵉ
{{#conceptᵉ "`0`-coherentᵉ equivalence"ᵉ Agda=is-finitely-coherent-equivalence}}.ᵉ
Recursively,ᵉ weᵉ sayᵉ thatᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ anᵉ
{{#conceptᵉ "`nᵉ +ᵉ 1`-coherentᵉ equivalence"ᵉ Agda=is-finitely-coherent-equivalenceᵉ}}
ifᵉ itᵉ comesᵉ equippedᵉ with aᵉ mapᵉ `gᵉ : Bᵉ → A`ᵉ andᵉ aᵉ familyᵉ ofᵉ mapsᵉ

```text
  rᵉ xᵉ yᵉ : (fᵉ xᵉ ＝ᵉ yᵉ) → (xᵉ ＝ᵉ gᵉ yᵉ)
```

indexedᵉ byᵉ `xᵉ : A`ᵉ andᵉ `yᵉ : B`,ᵉ suchᵉ thatᵉ eachᵉ `rᵉ xᵉ y`ᵉ isᵉ anᵉ `n`-coherentᵉ
equivalence.ᵉ

Byᵉ theᵉ equivalenceᵉ ofᵉ [retractingᵉ homotopies](foundation-core.retractions.mdᵉ)
andᵉ
[transpositionᵉ operationsᵉ ofᵉ identifications](foundation.transposition-identifications-along-retractions.mdᵉ)
itᵉ thereforeᵉ followsᵉ thatᵉ aᵉ `1`-coherentᵉ equivalenceᵉ isᵉ equivalentlyᵉ describedᵉ
asᵉ aᵉ mapᵉ equippedᵉ with aᵉ retraction.ᵉ Aᵉ `2`-coherentᵉ equivalenceᵉ isᵉ aᵉ mapᵉ
`fᵉ : Aᵉ → B`ᵉ equippedᵉ with `gᵉ : Bᵉ → A`ᵉ andᵉ forᵉ eachᵉ `xᵉ : A`ᵉ andᵉ `yᵉ : B`ᵉ aᵉ mapᵉ
`rᵉ xᵉ yᵉ : (fᵉ xᵉ ＝ᵉ yᵉ) → (xᵉ ＝ᵉ gᵉ y)`,ᵉ equippedᵉ with

```text
  sᵉ xᵉ yᵉ : (xᵉ ＝ᵉ gᵉ yᵉ) → (fᵉ xᵉ ＝ᵉ yᵉ)
```

andᵉ forᵉ eachᵉ `pᵉ : fᵉ xᵉ ＝ᵉ y`ᵉ andᵉ `qᵉ : xᵉ ＝ᵉ gᵉ y`ᵉ aᵉ mapᵉ

```text
  tᵉ pᵉ qᵉ : (rᵉ xᵉ yᵉ pᵉ ＝ᵉ qᵉ) → (pᵉ ＝ᵉ sᵉ xᵉ yᵉ q).ᵉ
```

Thisᵉ data isᵉ equivalentᵉ to theᵉ data ofᵉ aᵉ
[coherentlyᵉ invertibleᵉ map](foundation-core.coherently-invertible-maps.mdᵉ)

```text
  rᵉ : (xᵉ : Aᵉ) → gᵉ (fᵉ xᵉ) ＝ᵉ xᵉ
  sᵉ : (yᵉ : Bᵉ) → fᵉ (gᵉ yᵉ) ＝ᵉ yᵉ
  tᵉ : (xᵉ : Aᵉ) → apᵉ fᵉ (rᵉ xᵉ) ＝ᵉ sᵉ (fᵉ x).ᵉ
```

Theᵉ conditionᵉ ofᵉ beingᵉ anᵉ `n`-coherentᵉ equivalenceᵉ isᵉ aᵉ
[proposition](foundation-core.propositions.mdᵉ) forᵉ eachᵉ `nᵉ ≥ᵉ 2`,ᵉ andᵉ thisᵉ
propositionᵉ isᵉ equivalentᵉ to beingᵉ anᵉ equivalence.ᵉ

## Definitions

### The predicate of being an `n`-coherent equivalence

```agda
data
  is-finitely-coherent-equivalenceᵉ
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} :
    (nᵉ : ℕᵉ) (fᵉ : Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  where
  is-zero-coherent-equivalenceᵉ :
    (fᵉ : Aᵉ → Bᵉ) → is-finitely-coherent-equivalenceᵉ 0 fᵉ
  is-succ-coherent-equivalenceᵉ :
    (nᵉ : ℕᵉ)
    (fᵉ : Aᵉ → Bᵉ) (gᵉ : Bᵉ → Aᵉ) (Hᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ) → (fᵉ xᵉ ＝ᵉ yᵉ) → (xᵉ ＝ᵉ gᵉ yᵉ)) →
    ((xᵉ : Aᵉ) (yᵉ : Bᵉ) → is-finitely-coherent-equivalenceᵉ nᵉ (Hᵉ xᵉ yᵉ)) →
    is-finitely-coherent-equivalenceᵉ (succ-ℕᵉ nᵉ) fᵉ
```