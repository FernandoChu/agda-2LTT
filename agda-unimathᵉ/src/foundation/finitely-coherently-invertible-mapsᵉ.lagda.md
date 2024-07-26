# Finitely coherently invertible maps

```agda
module foundation.finitely-coherently-invertible-mapsᵉ where
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

Weᵉ introduceᵉ theᵉ conceptᵉ ofᵉ beingᵉ aᵉ
{{#conceptᵉ "finitelyᵉ coherentlyᵉ invertibleᵉ map"ᵉ Agda=is-finitely-coherently-invertibleᵉ}}
byᵉ inductionᵉ onᵉ theᵉ
[naturalᵉ numbers](elementary-number-theory.natural-numbers.md).ᵉ Inᵉ theᵉ baseᵉ
case,ᵉ weᵉ sayᵉ thatᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ aᵉ
{{#conceptᵉ "`0`-coherentlyᵉ invertibleᵉ map"ᵉ Agda=is-finitely-coherently-invertibleᵉ}}
ifᵉ itᵉ comesᵉ equippedᵉ with aᵉ mapᵉ `gᵉ : Bᵉ → A`.ᵉ Recursively,ᵉ weᵉ sayᵉ thatᵉ aᵉ mapᵉ
`fᵉ : Aᵉ → B`ᵉ isᵉ anᵉ
{{#conceptᵉ "`nᵉ +ᵉ 1`-coherentlyᵉ invertibleᵉ map"ᵉ Agda=is-finitely-coherently-invertibleᵉ}}
ifᵉ itᵉ comesᵉ equippedᵉ with mapᵉ `gᵉ : Bᵉ → A`ᵉ andᵉ aᵉ familyᵉ ofᵉ mapsᵉ

```text
  rᵉ xᵉ yᵉ : (fᵉ xᵉ ＝ᵉ yᵉ) → (xᵉ ＝ᵉ gᵉ yᵉ)
```

indexedᵉ byᵉ `xᵉ : A`ᵉ andᵉ `yᵉ : B`,ᵉ suchᵉ thatᵉ eachᵉ `rᵉ xᵉ y`ᵉ isᵉ `n`-coherentlyᵉ
invertible.ᵉ

Aᵉ `1`-coherentlyᵉ invertibleᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ thereforeᵉ equivalentlyᵉ describedᵉ
asᵉ aᵉ mapᵉ equippedᵉ with anᵉ inverseᵉ `gᵉ : Bᵉ → A`ᵉ whichᵉ isᵉ simultaneouslyᵉ aᵉ
[retraction](foundation-core.retractions.mdᵉ) andᵉ aᵉ
[section](foundation-core.sections.mdᵉ) ofᵉ `f`.ᵉ Inᵉ otherᵉ words,ᵉ aᵉ `1`-coherentlyᵉ
invertibleᵉ mapᵉ isᵉ justᵉ anᵉ [invertibleᵉ map](foundation-core.invertible-maps.md).ᵉ

Aᵉ `2`-coherentlyᵉ invertibleᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ comesᵉ equippedᵉ with `gᵉ : Bᵉ → A`ᵉ andᵉ
forᵉ eachᵉ `xᵉ : A`ᵉ andᵉ `yᵉ : B`ᵉ twoᵉ mapsᵉ

```text
  rᵉ : (fᵉ xᵉ ＝ᵉ yᵉ) → (xᵉ ＝ᵉ gᵉ yᵉ)
  sᵉ : (xᵉ ＝ᵉ gᵉ yᵉ) → (fᵉ xᵉ ＝ᵉ yᵉ)
```

andᵉ forᵉ eachᵉ `pᵉ : fᵉ xᵉ ＝ᵉ y`ᵉ andᵉ `qᵉ : xᵉ ＝ᵉ gᵉ y`ᵉ aᵉ mapᵉ

```text
  tᵉ pᵉ qᵉ : (rᵉ pᵉ ＝ᵉ qᵉ) → (pᵉ ＝ᵉ sᵉ qᵉ)
  uᵉ pᵉ qᵉ : (pᵉ ＝ᵉ sᵉ qᵉ) → (rᵉ pᵉ ＝ᵉ q).ᵉ
```

Thisᵉ data isᵉ equivalentᵉ to theᵉ data ofᵉ

```text
  rᵉ : (xᵉ : Aᵉ) → gᵉ (fᵉ xᵉ) ＝ᵉ xᵉ
  sᵉ : (yᵉ : Bᵉ) → fᵉ (gᵉ yᵉ) ＝ᵉ yᵉ
  tᵉ : (xᵉ : Aᵉ) → apᵉ fᵉ (rᵉ xᵉ) ＝ᵉ sᵉ (fᵉ xᵉ)
  uᵉ : (yᵉ : Bᵉ) → apᵉ gᵉ (sᵉ yᵉ) ＝ᵉ rᵉ (fᵉ y).ᵉ
```

Theᵉ conditionᵉ ofᵉ beingᵉ aᵉ `n`-coherentlyᵉ invertibleᵉ mapᵉ isᵉ notᵉ aᵉ
[proposition](foundation-core.propositions.mdᵉ) forᵉ anyᵉ `n`.ᵉ Inᵉ fact,ᵉ forᵉ `nᵉ ≥ᵉ 1`ᵉ
theᵉ typeᵉ ofᵉ allᵉ `n`-coherentlyᵉ invertibleᵉ mapsᵉ in aᵉ universeᵉ `𝒰`ᵉ isᵉ equivalentᵉ
to theᵉ typeᵉ ofᵉ mapsᵉ `sphereᵉ (nᵉ +ᵉ 1ᵉ) → 𝒰`ᵉ ofᵉ `nᵉ +ᵉ 1`-spheresᵉ in theᵉ universeᵉ `𝒰`.ᵉ

## Definitions

### The predicate of being an `n`-coherently invertible map

```agda
data
  is-finitely-coherently-invertibleᵉ
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} :
    (nᵉ : ℕᵉ) (fᵉ : Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  where
  is-zero-coherently-invertibleᵉ :
    (fᵉ : Aᵉ → Bᵉ) → (Bᵉ → Aᵉ) → is-finitely-coherently-invertibleᵉ 0 fᵉ
  is-succ-coherently-invertibleᵉ :
    (nᵉ : ℕᵉ)
    (fᵉ : Aᵉ → Bᵉ) (gᵉ : Bᵉ → Aᵉ) (Hᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ) → (fᵉ xᵉ ＝ᵉ yᵉ) → (xᵉ ＝ᵉ gᵉ yᵉ)) →
    ((xᵉ : Aᵉ) (yᵉ : Bᵉ) → is-finitely-coherently-invertibleᵉ nᵉ (Hᵉ xᵉ yᵉ)) →
    is-finitely-coherently-invertibleᵉ (succ-ℕᵉ nᵉ) fᵉ
```