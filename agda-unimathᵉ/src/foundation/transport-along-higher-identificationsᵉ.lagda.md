# Transport along higher identifications

```agda
module foundation.transport-along-higher-identificationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-homotopiesᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-algebraᵉ
open import foundation.path-algebraᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import foundation-core.identity-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
open import foundation-core.whiskering-homotopies-concatenationᵉ
```

</details>

### The action on identifications of transport

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ}
  where

  tr²ᵉ : (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (αᵉ : pᵉ ＝ᵉ p'ᵉ) (bᵉ : Bᵉ xᵉ) → (trᵉ Bᵉ pᵉ bᵉ) ＝ᵉ (trᵉ Bᵉ p'ᵉ bᵉ)
  tr²ᵉ Bᵉ αᵉ bᵉ = apᵉ (λ tᵉ → trᵉ Bᵉ tᵉ bᵉ) αᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ}
  {αᵉ α'ᵉ : pᵉ ＝ᵉ p'ᵉ}
  where

  tr³ᵉ : (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (βᵉ : αᵉ ＝ᵉ α'ᵉ) (bᵉ : Bᵉ xᵉ) → (tr²ᵉ Bᵉ αᵉ bᵉ) ＝ᵉ (tr²ᵉ Bᵉ α'ᵉ bᵉ)
  tr³ᵉ Bᵉ βᵉ bᵉ = apᵉ (λ tᵉ → tr²ᵉ Bᵉ tᵉ bᵉ) βᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ}
  {αᵉ α'ᵉ : pᵉ ＝ᵉ p'ᵉ} {γᵉ γ'ᵉ : αᵉ ＝ᵉ α'ᵉ}
  where

  tr⁴ᵉ : (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (ψᵉ : γᵉ ＝ᵉ γ'ᵉ) → (tr³ᵉ Bᵉ γᵉ) ~ᵉ (tr³ᵉ Bᵉ γ'ᵉ)
  tr⁴ᵉ Bᵉ ψᵉ bᵉ = apᵉ (λ tᵉ → tr³ᵉ Bᵉ tᵉ bᵉ) ψᵉ
```

### Computing 2-dimensional transport in a family of identifications with a fixed source

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ cᵉ : Aᵉ} {qᵉ q'ᵉ : bᵉ ＝ᵉ cᵉ}
  where

  tr²-Id-rightᵉ :
    (αᵉ : qᵉ ＝ᵉ q'ᵉ) (pᵉ : aᵉ ＝ᵉ bᵉ) →
    coherence-square-identificationsᵉ
      ( tr-Id-rightᵉ qᵉ pᵉ)
      ( tr²ᵉ (Idᵉ aᵉ) αᵉ pᵉ)
      ( left-whisker-concatᵉ pᵉ αᵉ)
      ( tr-Id-rightᵉ q'ᵉ pᵉ)
  tr²-Id-rightᵉ αᵉ pᵉ =
    inv-nat-htpyᵉ (λ (tᵉ : bᵉ ＝ᵉ cᵉ) → tr-Id-rightᵉ tᵉ pᵉ) αᵉ
```

### Coherences and algebraic identities for `tr²`

#### Computing `tr²` along the concatenation of identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ : Aᵉ}
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  tr²-concatᵉ :
    {pᵉ p'ᵉ p''ᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ p'ᵉ) (βᵉ : p'ᵉ ＝ᵉ p''ᵉ) →
    tr²ᵉ Bᵉ (αᵉ ∙ᵉ βᵉ) ~ᵉ tr²ᵉ Bᵉ αᵉ ∙hᵉ tr²ᵉ Bᵉ βᵉ
  tr²-concatᵉ αᵉ βᵉ bᵉ = ap-concatᵉ (λ tᵉ → trᵉ Bᵉ tᵉ bᵉ) αᵉ βᵉ
```

#### Computing `tr²` along the inverse of an identification

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ : Aᵉ}
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  tr²-invᵉ :
    {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ p'ᵉ) →
    tr²ᵉ Bᵉ (invᵉ αᵉ) ~ᵉ inv-htpyᵉ (tr²ᵉ Bᵉ αᵉ)
  tr²-invᵉ αᵉ bᵉ = ap-invᵉ (λ tᵉ → trᵉ Bᵉ tᵉ bᵉ) αᵉ

  left-inverse-law-tr²ᵉ :
    {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ p'ᵉ) →
    tr²ᵉ Bᵉ (invᵉ αᵉ) ∙hᵉ tr²ᵉ Bᵉ αᵉ ~ᵉ refl-htpyᵉ
  left-inverse-law-tr²ᵉ αᵉ =
    ( right-whisker-concat-htpyᵉ (tr²-invᵉ αᵉ) (tr²ᵉ Bᵉ αᵉ)) ∙hᵉ
    ( left-inv-htpyᵉ (tr²ᵉ Bᵉ αᵉ))

  right-inverse-law-tr²ᵉ :
    {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ p'ᵉ) →
    tr²ᵉ Bᵉ αᵉ ∙hᵉ tr²ᵉ Bᵉ (invᵉ αᵉ) ~ᵉ refl-htpyᵉ
  right-inverse-law-tr²ᵉ αᵉ =
    ( left-whisker-concat-htpyᵉ (tr²ᵉ Bᵉ αᵉ) (tr²-invᵉ αᵉ)) ∙hᵉ
    ( right-inv-htpyᵉ (tr²ᵉ Bᵉ αᵉ))
```

#### Computing `tr²` along the unit laws for vertical concatenation of identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ : Aᵉ}
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  tr²-left-unitᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) → tr²ᵉ Bᵉ left-unitᵉ ~ᵉ tr-concatᵉ reflᵉ pᵉ
  tr²-left-unitᵉ pᵉ = refl-htpyᵉ

  tr²-right-unitᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) → tr²ᵉ Bᵉ right-unitᵉ ~ᵉ tr-concatᵉ pᵉ reflᵉ
  tr²-right-unitᵉ reflᵉ = refl-htpyᵉ
```

#### Computing `tr²` along the whiskering of identification

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ zᵉ : Aᵉ}
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  tr²-left-whiskerᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) {qᵉ q'ᵉ : yᵉ ＝ᵉ zᵉ} (βᵉ : qᵉ ＝ᵉ q'ᵉ) →
    coherence-square-homotopiesᵉ
      ( tr-concatᵉ pᵉ qᵉ)
      ( tr²ᵉ Bᵉ (left-whisker-concatᵉ pᵉ βᵉ))
      ( tr²ᵉ Bᵉ βᵉ ·rᵉ trᵉ Bᵉ pᵉ)
      ( tr-concatᵉ pᵉ q'ᵉ)
  tr²-left-whiskerᵉ reflᵉ reflᵉ = refl-htpyᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ zᵉ : Aᵉ}
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  tr²-right-whiskerᵉ :
    {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ p'ᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    coherence-square-homotopiesᵉ
      ( tr-concatᵉ pᵉ qᵉ)
      ( tr²ᵉ Bᵉ (right-whisker-concatᵉ αᵉ qᵉ))
      ( ( trᵉ Bᵉ qᵉ) ·lᵉ (tr²ᵉ Bᵉ αᵉ))
      ( tr-concatᵉ p'ᵉ qᵉ)
  tr²-right-whiskerᵉ reflᵉ reflᵉ = inv-htpyᵉ right-unit-htpyᵉ
```

### Coherences and algebraic identities for `tr³`

#### Computing `tr³` along the concatenation of identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  {xᵉ yᵉ : Aᵉ} {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ} {αᵉ α'ᵉ α''ᵉ : pᵉ ＝ᵉ p'ᵉ}
  where

  tr³-concatᵉ :
    (γᵉ : αᵉ ＝ᵉ α'ᵉ) (δᵉ : α'ᵉ ＝ᵉ α''ᵉ) → tr³ᵉ Bᵉ (γᵉ ∙ᵉ δᵉ) ~ᵉ (tr³ᵉ Bᵉ γᵉ) ∙hᵉ (tr³ᵉ Bᵉ δᵉ)
  tr³-concatᵉ γᵉ δᵉ bᵉ = ap-concatᵉ (λ tᵉ → tr²ᵉ Bᵉ tᵉ bᵉ) γᵉ δᵉ
```

#### Computing `tr³` along the horizontal concatenation of identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ p'ᵉ p''ᵉ : xᵉ ＝ᵉ yᵉ}
  {αᵉ α'ᵉ : pᵉ ＝ᵉ p'ᵉ} {βᵉ β'ᵉ : p'ᵉ ＝ᵉ p''ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  tr³-horizontal-concatᵉ :
    (γᵉ : αᵉ ＝ᵉ α'ᵉ) (δᵉ : βᵉ ＝ᵉ β'ᵉ) →
    coherence-square-homotopiesᵉ
      ( tr²-concatᵉ αᵉ βᵉ)
      ( tr³ᵉ Bᵉ (horizontal-concat-Id²ᵉ γᵉ δᵉ))
      ( horizontal-concat-htpy²ᵉ (tr³ᵉ Bᵉ γᵉ) (tr³ᵉ Bᵉ δᵉ))
      ( tr²-concatᵉ α'ᵉ β'ᵉ)
  tr³-horizontal-concatᵉ reflᵉ reflᵉ = inv-htpyᵉ right-unit-htpyᵉ
```

#### Computing `tr³` along the inverse of an identification

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ} {αᵉ α'ᵉ : pᵉ ＝ᵉ p'ᵉ}
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  tr³-invᵉ :
    (γᵉ : αᵉ ＝ᵉ α'ᵉ) →
    tr³ᵉ Bᵉ (invᵉ γᵉ) ~ᵉ inv-htpyᵉ (tr³ᵉ Bᵉ γᵉ)
  tr³-invᵉ γᵉ bᵉ = ap-invᵉ (λ tᵉ → tr²ᵉ Bᵉ tᵉ bᵉ) γᵉ

  left-inv-law-tr³ᵉ :
    (γᵉ : αᵉ ＝ᵉ α'ᵉ) →
    tr³ᵉ Bᵉ (invᵉ γᵉ) ∙hᵉ tr³ᵉ Bᵉ γᵉ ~ᵉ refl-htpyᵉ
  left-inv-law-tr³ᵉ γᵉ =
    ( right-whisker-concat-htpyᵉ (tr³-invᵉ γᵉ) (tr³ᵉ Bᵉ γᵉ)) ∙hᵉ
    ( left-inv-htpyᵉ (tr³ᵉ Bᵉ γᵉ))

  right-inv-law-tr³ᵉ :
    (γᵉ : αᵉ ＝ᵉ α'ᵉ) →
    tr³ᵉ Bᵉ γᵉ ∙hᵉ tr³ᵉ Bᵉ (invᵉ γᵉ) ~ᵉ refl-htpyᵉ
  right-inv-law-tr³ᵉ γᵉ =
    ( left-whisker-concat-htpyᵉ (tr³ᵉ Bᵉ γᵉ) (tr³-invᵉ γᵉ)) ∙hᵉ
    ( right-inv-htpyᵉ (tr³ᵉ Bᵉ γᵉ))
```

#### Computing `tr³` along the unit laws for vertical concatenation of identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ}
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  tr³-right-unitᵉ :
    (αᵉ : pᵉ ＝ᵉ qᵉ) →
    tr³ᵉ Bᵉ (right-unitᵉ {pᵉ = αᵉ}) ~ᵉ tr²-concatᵉ αᵉ reflᵉ ∙hᵉ right-unit-htpyᵉ
  tr³-right-unitᵉ reflᵉ = refl-htpyᵉ

  tr³-left-unitᵉ :
    (αᵉ : pᵉ ＝ᵉ qᵉ) →
    tr³ᵉ Bᵉ (left-unitᵉ {pᵉ = αᵉ}) ~ᵉ tr²-concatᵉ reflᵉ αᵉ ∙hᵉ left-unit-htpyᵉ
  tr³-left-unitᵉ αᵉ = refl-htpyᵉ
```

#### Computing tr³ along the unit laws for whiskering of identifications

Theseᵉ coherencesᵉ takeᵉ theᵉ formᵉ ofᵉ theᵉ followingᵉ commutativeᵉ diagrams.ᵉ Noteᵉ thatᵉ
thereᵉ isᵉ anᵉ asymmetryᵉ betweenᵉ theᵉ leftᵉ andᵉ rightᵉ coherenceᵉ lawsᵉ dueᵉ to theᵉ
asymmetryᵉ in theᵉ definitionᵉ ofᵉ concatenationᵉ ofᵉ identifications.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ : Aᵉ}
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  tr³-left-unit-law-left-whisker-concatᵉ :
    {qᵉ q'ᵉ : xᵉ ＝ᵉ yᵉ} (βᵉ : qᵉ ＝ᵉ q'ᵉ) →
    coherence-square-homotopiesᵉ
      ( inv-htpyᵉ right-unit-htpyᵉ)
      ( refl-htpyᵉ)
      ( tr²-left-whiskerᵉ reflᵉ βᵉ)
      ( tr³ᵉ Bᵉ (left-unit-law-left-whisker-concatᵉ βᵉ))
  tr³-left-unit-law-left-whisker-concatᵉ reflᵉ = refl-htpyᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ : Aᵉ}
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  tr³-right-unit-law-right-whisker-concatᵉ :
    {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ p'ᵉ) →
    coherence-square-homotopiesᵉ
      ( ( tr²-concatᵉ (right-whisker-concatᵉ αᵉ reflᵉ) right-unitᵉ) ∙hᵉ
        ( left-whisker-concat-htpyᵉ
          ( tr²ᵉ Bᵉ (right-whisker-concatᵉ αᵉ reflᵉ))
          ( tr²-right-unitᵉ p'ᵉ)))
      ( tr³ᵉ Bᵉ (invᵉ (right-unit-law-right-whisker-concatᵉ αᵉ)))
      ( tr²-right-whiskerᵉ αᵉ reflᵉ)
      ( ( tr²-concatᵉ right-unitᵉ αᵉ) ∙hᵉ
        ( right-whisker-concat-htpyᵉ (tr²-right-unitᵉ pᵉ) (tr²ᵉ Bᵉ αᵉ)) ∙hᵉ
        ( inv-htpyᵉ
          ( left-whisker-concat-htpyᵉ
            ( tr-concatᵉ pᵉ reflᵉ)
            ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ αᵉ)))))
  tr³-right-unit-law-right-whisker-concatᵉ {pᵉ = reflᵉ} {p'ᵉ = reflᵉ} reflᵉ =
    refl-htpyᵉ
```

Theᵉ aboveᵉ coherencesᵉ haveᵉ simplifiedᵉ formsᵉ whenᵉ weᵉ considerᵉ 2-loopsᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ : Aᵉ}
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  tr³-left-unit-law-left-whisker-concat-Ω²ᵉ :
    (βᵉ : reflᵉ {xᵉ = xᵉ} ＝ᵉ reflᵉ) →
    coherence-square-homotopiesᵉ
      ( inv-htpyᵉ right-unit-htpyᵉ)
      ( refl-htpyᵉ)
      ( tr²-left-whiskerᵉ reflᵉ βᵉ)
      ( tr³ᵉ Bᵉ (left-unit-law-left-whisker-concatᵉ βᵉ))
  tr³-left-unit-law-left-whisker-concat-Ω²ᵉ βᵉ =
    tr³-left-unit-law-left-whisker-concatᵉ βᵉ

  tr³-right-unit-law-right-whisker-concat-Ω²ᵉ :
    (αᵉ : reflᵉ {xᵉ = xᵉ} ＝ᵉ reflᵉ) →
    coherence-square-homotopiesᵉ
      ( inv-htpyᵉ right-unit-htpyᵉ)
      ( tr³ᵉ Bᵉ (invᵉ (right-unit-law-right-whisker-concatᵉ αᵉ ∙ᵉ right-unitᵉ)))
      ( tr²-right-whiskerᵉ αᵉ reflᵉ)
      ( inv-htpyᵉ (left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ αᵉ)))
  tr³-right-unit-law-right-whisker-concat-Ω²ᵉ αᵉ =
    concat-top-homotopy-coherence-square-homotopiesᵉ
      ( ( tr³ᵉ Bᵉ (invᵉ right-unitᵉ)) ∙hᵉ
        ( tr²-concatᵉ (right-whisker-concatᵉ αᵉ reflᵉ) reflᵉ))
      ( tr³ᵉ
        ( Bᵉ)
        ( invᵉ (right-unit-law-right-whisker-concatᵉ αᵉ ∙ᵉ right-unitᵉ)))
      ( tr²-right-whiskerᵉ αᵉ reflᵉ)
      ( inv-htpyᵉ (left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ αᵉ)))
      ( ( right-whisker-concat-htpyᵉ
          ( tr³-invᵉ right-unitᵉ)
          ( tr²-concatᵉ (right-whisker-concatᵉ αᵉ reflᵉ) reflᵉ)) ∙hᵉ
        ( inv-htpyᵉ
          ( left-transpose-htpy-concatᵉ
            ( tr³ᵉ Bᵉ right-unitᵉ)
            ( inv-htpyᵉ right-unit-htpyᵉ)
            ( tr²-concatᵉ (right-whisker-concatᵉ αᵉ reflᵉ) reflᵉ)
            ( inv-htpyᵉ
              ( right-transpose-htpy-concatᵉ
                ( tr²-concatᵉ (right-whisker-concatᵉ αᵉ reflᵉ) reflᵉ)
                ( right-unit-htpyᵉ)
                ( tr³ᵉ Bᵉ right-unitᵉ)
                ( inv-htpyᵉ
                  ( tr³-right-unitᵉ (right-whisker-concatᵉ αᵉ reflᵉ))))))))
      ( concat-left-homotopy-coherence-square-homotopiesᵉ
        ( ( tr³ᵉ Bᵉ (invᵉ right-unitᵉ)) ∙hᵉ
          ( tr²-concatᵉ (right-whisker-concatᵉ αᵉ reflᵉ) reflᵉ))
        ( ( tr³ᵉ Bᵉ (invᵉ right-unitᵉ)) ∙hᵉ
          ( tr³ᵉ Bᵉ (invᵉ (right-unit-law-right-whisker-concatᵉ αᵉ))))
        ( tr²-right-whiskerᵉ αᵉ reflᵉ)
        ( inv-htpyᵉ (left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ αᵉ)))
        ( ( inv-htpyᵉ
            ( tr³-concatᵉ
              ( invᵉ right-unitᵉ)
              ( invᵉ (right-unit-law-right-whisker-concatᵉ αᵉ)))) ∙hᵉ
          ( tr⁴ᵉ
            ( Bᵉ)
            ( invᵉ
              ( distributive-inv-concatᵉ
                ( right-unit-law-right-whisker-concatᵉ αᵉ) (right-unitᵉ)))))
        ( left-whisker-concat-coherence-square-homotopiesᵉ
          ( tr³ᵉ Bᵉ (invᵉ right-unitᵉ))
          ( tr²-concatᵉ (right-whisker-concatᵉ αᵉ reflᵉ) reflᵉ)
          ( tr³ᵉ Bᵉ (invᵉ (right-unit-law-right-whisker-concatᵉ αᵉ)))
          ( tr²-right-whiskerᵉ αᵉ reflᵉ)
          ( inv-htpyᵉ (left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ αᵉ)))
          ( concat-bottom-homotopy-coherence-square-homotopiesᵉ
            ( tr²-concatᵉ (right-whisker-concatᵉ αᵉ reflᵉ) reflᵉ)
            ( tr³ᵉ Bᵉ (invᵉ (right-unit-law-right-whisker-concatᵉ αᵉ)))
            ( tr²-right-whiskerᵉ αᵉ reflᵉ)
            ( inv-htpyᵉ
              ( left-whisker-concat-htpyᵉ
                ( refl-htpyᵉ)
                ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ αᵉ))))
            ( ap-inv-htpyᵉ
              ( left-unit-law-left-whisker-concat-htpyᵉ
                ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ αᵉ))))
            ( concat-top-homotopy-coherence-square-homotopiesᵉ
              ( ( tr²-concatᵉ (right-whisker-concatᵉ αᵉ reflᵉ) reflᵉ) ∙hᵉ
                ( refl-htpyᵉ))
              ( tr³ᵉ Bᵉ (invᵉ (right-unit-law-right-whisker-concatᵉ αᵉ)))
              ( tr²-right-whiskerᵉ αᵉ reflᵉ)
              ( inv-htpyᵉ
                ( left-whisker-concat-htpyᵉ
                  ( refl-htpyᵉ)
                  ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ αᵉ))))
              ( right-unit-htpyᵉ)
              ( tr³-right-unit-law-right-whisker-concatᵉ αᵉ)))))
```

#### Computing `tr³` along `commutative-left-whisker-right-whisker-concat`

Thisᵉ coherenceᵉ naturallyᵉ takesᵉ theᵉ formᵉ ofᵉ aᵉ fillerᵉ forᵉ aᵉ cubeᵉ whoseᵉ leftᵉ faceᵉ
isᵉ

```text
tr³ᵉ Bᵉ (commutative-left-whisker-right-whisker-concatᵉ βᵉ αᵉ)
```

andᵉ whoseᵉ rightᵉ faceᵉ isᵉ

```text
commutative-right-whisker-left-whisker-htpyᵉ (tr²ᵉ Bᵉ βᵉ) (tr²ᵉ Bᵉ αᵉ)
```

However,ᵉ thisᵉ cubeᵉ hasᵉ trivialᵉ frontᵉ andᵉ backᵉ faces.ᵉ Thus,ᵉ weᵉ onlyᵉ proveᵉ aᵉ
simplifiedᵉ formᵉ ofᵉ theᵉ coherence.ᵉ

##### Non-trivial faces of the cube

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ zᵉ : Aᵉ}
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ} {qᵉ q'ᵉ : yᵉ ＝ᵉ zᵉ}
  where

  tr²-left-whisker-concat-tr²-right-whisker-concatᵉ :
    (βᵉ : qᵉ ＝ᵉ q'ᵉ) (αᵉ : pᵉ ＝ᵉ p'ᵉ) →
    coherence-square-homotopiesᵉ
      ( tr-concatᵉ pᵉ qᵉ)
      ( ( tr²ᵉ Bᵉ (left-whisker-concatᵉ pᵉ βᵉ)) ∙hᵉ
        ( tr²ᵉ Bᵉ (right-whisker-concatᵉ αᵉ q'ᵉ)))
      ( (tr²ᵉ Bᵉ βᵉ ·rᵉ trᵉ Bᵉ pᵉ) ∙hᵉ (trᵉ Bᵉ q'ᵉ ·lᵉ tr²ᵉ Bᵉ αᵉ))
      ( tr-concatᵉ p'ᵉ q'ᵉ)
  tr²-left-whisker-concat-tr²-right-whisker-concatᵉ βᵉ αᵉ =
    ( vertical-pasting-coherence-square-homotopiesᵉ
      ( tr-concatᵉ pᵉ qᵉ)
      ( tr²ᵉ Bᵉ (left-whisker-concatᵉ pᵉ βᵉ))
      ( right-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ) (trᵉ Bᵉ pᵉ))
      ( tr-concatᵉ pᵉ q'ᵉ)
      ( tr²ᵉ Bᵉ (right-whisker-concatᵉ αᵉ q'ᵉ))
      ( left-whisker-compᵉ (trᵉ Bᵉ q'ᵉ) (tr²ᵉ Bᵉ αᵉ))
      ( tr-concatᵉ p'ᵉ q'ᵉ)
      ( tr²-left-whiskerᵉ pᵉ βᵉ)
      ( tr²-right-whiskerᵉ αᵉ q'ᵉ))

  tr²-concat-left-whisker-concat-right-whisker-concatᵉ :
    (βᵉ : qᵉ ＝ᵉ q'ᵉ) (αᵉ : pᵉ ＝ᵉ p'ᵉ) →
    coherence-square-homotopiesᵉ
      ( tr-concatᵉ pᵉ qᵉ)
      ( tr²ᵉ Bᵉ (left-whisker-concatᵉ pᵉ βᵉ ∙ᵉ right-whisker-concatᵉ αᵉ q'ᵉ))
      ( (tr²ᵉ Bᵉ βᵉ ·rᵉ trᵉ Bᵉ pᵉ) ∙hᵉ (trᵉ Bᵉ q'ᵉ ·lᵉ tr²ᵉ Bᵉ αᵉ))
      ( tr-concatᵉ p'ᵉ q'ᵉ)
  tr²-concat-left-whisker-concat-right-whisker-concatᵉ βᵉ αᵉ =
    ( right-whisker-concat-htpyᵉ
      ( tr²-concatᵉ
        ( left-whisker-concatᵉ pᵉ βᵉ)
        ( right-whisker-concatᵉ αᵉ q'ᵉ))
      ( tr-concatᵉ p'ᵉ q'ᵉ)) ∙hᵉ
    ( tr²-left-whisker-concat-tr²-right-whisker-concatᵉ βᵉ αᵉ)

  tr²-right-whisker-concat-tr²-left-whisker-concatᵉ :
    (αᵉ : pᵉ ＝ᵉ p'ᵉ) (βᵉ : qᵉ ＝ᵉ q'ᵉ) →
    coherence-square-homotopiesᵉ
      ( tr-concatᵉ pᵉ qᵉ)
      ( ( tr²ᵉ Bᵉ (right-whisker-concatᵉ αᵉ qᵉ)) ∙hᵉ
        ( tr²ᵉ Bᵉ (left-whisker-concatᵉ p'ᵉ βᵉ)))
      ( (trᵉ Bᵉ qᵉ ·lᵉ tr²ᵉ Bᵉ αᵉ) ∙hᵉ (tr²ᵉ Bᵉ βᵉ ·rᵉ trᵉ Bᵉ p'ᵉ))
      ( tr-concatᵉ p'ᵉ q'ᵉ)
  tr²-right-whisker-concat-tr²-left-whisker-concatᵉ αᵉ βᵉ =
    ( vertical-pasting-coherence-square-homotopiesᵉ
      ( tr-concatᵉ pᵉ qᵉ)
      ( tr²ᵉ Bᵉ (right-whisker-concatᵉ αᵉ qᵉ))
      ( left-whisker-compᵉ (trᵉ Bᵉ qᵉ) (tr²ᵉ Bᵉ αᵉ))
      ( tr-concatᵉ p'ᵉ qᵉ)
      ( tr²ᵉ Bᵉ (left-whisker-concatᵉ p'ᵉ βᵉ))
      ( right-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ) (trᵉ Bᵉ p'ᵉ))
      ( tr-concatᵉ p'ᵉ q'ᵉ)
      ( tr²-right-whiskerᵉ αᵉ qᵉ)
      ( tr²-left-whiskerᵉ p'ᵉ βᵉ))

  tr²-concat-right-whisker-concat-left-whisker-concatᵉ :
    (αᵉ : pᵉ ＝ᵉ p'ᵉ) (βᵉ : qᵉ ＝ᵉ q'ᵉ) →
    coherence-square-homotopiesᵉ
      ( tr-concatᵉ pᵉ qᵉ)
      ( tr²ᵉ Bᵉ (right-whisker-concatᵉ αᵉ qᵉ ∙ᵉ left-whisker-concatᵉ p'ᵉ βᵉ))
      ( ( trᵉ Bᵉ qᵉ ·lᵉ tr²ᵉ Bᵉ αᵉ) ∙hᵉ (tr²ᵉ Bᵉ βᵉ ·rᵉ trᵉ Bᵉ p'ᵉ))
      ( tr-concatᵉ p'ᵉ q'ᵉ)
  tr²-concat-right-whisker-concat-left-whisker-concatᵉ αᵉ βᵉ =
    ( right-whisker-concat-htpyᵉ
      ( tr²-concatᵉ
        ( right-whisker-concatᵉ αᵉ qᵉ)
        ( left-whisker-concatᵉ p'ᵉ βᵉ))
      ( tr-concatᵉ p'ᵉ q'ᵉ)) ∙hᵉ
    ( tr²-right-whisker-concat-tr²-left-whisker-concatᵉ αᵉ βᵉ)
```

##### The coherence itself

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ yᵉ zᵉ : Aᵉ}
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  tr³-commutative-left-whisker-right-whisker-concatᵉ :
    {qᵉ q'ᵉ : yᵉ ＝ᵉ zᵉ} (βᵉ : qᵉ ＝ᵉ q'ᵉ) {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ p'ᵉ) →
    coherence-square-homotopiesᵉ
      ( tr²-concat-left-whisker-concat-right-whisker-concatᵉ βᵉ αᵉ)
      ( right-whisker-concat-htpyᵉ
        ( tr³ᵉ
          ( Bᵉ)
          ( commutative-left-whisker-right-whisker-concatᵉ βᵉ αᵉ))
        ( tr-concatᵉ p'ᵉ q'ᵉ))
      ( left-whisker-concat-htpyᵉ
        ( tr-concatᵉ pᵉ qᵉ)
        ( commutative-right-whisker-left-whisker-htpyᵉ
          ( tr²ᵉ Bᵉ βᵉ)
          ( tr²ᵉ Bᵉ αᵉ)))
      ( tr²-concat-right-whisker-concat-left-whisker-concatᵉ αᵉ βᵉ)
  tr³-commutative-left-whisker-right-whisker-concatᵉ
    {qᵉ = reflᵉ} reflᵉ {pᵉ = reflᵉ} reflᵉ =
    refl-htpyᵉ
```

##### A simplification of the non-trivial faces of the cube when `α` and `β` are 2-loops

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {aᵉ : Aᵉ}
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  tr²-left-whisker-concat-tr²-right-whisker-concat-Ω²ᵉ :
    (αᵉ βᵉ : reflᵉ {xᵉ = aᵉ} ＝ᵉ reflᵉ) →
    ( ( tr²ᵉ Bᵉ (left-whisker-concatᵉ reflᵉ αᵉ)) ∙hᵉ
      ( tr²ᵉ Bᵉ (right-whisker-concatᵉ βᵉ reflᵉ))) ~ᵉ
    ( tr²ᵉ Bᵉ αᵉ ∙hᵉ (idᵉ ·lᵉ (tr²ᵉ Bᵉ βᵉ)))
  tr²-left-whisker-concat-tr²-right-whisker-concat-Ω²ᵉ αᵉ βᵉ =
    horizontal-concat-htpy²ᵉ
      ( tr³ᵉ Bᵉ (left-unit-law-left-whisker-concatᵉ αᵉ))
      ( ( tr³ᵉ
          ( Bᵉ)
          ( invᵉ (right-unit-law-right-whisker-concatᵉ βᵉ ∙ᵉ right-unitᵉ))) ∙hᵉ
        ( inv-htpyᵉ (left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ))))

  compute-tr²-left-whisker-concat-tr²-right-whisker-concat-Ω²ᵉ :
    (αᵉ βᵉ : reflᵉ {xᵉ = aᵉ} ＝ᵉ reflᵉ) →
    ( inv-coherence-square-homotopies-horizontal-reflᵉ
      ( ( tr²ᵉ Bᵉ (left-whisker-concatᵉ reflᵉ αᵉ)) ∙hᵉ
        ( tr²ᵉ Bᵉ (right-whisker-concatᵉ βᵉ reflᵉ)))
      ( tr²ᵉ Bᵉ αᵉ ∙hᵉ idᵉ ·lᵉ (tr²ᵉ Bᵉ βᵉ))
      ( tr²-left-whisker-concat-tr²-right-whisker-concatᵉ αᵉ βᵉ)) ~ᵉ
    ( tr²-left-whisker-concat-tr²-right-whisker-concat-Ω²ᵉ αᵉ βᵉ)
  compute-tr²-left-whisker-concat-tr²-right-whisker-concat-Ω²ᵉ αᵉ βᵉ =
    ( vertical-pasting-inv-coherence-square-homotopies-horizontal-reflᵉ
      ( tr²ᵉ Bᵉ (left-whisker-concatᵉ reflᵉ αᵉ))
      ( tr²ᵉ Bᵉ αᵉ)
      ( tr²ᵉ Bᵉ (right-whisker-concatᵉ βᵉ reflᵉ))
      ( idᵉ ·lᵉ (tr²ᵉ Bᵉ βᵉ))
      ( tr²-left-whiskerᵉ reflᵉ αᵉ)
      ( tr²-right-whiskerᵉ βᵉ reflᵉ)) ∙hᵉ
    ( z-concat-htpy³ᵉ
      ( inv-htpyᵉ (tr³-left-unit-law-left-whisker-concat-Ω²ᵉ αᵉ))
      ( inv-htpyᵉ (tr³-right-unit-law-right-whisker-concat-Ω²ᵉ βᵉ)))

  tr²-right-whisker-concat-tr²-left-whisker-concat-Ω²ᵉ :
    (αᵉ βᵉ : reflᵉ {xᵉ = aᵉ} ＝ᵉ reflᵉ) →
    ( ( tr²ᵉ Bᵉ (right-whisker-concatᵉ αᵉ reflᵉ)) ∙hᵉ
      ( tr²ᵉ Bᵉ (left-whisker-concatᵉ reflᵉ βᵉ))) ~ᵉ
    ( ( idᵉ ·lᵉ (tr²ᵉ Bᵉ αᵉ)) ∙hᵉ (tr²ᵉ Bᵉ βᵉ))
  tr²-right-whisker-concat-tr²-left-whisker-concat-Ω²ᵉ αᵉ βᵉ =
    horizontal-concat-htpy²ᵉ
      ( ( tr³ᵉ
          ( Bᵉ)
          ( invᵉ (right-unit-law-right-whisker-concatᵉ αᵉ ∙ᵉ right-unitᵉ))) ∙hᵉ
        ( inv-htpyᵉ (left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ αᵉ))))
      ( tr³ᵉ Bᵉ (left-unit-law-left-whisker-concatᵉ βᵉ))

  compute-tr²-right-whisker-concat-tr²-left-whisker-concat-Ω²ᵉ :
    (αᵉ βᵉ : reflᵉ {xᵉ = aᵉ} ＝ᵉ reflᵉ) →
    ( inv-coherence-square-homotopies-horizontal-reflᵉ
      ( ( tr²ᵉ Bᵉ (right-whisker-concatᵉ αᵉ reflᵉ)) ∙hᵉ
      ( tr²ᵉ Bᵉ (left-whisker-concatᵉ reflᵉ βᵉ)))
      ( idᵉ ·lᵉ (tr²ᵉ Bᵉ αᵉ) ∙hᵉ tr²ᵉ Bᵉ βᵉ)
      ( tr²-right-whisker-concat-tr²-left-whisker-concatᵉ αᵉ βᵉ)) ~ᵉ
    ( tr²-right-whisker-concat-tr²-left-whisker-concat-Ω²ᵉ αᵉ βᵉ)
  compute-tr²-right-whisker-concat-tr²-left-whisker-concat-Ω²ᵉ αᵉ βᵉ =
    ( vertical-pasting-inv-coherence-square-homotopies-horizontal-reflᵉ
      ( tr²ᵉ Bᵉ (right-whisker-concatᵉ αᵉ reflᵉ))
      ( idᵉ ·lᵉ (tr²ᵉ Bᵉ αᵉ))
      ( tr²ᵉ Bᵉ (left-whisker-concatᵉ reflᵉ βᵉ))
      ( tr²ᵉ Bᵉ βᵉ)
      ( tr²-right-whiskerᵉ αᵉ reflᵉ)
      ( tr²-left-whiskerᵉ reflᵉ βᵉ)) ∙hᵉ
    ( z-concat-htpy³ᵉ
      ( inv-htpyᵉ (tr³-right-unit-law-right-whisker-concat-Ω²ᵉ αᵉ))
      ( inv-htpyᵉ (tr³-left-unit-law-left-whisker-concat-Ω²ᵉ βᵉ)))

  tr²-concat-left-whisker-concat-right-whisker-concat-Ω²ᵉ :
    (αᵉ βᵉ : reflᵉ {xᵉ = aᵉ} ＝ᵉ reflᵉ) →
    ( tr²ᵉ
      ( Bᵉ)
      ( ( left-whisker-concatᵉ reflᵉ αᵉ) ∙ᵉ
        ( right-whisker-concatᵉ βᵉ reflᵉ))) ~ᵉ
    ( ( ( tr²ᵉ Bᵉ αᵉ) ·rᵉ (trᵉ Bᵉ reflᵉ)) ∙hᵉ ((trᵉ Bᵉ reflᵉ) ·lᵉ (tr²ᵉ Bᵉ βᵉ)))
  tr²-concat-left-whisker-concat-right-whisker-concat-Ω²ᵉ αᵉ βᵉ =
    ( tr²-concatᵉ
      ( left-whisker-concatᵉ reflᵉ αᵉ)
      ( right-whisker-concatᵉ βᵉ reflᵉ)) ∙hᵉ
    ( tr²-left-whisker-concat-tr²-right-whisker-concat-Ω²ᵉ αᵉ βᵉ)

  compute-tr²-concat-left-whisker-concat-right-whisker-concat-Ω²ᵉ :
    (αᵉ βᵉ : reflᵉ {xᵉ = aᵉ} ＝ᵉ reflᵉ) →
    ( ( inv-htpyᵉ right-unit-htpyᵉ) ∙hᵉ
      ( tr²-concat-left-whisker-concat-right-whisker-concatᵉ αᵉ βᵉ)) ~ᵉ
    ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω²ᵉ αᵉ βᵉ)
  compute-tr²-concat-left-whisker-concat-right-whisker-concat-Ω²ᵉ αᵉ βᵉ =
    ( inv-htpyᵉ
      ( assoc-htpyᵉ
        ( inv-htpyᵉ right-unit-htpyᵉ)
        ( right-whisker-concat-htpyᵉ
          ( tr²-concatᵉ
            ( left-whisker-concatᵉ reflᵉ αᵉ)
            ( right-whisker-concatᵉ βᵉ reflᵉ))
          ( refl-htpyᵉ))
        ( tr²-left-whisker-concat-tr²-right-whisker-concatᵉ αᵉ βᵉ))) ∙hᵉ
    ( right-whisker-concat-htpyᵉ
      ( vertical-inv-coherence-square-homotopiesᵉ
        ( right-whisker-concat-htpyᵉ
          ( tr²-concatᵉ
            ( left-whisker-concatᵉ reflᵉ αᵉ)
            ( right-whisker-concatᵉ βᵉ reflᵉ))
          ( refl-htpyᵉ))
        ( right-unit-htpyᵉ)
        ( right-unit-htpyᵉ)
        ( tr²-concatᵉ
          ( left-whisker-concatᵉ reflᵉ αᵉ)
          ( right-whisker-concatᵉ βᵉ reflᵉ))
        ( right-unit-law-right-whisker-concat-htpyᵉ
          ( tr²-concatᵉ
            ( left-whisker-concatᵉ reflᵉ αᵉ)
            ( right-whisker-concatᵉ βᵉ reflᵉ))))
      ( tr²-left-whisker-concat-tr²-right-whisker-concatᵉ αᵉ βᵉ)) ∙hᵉ
    ( assoc-htpyᵉ
      ( tr²-concatᵉ
        ( left-whisker-concatᵉ reflᵉ αᵉ)
        ( right-whisker-concatᵉ βᵉ reflᵉ))
      ( inv-htpyᵉ right-unit-htpyᵉ)
      ( tr²-left-whisker-concat-tr²-right-whisker-concatᵉ αᵉ βᵉ)) ∙hᵉ
    ( left-whisker-concat-htpyᵉ
      ( tr²-concatᵉ
        ( left-whisker-concatᵉ reflᵉ αᵉ)
        ( right-whisker-concatᵉ βᵉ reflᵉ))
      ( compute-tr²-left-whisker-concat-tr²-right-whisker-concat-Ω²ᵉ αᵉ βᵉ))

  tr²-concat-right-whisker-concat-left-whisker-concat-Ω²ᵉ :
    (αᵉ βᵉ : reflᵉ {xᵉ = aᵉ} ＝ᵉ reflᵉ) →
    ( tr²ᵉ
      ( Bᵉ)
      ( ( right-whisker-concatᵉ αᵉ reflᵉ) ∙ᵉ
        ( left-whisker-concatᵉ reflᵉ βᵉ))) ~ᵉ
    ( ( ( trᵉ Bᵉ reflᵉ) ·lᵉ (tr²ᵉ Bᵉ αᵉ)) ∙hᵉ ((tr²ᵉ Bᵉ βᵉ) ·rᵉ (trᵉ Bᵉ reflᵉ)))
  tr²-concat-right-whisker-concat-left-whisker-concat-Ω²ᵉ αᵉ βᵉ =
    ( tr²-concatᵉ
      ( right-whisker-concatᵉ αᵉ reflᵉ)
      ( left-whisker-concatᵉ reflᵉ βᵉ)) ∙hᵉ
    ( tr²-right-whisker-concat-tr²-left-whisker-concat-Ω²ᵉ αᵉ βᵉ)

  compute-tr²-concat-right-whisker-concat-left-whisker-concat-Ω²ᵉ :
    (αᵉ βᵉ : reflᵉ {xᵉ = aᵉ} ＝ᵉ reflᵉ) →
    ( ( inv-htpyᵉ right-unit-htpyᵉ) ∙hᵉ
      ( tr²-concat-right-whisker-concat-left-whisker-concatᵉ αᵉ βᵉ)) ~ᵉ
    ( tr²-concat-right-whisker-concat-left-whisker-concat-Ω²ᵉ αᵉ βᵉ)
  compute-tr²-concat-right-whisker-concat-left-whisker-concat-Ω²ᵉ αᵉ βᵉ =
    ( inv-htpyᵉ
      ( assoc-htpyᵉ
        ( inv-htpyᵉ right-unit-htpyᵉ)
        ( right-whisker-concat-htpyᵉ
          ( tr²-concatᵉ
            ( right-whisker-concatᵉ αᵉ reflᵉ)
            ( left-whisker-concatᵉ reflᵉ βᵉ))
          ( refl-htpyᵉ))
        ( tr²-right-whisker-concat-tr²-left-whisker-concatᵉ αᵉ βᵉ))) ∙hᵉ
    ( right-whisker-concat-htpyᵉ
      ( vertical-inv-coherence-square-homotopiesᵉ
        ( right-whisker-concat-htpyᵉ
          ( tr²-concatᵉ
            ( right-whisker-concatᵉ αᵉ reflᵉ)
            ( left-whisker-concatᵉ reflᵉ βᵉ))
          ( refl-htpyᵉ))
        ( right-unit-htpyᵉ)
        ( right-unit-htpyᵉ)
        ( tr²-concatᵉ
          ( right-whisker-concatᵉ αᵉ reflᵉ)
          ( left-whisker-concatᵉ reflᵉ βᵉ))
        ( right-unit-law-right-whisker-concat-htpyᵉ
          ( tr²-concatᵉ
            ( right-whisker-concatᵉ αᵉ reflᵉ)
            ( left-whisker-concatᵉ reflᵉ βᵉ))))
      ( tr²-right-whisker-concat-tr²-left-whisker-concatᵉ αᵉ βᵉ)) ∙hᵉ
    ( assoc-htpyᵉ
      ( tr²-concatᵉ
        ( right-whisker-concatᵉ αᵉ reflᵉ)
        ( left-whisker-concatᵉ reflᵉ βᵉ))
      ( inv-htpyᵉ right-unit-htpyᵉ)
      ( tr²-right-whisker-concat-tr²-left-whisker-concatᵉ αᵉ βᵉ)) ∙hᵉ
    ( left-whisker-concat-htpyᵉ
      ( tr²-concatᵉ
        ( right-whisker-concatᵉ αᵉ reflᵉ)
        ( left-whisker-concatᵉ reflᵉ βᵉ))
      ( compute-tr²-right-whisker-concat-tr²-left-whisker-concat-Ω²ᵉ αᵉ βᵉ))
```

##### A simplification of the main coherence when `α` and `β` are 2-loops

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {aᵉ : Aᵉ}
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  tr³-commutative-left-whisker-right-whisker-concat-Ω²ᵉ :
    (αᵉ βᵉ : reflᵉ {xᵉ = aᵉ} ＝ᵉ reflᵉ) →
    coherence-square-homotopiesᵉ
      ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω²ᵉ αᵉ βᵉ)
      ( tr³ᵉ Bᵉ (commutative-left-whisker-right-whisker-concatᵉ αᵉ βᵉ))
      ( commutative-right-whisker-left-whisker-htpyᵉ
        ( tr²ᵉ Bᵉ αᵉ)
        ( tr²ᵉ Bᵉ βᵉ))
      ( tr²-concat-right-whisker-concat-left-whisker-concat-Ω²ᵉ βᵉ αᵉ)
  tr³-commutative-left-whisker-right-whisker-concat-Ω²ᵉ αᵉ βᵉ =
    concat-bottom-homotopy-coherence-square-homotopiesᵉ
      ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω²ᵉ αᵉ βᵉ)
      ( tr³ᵉ Bᵉ (commutative-left-whisker-right-whisker-concatᵉ αᵉ βᵉ))
      ( commutative-right-whisker-left-whisker-htpyᵉ
        ( tr²ᵉ Bᵉ αᵉ)
        ( tr²ᵉ Bᵉ βᵉ))
      ( ( inv-htpyᵉ right-unit-htpyᵉ) ∙hᵉ
        ( tr²-concat-right-whisker-concat-left-whisker-concatᵉ βᵉ αᵉ))
      ( compute-tr²-concat-right-whisker-concat-left-whisker-concat-Ω²ᵉ βᵉ αᵉ)
      ( concat-top-homotopy-coherence-square-homotopiesᵉ
        ( ( inv-htpyᵉ right-unit-htpyᵉ) ∙hᵉ
          ( tr²-concat-left-whisker-concat-right-whisker-concatᵉ αᵉ βᵉ))
        ( tr³ᵉ Bᵉ (commutative-left-whisker-right-whisker-concatᵉ αᵉ βᵉ))
        ( commutative-right-whisker-left-whisker-htpyᵉ
          ( tr²ᵉ Bᵉ αᵉ)
          ( tr²ᵉ Bᵉ βᵉ))
        ( ( inv-htpyᵉ right-unit-htpyᵉ) ∙hᵉ
          ( tr²-concat-right-whisker-concat-left-whisker-concatᵉ βᵉ αᵉ))
        ( compute-tr²-concat-left-whisker-concat-right-whisker-concat-Ω²ᵉ αᵉ βᵉ)
        ( horizontal-pasting-coherence-square-homotopiesᵉ
          ( inv-htpyᵉ right-unit-htpyᵉ)
          ( tr²-concat-left-whisker-concat-right-whisker-concatᵉ αᵉ βᵉ)
          ( tr³ᵉ Bᵉ (commutative-left-whisker-right-whisker-concatᵉ αᵉ βᵉ))
          ( right-whisker-concat-htpyᵉ
            ( tr³ᵉ Bᵉ (commutative-left-whisker-right-whisker-concatᵉ αᵉ βᵉ))
            ( refl-htpyᵉ))
          ( commutative-right-whisker-left-whisker-htpyᵉ
            ( tr²ᵉ Bᵉ αᵉ)
            ( tr²ᵉ Bᵉ βᵉ))
          ( inv-htpyᵉ right-unit-htpyᵉ)
          ( tr²-concat-right-whisker-concat-left-whisker-concatᵉ βᵉ αᵉ)
          ( horizontal-inv-coherence-square-homotopiesᵉ
            ( right-unit-htpyᵉ)
            ( right-whisker-concat-htpyᵉ
              ( tr³ᵉ Bᵉ (commutative-left-whisker-right-whisker-concatᵉ αᵉ βᵉ))
              ( refl-htpyᵉ))
            ( tr³ᵉ Bᵉ (commutative-left-whisker-right-whisker-concatᵉ αᵉ βᵉ))
            ( right-unit-htpyᵉ)
            ( inv-htpyᵉ
              ( right-unit-law-right-whisker-concat-htpyᵉ
                ( tr³ᵉ
                  ( Bᵉ)
                  ( commutative-left-whisker-right-whisker-concatᵉ αᵉ βᵉ)))))
          ( concat-right-homotopy-coherence-square-homotopiesᵉ
            ( tr²-concat-left-whisker-concat-right-whisker-concatᵉ αᵉ βᵉ)
            ( right-whisker-concat-htpyᵉ
              ( tr³ᵉ Bᵉ (commutative-left-whisker-right-whisker-concatᵉ αᵉ βᵉ))
              ( refl-htpyᵉ))
            ( left-whisker-concat-htpyᵉ
              ( refl-htpyᵉ)
              ( commutative-right-whisker-left-whisker-htpyᵉ
                ( tr²ᵉ Bᵉ αᵉ)
                ( tr²ᵉ Bᵉ βᵉ)))
            ( tr²-concat-right-whisker-concat-left-whisker-concatᵉ βᵉ αᵉ)
            ( left-unit-law-left-whisker-compᵉ
              ( commutative-right-whisker-left-whisker-htpyᵉ
                ( tr²ᵉ Bᵉ αᵉ)
                ( tr²ᵉ Bᵉ βᵉ)))
            ( tr³-commutative-left-whisker-right-whisker-concatᵉ αᵉ βᵉ))))
```