# Composition algebra

```agda
module foundation.composition-algebraᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-higher-homotopies-compositionᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ [homotopyᵉ ofᵉ maps](foundation-core.homotopies.mdᵉ) `Hᵉ : fᵉ ~ᵉ g`,ᵉ thereᵉ areᵉ
standardᵉ witnessesᵉ

```text
  htpy-precompᵉ Hᵉ Sᵉ : precompᵉ fᵉ Sᵉ ~ᵉ precompᵉ gᵉ Sᵉ
```

andᵉ

```text
  htpy-postcompᵉ Sᵉ Hᵉ : postcompᵉ Sᵉ fᵉ ~ᵉ postcompᵉ Sᵉ g.ᵉ
```

Thisᵉ fileᵉ recordsᵉ theirᵉ interactionsᵉ with eachotherᵉ andᵉ differentᵉ operationsᵉ onᵉ
homotopies.ᵉ

## Properties

### Precomposition distributes over whiskerings of homotopies

Theᵉ operationᵉ `htpy-precomp`ᵉ distributesᵉ overᵉ
[whiskeringsᵉ ofᵉ homotopies](foundation.whiskering-homotopies-composition.mdᵉ)
contravariantly.ᵉ Givenᵉ aᵉ homotopyᵉ `Hᵉ : fᵉ ~ᵉ g`ᵉ andᵉ aᵉ suitableᵉ mapᵉ `h`ᵉ theᵉ
homotopyᵉ constructedᵉ asᵉ theᵉ whiskeringᵉ

```text
               -ᵉ ∘ᵉ fᵉ
          ----------------->ᵉ         -ᵉ ∘ᵉ hᵉ
  (Bᵉ → Sᵉ)  htpy-precompᵉ Hᵉ Sᵉ  (Aᵉ → Sᵉ) ----->ᵉ (Cᵉ → Sᵉ)
          ----------------->ᵉ
               -ᵉ ∘ᵉ gᵉ
```

isᵉ homotopicᵉ to theᵉ homotopyᵉ

```text
                    -ᵉ ∘ᵉ (fᵉ ∘ᵉ hᵉ)
            -------------------------->ᵉ
    (Bᵉ → Sᵉ)   htpy-precompᵉ (Hᵉ ·rᵉ hᵉ) Sᵉ   (Cᵉ → S).ᵉ
            -------------------------->ᵉ
                    -ᵉ ∘ᵉ (gᵉ ∘ᵉ hᵉ)
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  {fᵉ gᵉ : Aᵉ → Bᵉ}
  where

  inv-distributive-htpy-precomp-right-whiskerᵉ :
    (hᵉ : Cᵉ → Aᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ) (Sᵉ : UUᵉ l4ᵉ) →
    precompᵉ hᵉ Sᵉ ·lᵉ htpy-precompᵉ Hᵉ Sᵉ ~ᵉ htpy-precompᵉ (Hᵉ ·rᵉ hᵉ) Sᵉ
  inv-distributive-htpy-precomp-right-whiskerᵉ hᵉ Hᵉ Sᵉ iᵉ =
    compute-eq-htpy-ap-precompᵉ hᵉ (iᵉ ·lᵉ Hᵉ)

  distributive-htpy-precomp-right-whiskerᵉ :
    (hᵉ : Cᵉ → Aᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ) (Sᵉ : UUᵉ l4ᵉ) →
    htpy-precompᵉ (Hᵉ ·rᵉ hᵉ) Sᵉ ~ᵉ precompᵉ hᵉ Sᵉ ·lᵉ htpy-precompᵉ Hᵉ Sᵉ
  distributive-htpy-precomp-right-whiskerᵉ hᵉ Hᵉ Sᵉ =
    inv-htpyᵉ (inv-distributive-htpy-precomp-right-whiskerᵉ hᵉ Hᵉ Sᵉ)
```

Similarly,ᵉ theᵉ homotopyᵉ givenᵉ byᵉ theᵉ whiskeringᵉ

```text
                               -ᵉ ∘ᵉ fᵉ
          -ᵉ ∘ᵉ hᵉ          ----------------->ᵉ
  (Cᵉ → Sᵉ) ----->ᵉ (Bᵉ → Sᵉ)  htpy-precompᵉ Hᵉ Sᵉ  (Aᵉ → Sᵉ)
                         ----------------->ᵉ
                               -ᵉ ∘ᵉ gᵉ
```

isᵉ homotopicᵉ to theᵉ homotopyᵉ

```text
                    -ᵉ ∘ᵉ (hᵉ ∘ᵉ fᵉ)
            -------------------------->ᵉ
    (Cᵉ → Sᵉ)   htpy-precompᵉ (hᵉ ·ᵉ lᵉ Hᵉ) Sᵉ   (Aᵉ → S).ᵉ
            -------------------------->ᵉ
                    -ᵉ ∘ᵉ (hᵉ ∘ᵉ gᵉ)
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  {fᵉ gᵉ : Aᵉ → Bᵉ}
  where

  inv-distributive-htpy-precomp-left-whiskerᵉ :
    (hᵉ : Bᵉ → Cᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ) (Sᵉ : UUᵉ l4ᵉ) →
    htpy-precompᵉ Hᵉ Sᵉ ·rᵉ precompᵉ hᵉ Sᵉ ~ᵉ htpy-precompᵉ (hᵉ ·lᵉ Hᵉ) Sᵉ
  inv-distributive-htpy-precomp-left-whiskerᵉ hᵉ Hᵉ Sᵉ iᵉ =
    apᵉ eq-htpyᵉ (eq-htpyᵉ (ap-compᵉ iᵉ hᵉ ∘ᵉ Hᵉ))

  distributive-htpy-precomp-left-whiskerᵉ :
    (hᵉ : Bᵉ → Cᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ) (Sᵉ : UUᵉ l4ᵉ) →
    htpy-precompᵉ (hᵉ ·lᵉ Hᵉ) Sᵉ ~ᵉ htpy-precompᵉ Hᵉ Sᵉ ·rᵉ precompᵉ hᵉ Sᵉ
  distributive-htpy-precomp-left-whiskerᵉ hᵉ Hᵉ Sᵉ =
    inv-htpyᵉ (inv-distributive-htpy-precomp-left-whiskerᵉ hᵉ Hᵉ Sᵉ)
```

### Precomposition distributes over concatenations of homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  {fᵉ gᵉ hᵉ : Aᵉ → Bᵉ}
  where

  distributive-htpy-precomp-concat-htpyᵉ :
    (Hᵉ : fᵉ ~ᵉ gᵉ) (Kᵉ : gᵉ ~ᵉ hᵉ) (Sᵉ : UUᵉ l3ᵉ) →
    htpy-precompᵉ (Hᵉ ∙hᵉ Kᵉ) Sᵉ ~ᵉ htpy-precompᵉ Hᵉ Sᵉ ∙hᵉ htpy-precompᵉ Kᵉ Sᵉ
  distributive-htpy-precomp-concat-htpyᵉ Hᵉ Kᵉ Sᵉ iᵉ =
    ( apᵉ eq-htpyᵉ (eq-htpyᵉ (distributive-left-whisker-comp-concatᵉ iᵉ Hᵉ Kᵉ))) ∙ᵉ
    ( eq-htpy-concat-htpyᵉ (iᵉ ·lᵉ Hᵉ) (iᵉ ·lᵉ Kᵉ))
```

### Postcomposition distributes over whiskerings of homotopies

Givenᵉ aᵉ homotopyᵉ `Hᵉ : fᵉ ~ᵉ g`ᵉ andᵉ aᵉ suitableᵉ mapᵉ `h`ᵉ theᵉ homotopyᵉ givenᵉ byᵉ theᵉ
whiskeringᵉ

```text
                               fᵉ ∘ᵉ –ᵉ
          hᵉ ∘ᵉ -ᵉ          ------------------>ᵉ
  (Sᵉ → Cᵉ) ----->ᵉ (Sᵉ → Bᵉ)  htpy-postcompᵉ Sᵉ Hᵉ  (Sᵉ → Aᵉ)
                         ------------------>ᵉ
                               gᵉ ∘ᵉ -ᵉ
```

isᵉ homotopicᵉ to theᵉ homotopyᵉ

```text
                    (fᵉ ∘ᵉ hᵉ) ∘ᵉ -ᵉ
            -------------------------->ᵉ
    (Sᵉ → Cᵉ)   htpy-postcompᵉ Sᵉ (Hᵉ ·rᵉ hᵉ)   (Sᵉ → A).ᵉ
            -------------------------->ᵉ
                    (gᵉ ∘ᵉ hᵉ) ∘ᵉ -ᵉ
```

Inᵉ fact,ᵉ theyᵉ areᵉ syntacticallyᵉ equal.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  {fᵉ gᵉ : Aᵉ → Bᵉ}
  where

  inv-distributive-htpy-postcomp-right-whiskerᵉ :
    (hᵉ : Cᵉ → Aᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ) (Sᵉ : UUᵉ l4ᵉ) →
    htpy-postcompᵉ Sᵉ (Hᵉ ·rᵉ hᵉ) ~ᵉ htpy-postcompᵉ Sᵉ Hᵉ ·rᵉ postcompᵉ Sᵉ hᵉ
  inv-distributive-htpy-postcomp-right-whiskerᵉ hᵉ Hᵉ Sᵉ = refl-htpyᵉ

  distributive-htpy-postcomp-right-whiskerᵉ :
    (hᵉ : Cᵉ → Aᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ) (Sᵉ : UUᵉ l4ᵉ) →
    htpy-postcompᵉ Sᵉ Hᵉ ·rᵉ postcompᵉ Sᵉ hᵉ ~ᵉ htpy-postcompᵉ Sᵉ (Hᵉ ·rᵉ hᵉ)
  distributive-htpy-postcomp-right-whiskerᵉ hᵉ Hᵉ Sᵉ = refl-htpyᵉ
```

Similarly,ᵉ theᵉ homotopyᵉ givenᵉ byᵉ theᵉ whiskeringᵉ

```text
                fᵉ ∘ᵉ -ᵉ
          ----------------->ᵉ          hᵉ ∘ᵉ -ᵉ
  (Sᵉ → Aᵉ)  htpy-postcompᵉ Sᵉ Hᵉ  (Sᵉ → Bᵉ) ----->ᵉ (Sᵉ → Cᵉ)
          ----------------->ᵉ
                gᵉ ∘ᵉ -ᵉ
```

isᵉ homotopicᵉ to theᵉ homotopyᵉ

```text
                    (hᵉ ∘ᵉ fᵉ) ∘ᵉ -ᵉ
            -------------------------->ᵉ
    (Sᵉ → Aᵉ)   htpy-postcompᵉ Sᵉ (hᵉ ·lᵉ Hᵉ)   (Sᵉ → C).ᵉ
            -------------------------->ᵉ
                    (hᵉ ∘ᵉ gᵉ) ∘ᵉ -ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  {fᵉ gᵉ : Aᵉ → Bᵉ}
  where

  inv-distributive-htpy-postcomp-left-whiskerᵉ :
    (hᵉ : Bᵉ → Cᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ) (Sᵉ : UUᵉ l4ᵉ) →
    postcompᵉ Sᵉ hᵉ ·lᵉ htpy-postcompᵉ Sᵉ Hᵉ ~ᵉ htpy-postcompᵉ Sᵉ (hᵉ ·lᵉ Hᵉ)
  inv-distributive-htpy-postcomp-left-whiskerᵉ hᵉ Hᵉ Sᵉ iᵉ =
    compute-eq-htpy-ap-postcompᵉ hᵉ (Hᵉ ·rᵉ iᵉ)

  distributive-htpy-postcomp-left-whiskerᵉ :
    (hᵉ : Bᵉ → Cᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ) (Sᵉ : UUᵉ l4ᵉ) →
    htpy-postcompᵉ Sᵉ (hᵉ ·lᵉ Hᵉ) ~ᵉ postcompᵉ Sᵉ hᵉ ·lᵉ htpy-postcompᵉ Sᵉ Hᵉ
  distributive-htpy-postcomp-left-whiskerᵉ hᵉ Hᵉ Sᵉ =
    inv-htpyᵉ (inv-distributive-htpy-postcomp-left-whiskerᵉ hᵉ Hᵉ Sᵉ)
```

### Postcomposition distributes over concatenations of homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  {fᵉ gᵉ hᵉ : Aᵉ → Bᵉ}
  where

  distributive-htpy-postcomp-concat-htpyᵉ :
    (Hᵉ : fᵉ ~ᵉ gᵉ) (Kᵉ : gᵉ ~ᵉ hᵉ) (Sᵉ : UUᵉ l3ᵉ) →
    htpy-postcompᵉ Sᵉ (Hᵉ ∙hᵉ Kᵉ) ~ᵉ htpy-postcompᵉ Sᵉ Hᵉ ∙hᵉ htpy-postcompᵉ Sᵉ Kᵉ
  distributive-htpy-postcomp-concat-htpyᵉ Hᵉ Kᵉ Sᵉ iᵉ =
    ( apᵉ eq-htpyᵉ (eq-htpyᵉ (distributive-right-whisker-comp-concatᵉ iᵉ Hᵉ Kᵉ))) ∙ᵉ
    ( eq-htpy-concat-htpyᵉ (Hᵉ ·rᵉ iᵉ) (Kᵉ ·rᵉ iᵉ))
```

### The actions of precomposition and postcomposition on homotopies commute

Givenᵉ homotopiesᵉ `Fᵉ : fᵉ ~ᵉ f'`ᵉ andᵉ `Gᵉ : gᵉ ~ᵉ g'`,ᵉ weᵉ haveᵉ aᵉ commutingᵉ squareᵉ ofᵉ
homotopiesᵉ

```text
                        postcompᵉ Aᵉ gᵉ ·lᵉ htpy-precompᵉ Fᵉ Xᵉ
           (gᵉ ∘ᵉ -ᵉ ∘ᵉ fᵉ) --------------------------------->ᵉ (gᵉ ∘ᵉ -ᵉ ∘ᵉ f'ᵉ)
                |                                              |
                |                                              |
                |                                              |
  precompᵉ fᵉ Yᵉ ·lᵉ htpy-postcompᵉ Bᵉ Gᵉ            htpy-postcompᵉ Aᵉ Gᵉ ·rᵉ precompᵉ f'ᵉ Xᵉ
                |                                              |
                |                                              |
                ∨ᵉ                                              ∨ᵉ
          (g'ᵉ ∘ᵉ -ᵉ ∘ᵉ fᵉ) -------------------------------->ᵉ (g'ᵉ ∘ᵉ -ᵉ ∘ᵉ f').ᵉ
                       htpy-precompᵉ Fᵉ Yᵉ ·rᵉ postcompᵉ Bᵉ g'ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  where

  commutative-postcomp-htpy-precompᵉ :
    {fᵉ f'ᵉ : Aᵉ → Bᵉ} (gᵉ : Xᵉ → Yᵉ) (Fᵉ : fᵉ ~ᵉ f'ᵉ) →
    htpy-precompᵉ Fᵉ Yᵉ ·rᵉ postcompᵉ Bᵉ gᵉ ~ᵉ postcompᵉ Aᵉ gᵉ ·lᵉ htpy-precompᵉ Fᵉ Xᵉ
  commutative-postcomp-htpy-precompᵉ {fᵉ} gᵉ =
    ind-htpyᵉ fᵉ
      ( λ f'ᵉ Fᵉ →
        htpy-precompᵉ Fᵉ Yᵉ ·rᵉ postcompᵉ Bᵉ gᵉ ~ᵉ postcompᵉ Aᵉ gᵉ ·lᵉ htpy-precompᵉ Fᵉ Xᵉ)
      ( ( right-whisker-comp²ᵉ
          ( compute-htpy-precomp-refl-htpyᵉ fᵉ Yᵉ)
          ( postcompᵉ Bᵉ gᵉ)) ∙hᵉ
        ( inv-htpyᵉ
          ( left-whisker-comp²ᵉ
            ( postcompᵉ Aᵉ gᵉ)
            ( compute-htpy-precomp-refl-htpyᵉ fᵉ Xᵉ))))

  commutative-precomp-htpy-postcompᵉ :
    (fᵉ : Aᵉ → Bᵉ) {gᵉ g'ᵉ : Xᵉ → Yᵉ} (Gᵉ : gᵉ ~ᵉ g'ᵉ) →
    htpy-postcompᵉ Aᵉ Gᵉ ·rᵉ precompᵉ fᵉ Xᵉ ~ᵉ precompᵉ fᵉ Yᵉ ·lᵉ htpy-postcompᵉ Bᵉ Gᵉ
  commutative-precomp-htpy-postcompᵉ fᵉ {gᵉ} =
    ind-htpyᵉ gᵉ
      ( λ g'ᵉ Gᵉ →
        htpy-postcompᵉ Aᵉ Gᵉ ·rᵉ precompᵉ fᵉ Xᵉ ~ᵉ precompᵉ fᵉ Yᵉ ·lᵉ htpy-postcompᵉ Bᵉ Gᵉ)
      ( ( right-whisker-comp²ᵉ
          ( compute-htpy-postcomp-refl-htpyᵉ Aᵉ gᵉ)
          ( precompᵉ fᵉ Xᵉ)) ∙hᵉ
        ( inv-htpyᵉ
          ( left-whisker-comp²ᵉ
            ( precompᵉ fᵉ Yᵉ)
            ( compute-htpy-postcomp-refl-htpyᵉ Bᵉ gᵉ))))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  {fᵉ f'ᵉ : Aᵉ → Bᵉ} {gᵉ g'ᵉ : Xᵉ → Yᵉ}
  where

  commutative-htpy-postcomp-htpy-precompᵉ :
    (Fᵉ : fᵉ ~ᵉ f'ᵉ) (Gᵉ : gᵉ ~ᵉ g'ᵉ) →
    ( postcompᵉ Aᵉ gᵉ ·lᵉ htpy-precompᵉ Fᵉ Xᵉ ∙hᵉ htpy-postcompᵉ Aᵉ Gᵉ ·rᵉ precompᵉ f'ᵉ Xᵉ) ~ᵉ
    ( precompᵉ fᵉ Yᵉ ·lᵉ htpy-postcompᵉ Bᵉ Gᵉ ∙hᵉ htpy-precompᵉ Fᵉ Yᵉ ·rᵉ postcompᵉ Bᵉ g'ᵉ)
  commutative-htpy-postcomp-htpy-precompᵉ Fᵉ =
    ind-htpyᵉ gᵉ
      ( λ g'ᵉ Gᵉ →
        ( postcompᵉ Aᵉ gᵉ ·lᵉ htpy-precompᵉ Fᵉ Xᵉ ∙hᵉ
          htpy-postcompᵉ Aᵉ Gᵉ ·rᵉ precompᵉ f'ᵉ Xᵉ) ~ᵉ
        ( precompᵉ fᵉ Yᵉ ·lᵉ htpy-postcompᵉ Bᵉ Gᵉ ∙hᵉ
          htpy-precompᵉ Fᵉ Yᵉ ·rᵉ postcompᵉ Bᵉ g'ᵉ))
      ( ( ap-concat-htpyᵉ
          ( postcompᵉ Aᵉ gᵉ ·lᵉ htpy-precompᵉ Fᵉ Xᵉ)
          ( right-whisker-comp²ᵉ
            ( compute-htpy-postcomp-refl-htpyᵉ Aᵉ gᵉ)
            ( precompᵉ f'ᵉ Xᵉ))) ∙hᵉ
        ( right-unit-htpyᵉ) ∙hᵉ
        ( inv-htpyᵉ (commutative-postcomp-htpy-precompᵉ gᵉ Fᵉ)) ∙hᵉ
        ( ap-concat-htpy'ᵉ
          ( htpy-precompᵉ Fᵉ Yᵉ ·rᵉ postcompᵉ Bᵉ gᵉ)
          ( left-whisker-comp²ᵉ
            ( precompᵉ fᵉ Yᵉ)
            ( inv-htpyᵉ (compute-htpy-postcomp-refl-htpyᵉ Bᵉ gᵉ)))))
```