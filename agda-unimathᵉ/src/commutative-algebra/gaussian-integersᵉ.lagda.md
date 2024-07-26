# The Gaussian integers

```agda
module commutative-algebra.gaussian-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ

open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.difference-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.semigroupsᵉ

open import ring-theory.ringsᵉ
```

</details>

## Idea

Theᵉ **Gaussianᵉ integers**ᵉ areᵉ theᵉ complexᵉ numbersᵉ ofᵉ theᵉ formᵉ `aᵉ +ᵉ bi`,ᵉ where
`a`ᵉ andᵉ `b`ᵉ areᵉ integers.ᵉ

## Definition

### The underlying type of the Gaussian integers

```agda
ℤ[iᵉ] : UUᵉ lzero
ℤ[iᵉ] = ℤᵉ ×ᵉ ℤᵉ
```

### Observational equality of the Gaussian integers

```agda
Eq-ℤ[iᵉ] : ℤ[iᵉ] → ℤ[iᵉ] → UUᵉ lzero
Eq-ℤ[iᵉ] xᵉ yᵉ = (pr1ᵉ xᵉ ＝ᵉ pr1ᵉ yᵉ) ×ᵉ (pr2ᵉ xᵉ ＝ᵉ pr2ᵉ yᵉ)

refl-Eq-ℤ[iᵉ] : (xᵉ : ℤ[iᵉ]) → Eq-ℤ[iᵉ] xᵉ xᵉ
pr1ᵉ (refl-Eq-ℤ[iᵉ] xᵉ) = reflᵉ
pr2ᵉ (refl-Eq-ℤ[iᵉ] xᵉ) = reflᵉ

Eq-eq-ℤ[iᵉ] : {xᵉ yᵉ : ℤ[iᵉ]} → xᵉ ＝ᵉ yᵉ → Eq-ℤ[iᵉ] xᵉ yᵉ
Eq-eq-ℤ[iᵉ] {xᵉ} reflᵉ = refl-Eq-ℤ[iᵉ] xᵉ

eq-Eq-ℤ[i]'ᵉ : {xᵉ yᵉ : ℤ[iᵉ]} → Eq-ℤ[iᵉ] xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
eq-Eq-ℤ[i]'ᵉ {aᵉ ,ᵉ bᵉ} {.aᵉ ,ᵉ .bᵉ} (reflᵉ ,ᵉ reflᵉ) = reflᵉ

eq-Eq-ℤ[iᵉ] : {xᵉ yᵉ : ℤ[iᵉ]} → pr1ᵉ xᵉ ＝ᵉ pr1ᵉ yᵉ → pr2ᵉ xᵉ ＝ᵉ pr2ᵉ yᵉ → xᵉ ＝ᵉ yᵉ
eq-Eq-ℤ[iᵉ] {aᵉ ,ᵉ bᵉ} {.aᵉ ,ᵉ .bᵉ} reflᵉ reflᵉ = reflᵉ
```

### The Gaussian integer zero

```agda
zero-ℤ[iᵉ] : ℤ[iᵉ]
pr1ᵉ zero-ℤ[iᵉ] = zero-ℤᵉ
pr2ᵉ zero-ℤ[iᵉ] = zero-ℤᵉ
```

### The Gaussian integer one

```agda
one-ℤ[iᵉ] : ℤ[iᵉ]
pr1ᵉ one-ℤ[iᵉ] = one-ℤᵉ
pr2ᵉ one-ℤ[iᵉ] = zero-ℤᵉ
```

### The inclusion of the integers into the Gaussian integers

```agda
gaussian-int-ℤᵉ : ℤᵉ → ℤ[iᵉ]
pr1ᵉ (gaussian-int-ℤᵉ xᵉ) = xᵉ
pr2ᵉ (gaussian-int-ℤᵉ xᵉ) = zero-ℤᵉ
```

### The Gaussian integer `i`

```agda
i-ℤ[iᵉ] : ℤ[iᵉ]
pr1ᵉ i-ℤ[iᵉ] = zero-ℤᵉ
pr2ᵉ i-ℤ[iᵉ] = one-ℤᵉ
```

### The Gaussian integer `-i`

```agda
neg-i-ℤ[iᵉ] : ℤ[iᵉ]
pr1ᵉ neg-i-ℤ[iᵉ] = zero-ℤᵉ
pr2ᵉ neg-i-ℤ[iᵉ] = neg-one-ℤᵉ
```

### Addition of Gaussian integers

```agda
add-ℤ[iᵉ] : ℤ[iᵉ] → ℤ[iᵉ] → ℤ[iᵉ]
pr1ᵉ (add-ℤ[iᵉ] (aᵉ ,ᵉ bᵉ) (a'ᵉ ,ᵉ b'ᵉ)) = aᵉ +ℤᵉ a'ᵉ
pr2ᵉ (add-ℤ[iᵉ] (aᵉ ,ᵉ bᵉ) (a'ᵉ ,ᵉ b'ᵉ)) = bᵉ +ℤᵉ b'ᵉ

infixl 35 _+ℤ[iᵉ]_
_+ℤ[iᵉ]_ = add-ℤ[iᵉ]

ap-add-ℤ[iᵉ] :
  {xᵉ x'ᵉ yᵉ y'ᵉ : ℤ[iᵉ]} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → xᵉ +ℤ[iᵉ] yᵉ ＝ᵉ x'ᵉ +ℤ[iᵉ] y'ᵉ
ap-add-ℤ[iᵉ] pᵉ qᵉ = ap-binaryᵉ add-ℤ[iᵉ] pᵉ qᵉ
```

### Negatives of Gaussian integers

```agda
neg-ℤ[iᵉ] : ℤ[iᵉ] → ℤ[iᵉ]
pr1ᵉ (neg-ℤ[iᵉ] (aᵉ ,ᵉ bᵉ)) = neg-ℤᵉ aᵉ
pr2ᵉ (neg-ℤ[iᵉ] (aᵉ ,ᵉ bᵉ)) = neg-ℤᵉ bᵉ
```

### Multiplication of Gaussian integers

```agda
mul-ℤ[iᵉ] : ℤ[iᵉ] → ℤ[iᵉ] → ℤ[iᵉ]
pr1ᵉ (mul-ℤ[iᵉ] (aᵉ ,ᵉ bᵉ) (a'ᵉ ,ᵉ b'ᵉ)) = (aᵉ *ℤᵉ a'ᵉ) -ℤᵉ (bᵉ *ℤᵉ b'ᵉ)
pr2ᵉ (mul-ℤ[iᵉ] (aᵉ ,ᵉ bᵉ) (a'ᵉ ,ᵉ b'ᵉ)) = (aᵉ *ℤᵉ b'ᵉ) +ℤᵉ (a'ᵉ *ℤᵉ bᵉ)

infixl 40 _*ℤ[iᵉ]_
_*ℤ[iᵉ]_ = mul-ℤ[iᵉ]

ap-mul-ℤ[iᵉ] :
  {xᵉ x'ᵉ yᵉ y'ᵉ : ℤ[iᵉ]} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → xᵉ *ℤ[iᵉ] yᵉ ＝ᵉ x'ᵉ *ℤ[iᵉ] y'ᵉ
ap-mul-ℤ[iᵉ] pᵉ qᵉ = ap-binaryᵉ mul-ℤ[iᵉ] pᵉ qᵉ
```

### Conjugation of Gaussian integers

```agda
conjugate-ℤ[iᵉ] : ℤ[iᵉ] → ℤ[iᵉ]
pr1ᵉ (conjugate-ℤ[iᵉ] (aᵉ ,ᵉ bᵉ)) = aᵉ
pr2ᵉ (conjugate-ℤ[iᵉ] (aᵉ ,ᵉ bᵉ)) = neg-ℤᵉ bᵉ
```

### The Gaussian integers form a commutative ring

```agda
left-unit-law-add-ℤ[iᵉ] : (xᵉ : ℤ[iᵉ]) → zero-ℤ[iᵉ] +ℤ[iᵉ] xᵉ ＝ᵉ xᵉ
left-unit-law-add-ℤ[iᵉ] (aᵉ ,ᵉ bᵉ) = eq-Eq-ℤ[iᵉ] reflᵉ reflᵉ

right-unit-law-add-ℤ[iᵉ] : (xᵉ : ℤ[iᵉ]) → xᵉ +ℤ[iᵉ] zero-ℤ[iᵉ] ＝ᵉ xᵉ
right-unit-law-add-ℤ[iᵉ] (aᵉ ,ᵉ bᵉ) =
  eq-Eq-ℤ[iᵉ] (right-unit-law-add-ℤᵉ aᵉ) (right-unit-law-add-ℤᵉ bᵉ)

associative-add-ℤ[iᵉ] :
  (xᵉ yᵉ zᵉ : ℤ[iᵉ]) → (xᵉ +ℤ[iᵉ] yᵉ) +ℤ[iᵉ] zᵉ ＝ᵉ xᵉ +ℤ[iᵉ] (yᵉ +ℤ[iᵉ] zᵉ)
associative-add-ℤ[iᵉ] (a1ᵉ ,ᵉ b1ᵉ) (a2ᵉ ,ᵉ b2ᵉ) (a3ᵉ ,ᵉ b3ᵉ) =
  eq-Eq-ℤ[iᵉ] (associative-add-ℤᵉ a1ᵉ a2ᵉ a3ᵉ) (associative-add-ℤᵉ b1ᵉ b2ᵉ b3ᵉ)

left-inverse-law-add-ℤ[iᵉ] :
  (xᵉ : ℤ[iᵉ]) → (neg-ℤ[iᵉ] xᵉ) +ℤ[iᵉ] xᵉ ＝ᵉ zero-ℤ[iᵉ]
left-inverse-law-add-ℤ[iᵉ] (aᵉ ,ᵉ bᵉ) =
  eq-Eq-ℤ[iᵉ] (left-inverse-law-add-ℤᵉ aᵉ) (left-inverse-law-add-ℤᵉ bᵉ)

right-inverse-law-add-ℤ[iᵉ] :
  (xᵉ : ℤ[iᵉ]) → xᵉ +ℤ[iᵉ] (neg-ℤ[iᵉ] xᵉ) ＝ᵉ zero-ℤ[iᵉ]
right-inverse-law-add-ℤ[iᵉ] (aᵉ ,ᵉ bᵉ) =
  eq-Eq-ℤ[iᵉ] (right-inverse-law-add-ℤᵉ aᵉ) (right-inverse-law-add-ℤᵉ bᵉ)

commutative-add-ℤ[iᵉ] :
  (xᵉ yᵉ : ℤ[iᵉ]) → xᵉ +ℤ[iᵉ] yᵉ ＝ᵉ yᵉ +ℤ[iᵉ] xᵉ
commutative-add-ℤ[iᵉ] (aᵉ ,ᵉ bᵉ) (a'ᵉ ,ᵉ b'ᵉ) =
  eq-Eq-ℤ[iᵉ] (commutative-add-ℤᵉ aᵉ a'ᵉ) (commutative-add-ℤᵉ bᵉ b'ᵉ)

left-unit-law-mul-ℤ[iᵉ] : (xᵉ : ℤ[iᵉ]) → one-ℤ[iᵉ] *ℤ[iᵉ] xᵉ ＝ᵉ xᵉ
left-unit-law-mul-ℤ[iᵉ] (aᵉ ,ᵉ bᵉ) =
  eq-Eq-ℤ[iᵉ]
    ( right-unit-law-add-ℤᵉ aᵉ)
    ( apᵉ (bᵉ +ℤᵉ_) (right-zero-law-mul-ℤᵉ aᵉ) ∙ᵉ right-unit-law-add-ℤᵉ bᵉ)

right-unit-law-mul-ℤ[iᵉ] : (xᵉ : ℤ[iᵉ]) → xᵉ *ℤ[iᵉ] one-ℤ[iᵉ] ＝ᵉ xᵉ
right-unit-law-mul-ℤ[iᵉ] (aᵉ ,ᵉ bᵉ) =
  eq-Eq-ℤ[iᵉ]
    ( ( ap-add-ℤᵉ
        ( right-unit-law-mul-ℤᵉ aᵉ)
        ( apᵉ neg-ℤᵉ (right-zero-law-mul-ℤᵉ bᵉ))) ∙ᵉ
      ( right-unit-law-add-ℤᵉ aᵉ))
    ( apᵉ (_+ℤᵉ bᵉ) (right-zero-law-mul-ℤᵉ aᵉ))

commutative-mul-ℤ[iᵉ] :
  (xᵉ yᵉ : ℤ[iᵉ]) → xᵉ *ℤ[iᵉ] yᵉ ＝ᵉ yᵉ *ℤ[iᵉ] xᵉ
commutative-mul-ℤ[iᵉ] (aᵉ ,ᵉ bᵉ) (cᵉ ,ᵉ dᵉ) =
  eq-Eq-ℤ[iᵉ]
    ( ap-add-ℤᵉ (commutative-mul-ℤᵉ aᵉ cᵉ) (apᵉ neg-ℤᵉ (commutative-mul-ℤᵉ bᵉ dᵉ)))
    ( commutative-add-ℤᵉ (aᵉ *ℤᵉ dᵉ) (cᵉ *ℤᵉ bᵉ))

associative-mul-ℤ[iᵉ] :
  (xᵉ yᵉ zᵉ : ℤ[iᵉ]) → (xᵉ *ℤ[iᵉ] yᵉ) *ℤ[iᵉ] zᵉ ＝ᵉ xᵉ *ℤ[iᵉ] (yᵉ *ℤ[iᵉ] zᵉ)
associative-mul-ℤ[iᵉ] (aᵉ ,ᵉ bᵉ) (cᵉ ,ᵉ dᵉ) (eᵉ ,ᵉ fᵉ) =
  eq-Eq-ℤ[iᵉ]
    ( ( ap-add-ℤᵉ
        ( ( right-distributive-mul-add-ℤᵉ
            ( aᵉ *ℤᵉ cᵉ)
            ( neg-one-ℤᵉ *ℤᵉ (bᵉ *ℤᵉ dᵉ))
            ( eᵉ)) ∙ᵉ
          ( ap-add-ℤᵉ
            ( associative-mul-ℤᵉ aᵉ cᵉ eᵉ)
            ( ( associative-mul-ℤᵉ neg-one-ℤᵉ (bᵉ *ℤᵉ dᵉ) eᵉ) ∙ᵉ
              ( apᵉ
                ( neg-one-ℤᵉ *ℤᵉ_)
                ( ( associative-mul-ℤᵉ bᵉ dᵉ eᵉ) ∙ᵉ
                  ( apᵉ (bᵉ *ℤᵉ_) (commutative-mul-ℤᵉ dᵉ eᵉ)))))))
        ( ( apᵉ
            ( neg-ℤᵉ)
            ( ( right-distributive-mul-add-ℤᵉ (aᵉ *ℤᵉ dᵉ) (cᵉ *ℤᵉ bᵉ) fᵉ) ∙ᵉ
              ( ap-add-ℤᵉ
                ( associative-mul-ℤᵉ aᵉ dᵉ fᵉ)
                ( associative-mul-ℤᵉ cᵉ bᵉ fᵉ)))) ∙ᵉ
          ( ( left-distributive-mul-add-ℤᵉ
              ( neg-one-ℤᵉ)
              ( aᵉ *ℤᵉ (dᵉ *ℤᵉ fᵉ))
              ( cᵉ *ℤᵉ (bᵉ *ℤᵉ fᵉ)))))) ∙ᵉ
      ( ( interchange-law-add-add-ℤᵉ
          ( aᵉ *ℤᵉ (cᵉ *ℤᵉ eᵉ))
          ( neg-ℤᵉ (bᵉ *ℤᵉ (eᵉ *ℤᵉ dᵉ)))
          ( neg-ℤᵉ (aᵉ *ℤᵉ (dᵉ *ℤᵉ fᵉ)))
          ( neg-ℤᵉ (cᵉ *ℤᵉ (bᵉ *ℤᵉ fᵉ)))) ∙ᵉ
        ( ap-add-ℤᵉ
          ( ( ap-add-ℤᵉ
              ( reflᵉ {xᵉ = aᵉ *ℤᵉ (cᵉ *ℤᵉ eᵉ)})
              ( invᵉ
                ( right-negative-law-mul-ℤᵉ aᵉ (dᵉ *ℤᵉ fᵉ)))) ∙ᵉ
            ( invᵉ
              ( left-distributive-mul-add-ℤᵉ aᵉ
                ( cᵉ *ℤᵉ eᵉ)
                ( neg-ℤᵉ (dᵉ *ℤᵉ fᵉ)))))
          ( ( invᵉ
              ( left-distributive-mul-add-ℤᵉ
                ( neg-one-ℤᵉ)
                ( bᵉ *ℤᵉ (eᵉ *ℤᵉ dᵉ))
                ( cᵉ *ℤᵉ (bᵉ *ℤᵉ fᵉ)))) ∙ᵉ
            ( apᵉ neg-ℤᵉ
              ( ( ap-add-ℤᵉ
                  ( reflᵉ {xᵉ = bᵉ *ℤᵉ (eᵉ *ℤᵉ dᵉ)})
                  ( ( apᵉ (cᵉ *ℤᵉ_) (commutative-mul-ℤᵉ bᵉ fᵉ)) ∙ᵉ
                    ( ( invᵉ (associative-mul-ℤᵉ cᵉ fᵉ bᵉ)) ∙ᵉ
                      ( commutative-mul-ℤᵉ (cᵉ *ℤᵉ fᵉ) bᵉ)))) ∙ᵉ
                ( ( invᵉ
                    ( left-distributive-mul-add-ℤᵉ bᵉ
                      ( eᵉ *ℤᵉ dᵉ)
                      ( cᵉ *ℤᵉ fᵉ))) ∙ᵉ
                  ( apᵉ
                    ( bᵉ *ℤᵉ_)
                    ( commutative-add-ℤᵉ (eᵉ *ℤᵉ dᵉ) (cᵉ *ℤᵉ fᵉ))))))))))
    ( ( ap-add-ℤᵉ
        ( ( right-distributive-mul-add-ℤᵉ
            ( aᵉ *ℤᵉ cᵉ)
            ( neg-ℤᵉ (bᵉ *ℤᵉ dᵉ))
            ( fᵉ)) ∙ᵉ
          ( apᵉ
            ( ((aᵉ *ℤᵉ cᵉ) *ℤᵉ fᵉ) +ℤᵉ_)
            ( left-negative-law-mul-ℤᵉ (bᵉ *ℤᵉ dᵉ) fᵉ)))
        ( ( left-distributive-mul-add-ℤᵉ eᵉ (aᵉ *ℤᵉ dᵉ) (cᵉ *ℤᵉ bᵉ)) ∙ᵉ
          ( ap-add-ℤᵉ
            ( ( commutative-mul-ℤᵉ eᵉ (aᵉ *ℤᵉ dᵉ)) ∙ᵉ
              ( ( associative-mul-ℤᵉ aᵉ dᵉ eᵉ) ∙ᵉ
                ( apᵉ (aᵉ *ℤᵉ_) (commutative-mul-ℤᵉ dᵉ eᵉ))))
            ( ( invᵉ (associative-mul-ℤᵉ eᵉ cᵉ bᵉ)) ∙ᵉ
              ( apᵉ (_*ℤᵉ bᵉ) (commutative-mul-ℤᵉ eᵉ cᵉ)))))) ∙ᵉ
      ( ( interchange-law-add-add-ℤᵉ
          ( (aᵉ *ℤᵉ cᵉ) *ℤᵉ fᵉ)
          ( neg-ℤᵉ ((bᵉ *ℤᵉ dᵉ) *ℤᵉ fᵉ))
          ( aᵉ *ℤᵉ (eᵉ *ℤᵉ dᵉ))
          ( (cᵉ *ℤᵉ eᵉ) *ℤᵉ bᵉ)) ∙ᵉ
        ( ap-add-ℤᵉ
          ( ( ap-add-ℤᵉ
              ( associative-mul-ℤᵉ aᵉ cᵉ fᵉ)
              ( reflᵉ)) ∙ᵉ
            ( invᵉ (left-distributive-mul-add-ℤᵉ aᵉ (cᵉ *ℤᵉ fᵉ) (eᵉ *ℤᵉ dᵉ))))
          ( ( ap-add-ℤᵉ
              ( ( apᵉ
                  ( neg-ℤᵉ)
                  ( ( associative-mul-ℤᵉ bᵉ dᵉ fᵉ) ∙ᵉ
                    ( commutative-mul-ℤᵉ bᵉ (dᵉ *ℤᵉ fᵉ)))) ∙ᵉ
                ( invᵉ (left-negative-law-mul-ℤᵉ (dᵉ *ℤᵉ fᵉ) bᵉ)))
              ( reflᵉ)) ∙ᵉ
            ( ( invᵉ
                ( ( right-distributive-mul-add-ℤᵉ
                    ( neg-ℤᵉ (dᵉ *ℤᵉ fᵉ))
                    ( cᵉ *ℤᵉ eᵉ) bᵉ))) ∙ᵉ
              ( apᵉ
                ( _*ℤᵉ bᵉ)
                ( commutative-add-ℤᵉ (neg-ℤᵉ (dᵉ *ℤᵉ fᵉ)) (cᵉ *ℤᵉ eᵉ))))))))

left-distributive-mul-add-ℤ[iᵉ] :
  (xᵉ yᵉ zᵉ : ℤ[iᵉ]) →
  xᵉ *ℤ[iᵉ] (yᵉ +ℤ[iᵉ] zᵉ) ＝ᵉ (xᵉ *ℤ[iᵉ] yᵉ) +ℤ[iᵉ] (xᵉ *ℤ[iᵉ] zᵉ)
left-distributive-mul-add-ℤ[iᵉ] (aᵉ ,ᵉ bᵉ) (cᵉ ,ᵉ dᵉ) (eᵉ ,ᵉ fᵉ) =
  eq-Eq-ℤ[iᵉ]
    ( ( ap-add-ℤᵉ
        ( left-distributive-mul-add-ℤᵉ aᵉ cᵉ eᵉ)
        ( ( apᵉ neg-ℤᵉ (left-distributive-mul-add-ℤᵉ bᵉ dᵉ fᵉ)) ∙ᵉ
          ( left-distributive-mul-add-ℤᵉ neg-one-ℤᵉ (bᵉ *ℤᵉ dᵉ) (bᵉ *ℤᵉ fᵉ)))) ∙ᵉ
      ( interchange-law-add-add-ℤᵉ
        ( aᵉ *ℤᵉ cᵉ)
        ( aᵉ *ℤᵉ eᵉ)
        ( neg-ℤᵉ (bᵉ *ℤᵉ dᵉ))
        ( neg-ℤᵉ (bᵉ *ℤᵉ fᵉ))))
    ( ( ap-add-ℤᵉ
        ( left-distributive-mul-add-ℤᵉ aᵉ dᵉ fᵉ)
        ( right-distributive-mul-add-ℤᵉ cᵉ eᵉ bᵉ)) ∙ᵉ
      ( interchange-law-add-add-ℤᵉ
        ( aᵉ *ℤᵉ dᵉ)
        ( aᵉ *ℤᵉ fᵉ)
        ( cᵉ *ℤᵉ bᵉ)
        ( eᵉ *ℤᵉ bᵉ)))

right-distributive-mul-add-ℤ[iᵉ] :
  (xᵉ yᵉ zᵉ : ℤ[iᵉ]) →
  (xᵉ +ℤ[iᵉ] yᵉ) *ℤ[iᵉ] zᵉ ＝ᵉ (xᵉ *ℤ[iᵉ] zᵉ) +ℤ[iᵉ] (yᵉ *ℤ[iᵉ] zᵉ)
right-distributive-mul-add-ℤ[iᵉ] xᵉ yᵉ zᵉ =
  ( commutative-mul-ℤ[iᵉ] (xᵉ +ℤ[iᵉ] yᵉ) zᵉ) ∙ᵉ
  ( ( left-distributive-mul-add-ℤ[iᵉ] zᵉ xᵉ yᵉ) ∙ᵉ
    ( ap-add-ℤ[iᵉ] (commutative-mul-ℤ[iᵉ] zᵉ xᵉ) (commutative-mul-ℤ[iᵉ] zᵉ yᵉ)))

ℤ[i]-Semigroupᵉ : Semigroupᵉ lzero
pr1ᵉ ℤ[i]-Semigroupᵉ = product-Setᵉ ℤ-Setᵉ ℤ-Setᵉ
pr1ᵉ (pr2ᵉ ℤ[i]-Semigroupᵉ) = add-ℤ[iᵉ]
pr2ᵉ (pr2ᵉ ℤ[i]-Semigroupᵉ) = associative-add-ℤ[iᵉ]

ℤ[i]-Groupᵉ : Groupᵉ lzero
pr1ᵉ ℤ[i]-Groupᵉ = ℤ[i]-Semigroupᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ ℤ[i]-Groupᵉ)) = zero-ℤ[iᵉ]
pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ ℤ[i]-Groupᵉ))) = left-unit-law-add-ℤ[iᵉ]
pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ ℤ[i]-Groupᵉ))) = right-unit-law-add-ℤ[iᵉ]
pr1ᵉ (pr2ᵉ (pr2ᵉ ℤ[i]-Groupᵉ)) = neg-ℤ[iᵉ]
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ℤ[i]-Groupᵉ))) = left-inverse-law-add-ℤ[iᵉ]
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ℤ[i]-Groupᵉ))) = right-inverse-law-add-ℤ[iᵉ]

ℤ[i]-Abᵉ : Abᵉ lzero
pr1ᵉ ℤ[i]-Abᵉ = ℤ[i]-Groupᵉ
pr2ᵉ ℤ[i]-Abᵉ = commutative-add-ℤ[iᵉ]

ℤ[i]-Ringᵉ : Ringᵉ lzero
pr1ᵉ ℤ[i]-Ringᵉ = ℤ[i]-Abᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ ℤ[i]-Ringᵉ)) = mul-ℤ[iᵉ]
pr2ᵉ (pr1ᵉ (pr2ᵉ ℤ[i]-Ringᵉ)) = associative-mul-ℤ[iᵉ]
pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ ℤ[i]-Ringᵉ))) = one-ℤ[iᵉ]
pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ ℤ[i]-Ringᵉ)))) = left-unit-law-mul-ℤ[iᵉ]
pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ ℤ[i]-Ringᵉ)))) = right-unit-law-mul-ℤ[iᵉ]
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ℤ[i]-Ringᵉ))) = left-distributive-mul-add-ℤ[iᵉ]
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ℤ[i]-Ringᵉ))) = right-distributive-mul-add-ℤ[iᵉ]

ℤ[i]-Commutative-Ringᵉ : Commutative-Ringᵉ lzero
pr1ᵉ ℤ[i]-Commutative-Ringᵉ = ℤ[i]-Ringᵉ
pr2ᵉ ℤ[i]-Commutative-Ringᵉ = commutative-mul-ℤ[iᵉ]
```