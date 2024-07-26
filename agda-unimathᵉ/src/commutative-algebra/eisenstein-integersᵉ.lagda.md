# The Eisenstein integers

```agda
module commutative-algebra.eisenstein-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ

open import elementary-number-theory.addition-integersᵉ
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

Theᵉ **Eisensteinᵉ integers**ᵉ areᵉ theᵉ complexᵉ numbersᵉ ofᵉ theᵉ formᵉ `aᵉ +ᵉ bω`,ᵉ where
`ωᵉ = -½ᵉ +ᵉ ½√3i`,ᵉ andᵉ where `a`ᵉ andᵉ `b`ᵉ areᵉ integers.ᵉ Noteᵉ thatᵉ `ω`ᵉ isᵉ aᵉ solutionᵉ
to theᵉ equationᵉ `ω²ᵉ +ᵉ ωᵉ +ᵉ 1 = 0`.ᵉ

## Definition

### The underlying type of the Eisenstein integers

```agda
ℤ[ωᵉ] : UUᵉ lzero
ℤ[ωᵉ] = ℤᵉ ×ᵉ ℤᵉ
```

### Observational equality of the Eisenstein integers

```agda
Eq-ℤ[ωᵉ] : ℤ[ωᵉ] → ℤ[ωᵉ] → UUᵉ lzero
Eq-ℤ[ωᵉ] xᵉ yᵉ = (pr1ᵉ xᵉ ＝ᵉ pr1ᵉ yᵉ) ×ᵉ (pr2ᵉ xᵉ ＝ᵉ pr2ᵉ yᵉ)

refl-Eq-ℤ[ωᵉ] : (xᵉ : ℤ[ωᵉ]) → Eq-ℤ[ωᵉ] xᵉ xᵉ
pr1ᵉ (refl-Eq-ℤ[ωᵉ] xᵉ) = reflᵉ
pr2ᵉ (refl-Eq-ℤ[ωᵉ] xᵉ) = reflᵉ

Eq-eq-ℤ[ωᵉ] : {xᵉ yᵉ : ℤ[ωᵉ]} → xᵉ ＝ᵉ yᵉ → Eq-ℤ[ωᵉ] xᵉ yᵉ
Eq-eq-ℤ[ωᵉ] {xᵉ} reflᵉ = refl-Eq-ℤ[ωᵉ] xᵉ

eq-Eq-ℤ[ω]'ᵉ : {xᵉ yᵉ : ℤ[ωᵉ]} → Eq-ℤ[ωᵉ] xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
eq-Eq-ℤ[ω]'ᵉ {aᵉ ,ᵉ bᵉ} {.aᵉ ,ᵉ .bᵉ} (reflᵉ ,ᵉ reflᵉ) = reflᵉ

eq-Eq-ℤ[ωᵉ] : {xᵉ yᵉ : ℤ[ωᵉ]} → (pr1ᵉ xᵉ ＝ᵉ pr1ᵉ yᵉ) → (pr2ᵉ xᵉ ＝ᵉ pr2ᵉ yᵉ) → xᵉ ＝ᵉ yᵉ
eq-Eq-ℤ[ωᵉ] {aᵉ ,ᵉ bᵉ} {.aᵉ ,ᵉ .bᵉ} reflᵉ reflᵉ = reflᵉ
```

### The Eisenstein integer zero

```agda
zero-ℤ[ωᵉ] : ℤ[ωᵉ]
pr1ᵉ zero-ℤ[ωᵉ] = zero-ℤᵉ
pr2ᵉ zero-ℤ[ωᵉ] = zero-ℤᵉ
```

### The Eisenstein integer one

```agda
one-ℤ[ωᵉ] : ℤ[ωᵉ]
pr1ᵉ one-ℤ[ωᵉ] = one-ℤᵉ
pr2ᵉ one-ℤ[ωᵉ] = zero-ℤᵉ
```

### The inclusion of the integers into the Eisenstein integers

```agda
eisenstein-int-ℤᵉ : ℤᵉ → ℤ[ωᵉ]
pr1ᵉ (eisenstein-int-ℤᵉ xᵉ) = xᵉ
pr2ᵉ (eisenstein-int-ℤᵉ xᵉ) = zero-ℤᵉ
```

### The Eisenstein integer ω

```agda
ω-ℤ[ωᵉ] : ℤ[ωᵉ]
pr1ᵉ ω-ℤ[ωᵉ] = zero-ℤᵉ
pr2ᵉ ω-ℤ[ωᵉ] = one-ℤᵉ
```

### The Eisenstein integer -ω

```agda
neg-ω-ℤ[ωᵉ] : ℤ[ωᵉ]
pr1ᵉ neg-ω-ℤ[ωᵉ] = zero-ℤᵉ
pr2ᵉ neg-ω-ℤ[ωᵉ] = neg-one-ℤᵉ
```

### Addition of Eisenstein integers

```agda
add-ℤ[ωᵉ] : ℤ[ωᵉ] → ℤ[ωᵉ] → ℤ[ωᵉ]
pr1ᵉ (add-ℤ[ωᵉ] (aᵉ ,ᵉ bᵉ) (a'ᵉ ,ᵉ b'ᵉ)) = aᵉ +ℤᵉ a'ᵉ
pr2ᵉ (add-ℤ[ωᵉ] (aᵉ ,ᵉ bᵉ) (a'ᵉ ,ᵉ b'ᵉ)) = bᵉ +ℤᵉ b'ᵉ

infixl 35 _+ℤ[ωᵉ]_
_+ℤ[ωᵉ]_ = add-ℤ[ωᵉ]

ap-add-ℤ[ωᵉ] :
  {xᵉ x'ᵉ yᵉ y'ᵉ : ℤ[ωᵉ]} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → xᵉ +ℤ[ωᵉ] yᵉ ＝ᵉ x'ᵉ +ℤ[ωᵉ] y'ᵉ
ap-add-ℤ[ωᵉ] pᵉ qᵉ = ap-binaryᵉ add-ℤ[ωᵉ] pᵉ qᵉ
```

### Negatives of Eisenstein integers

```agda
neg-ℤ[ωᵉ] : ℤ[ωᵉ] → ℤ[ωᵉ]
pr1ᵉ (neg-ℤ[ωᵉ] (aᵉ ,ᵉ bᵉ)) = neg-ℤᵉ aᵉ
pr2ᵉ (neg-ℤ[ωᵉ] (aᵉ ,ᵉ bᵉ)) = neg-ℤᵉ bᵉ
```

### Multiplication of Eisenstein integers

Noteᵉ thatᵉ `(aᵉ +ᵉ bω)(cᵉ +ᵉ dωᵉ) = (acᵉ -ᵉ bdᵉ) +ᵉ (adᵉ +ᵉ cbᵉ -ᵉ bd)ω`ᵉ

```agda
mul-ℤ[ωᵉ] : ℤ[ωᵉ] → ℤ[ωᵉ] → ℤ[ωᵉ]
pr1ᵉ (mul-ℤ[ωᵉ] (a1ᵉ ,ᵉ b1ᵉ) (a2ᵉ ,ᵉ b2ᵉ)) =
  (a1ᵉ *ℤᵉ a2ᵉ) +ℤᵉ (neg-ℤᵉ (b1ᵉ *ℤᵉ b2ᵉ))
pr2ᵉ (mul-ℤ[ωᵉ] (a1ᵉ ,ᵉ b1ᵉ) (a2ᵉ ,ᵉ b2ᵉ)) =
  ((a1ᵉ *ℤᵉ b2ᵉ) +ℤᵉ (a2ᵉ *ℤᵉ b1ᵉ)) +ℤᵉ (neg-ℤᵉ (b1ᵉ *ℤᵉ b2ᵉ))

infixl 40 _*ℤ[ωᵉ]_
_*ℤ[ωᵉ]_ = mul-ℤ[ωᵉ]

ap-mul-ℤ[ωᵉ] :
  {xᵉ x'ᵉ yᵉ y'ᵉ : ℤ[ωᵉ]} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → xᵉ *ℤ[ωᵉ] yᵉ ＝ᵉ x'ᵉ *ℤ[ωᵉ] y'ᵉ
ap-mul-ℤ[ωᵉ] pᵉ qᵉ = ap-binaryᵉ mul-ℤ[ωᵉ] pᵉ qᵉ
```

### Conjugation of Eisenstein integers

Theᵉ conjugateᵉ ofᵉ `aᵉ +ᵉ bω`ᵉ isᵉ `aᵉ +ᵉ bω²`,ᵉ whichᵉ isᵉ `(aᵉ -ᵉ bᵉ) -ᵉ bω`.ᵉ

```agda
conjugate-ℤ[ωᵉ] : ℤ[ωᵉ] → ℤ[ωᵉ]
pr1ᵉ (conjugate-ℤ[ωᵉ] (aᵉ ,ᵉ bᵉ)) = aᵉ +ℤᵉ (neg-ℤᵉ bᵉ)
pr2ᵉ (conjugate-ℤ[ωᵉ] (aᵉ ,ᵉ bᵉ)) = neg-ℤᵉ bᵉ

conjugate-conjugate-ℤ[ωᵉ] :
  (xᵉ : ℤ[ωᵉ]) → conjugate-ℤ[ωᵉ] (conjugate-ℤ[ωᵉ] xᵉ) ＝ᵉ xᵉ
conjugate-conjugate-ℤ[ωᵉ] (aᵉ ,ᵉ bᵉ) =
  eq-Eq-ℤ[ωᵉ] (is-retraction-right-add-neg-ℤᵉ (neg-ℤᵉ bᵉ) aᵉ) (neg-neg-ℤᵉ bᵉ)
```

### The Eisenstein integers form a ring with conjugation

```agda
left-unit-law-add-ℤ[ωᵉ] : (xᵉ : ℤ[ωᵉ]) → zero-ℤ[ωᵉ] +ℤ[ωᵉ] xᵉ ＝ᵉ xᵉ
left-unit-law-add-ℤ[ωᵉ] (aᵉ ,ᵉ bᵉ) = eq-Eq-ℤ[ωᵉ] reflᵉ reflᵉ

right-unit-law-add-ℤ[ωᵉ] : (xᵉ : ℤ[ωᵉ]) → xᵉ +ℤ[ωᵉ] zero-ℤ[ωᵉ] ＝ᵉ xᵉ
right-unit-law-add-ℤ[ωᵉ] (aᵉ ,ᵉ bᵉ) =
  eq-Eq-ℤ[ωᵉ] (right-unit-law-add-ℤᵉ aᵉ) (right-unit-law-add-ℤᵉ bᵉ)

associative-add-ℤ[ωᵉ] :
  (xᵉ yᵉ zᵉ : ℤ[ωᵉ]) → (xᵉ +ℤ[ωᵉ] yᵉ) +ℤ[ωᵉ] zᵉ ＝ᵉ xᵉ +ℤ[ωᵉ] (yᵉ +ℤ[ωᵉ] zᵉ)
associative-add-ℤ[ωᵉ] (aᵉ ,ᵉ bᵉ) (cᵉ ,ᵉ dᵉ) (eᵉ ,ᵉ fᵉ) =
  eq-Eq-ℤ[ωᵉ] (associative-add-ℤᵉ aᵉ cᵉ eᵉ) (associative-add-ℤᵉ bᵉ dᵉ fᵉ)

left-inverse-law-add-ℤ[ωᵉ] :
  (xᵉ : ℤ[ωᵉ]) → (neg-ℤ[ωᵉ] xᵉ) +ℤ[ωᵉ] xᵉ ＝ᵉ zero-ℤ[ωᵉ]
left-inverse-law-add-ℤ[ωᵉ] (aᵉ ,ᵉ bᵉ) =
  eq-Eq-ℤ[ωᵉ] (left-inverse-law-add-ℤᵉ aᵉ) (left-inverse-law-add-ℤᵉ bᵉ)

right-inverse-law-add-ℤ[ωᵉ] :
  (xᵉ : ℤ[ωᵉ]) → xᵉ +ℤ[ωᵉ] (neg-ℤ[ωᵉ] xᵉ) ＝ᵉ zero-ℤ[ωᵉ]
right-inverse-law-add-ℤ[ωᵉ] (aᵉ ,ᵉ bᵉ) =
  eq-Eq-ℤ[ωᵉ] (right-inverse-law-add-ℤᵉ aᵉ) (right-inverse-law-add-ℤᵉ bᵉ)

commutative-add-ℤ[ωᵉ] :
  (xᵉ yᵉ : ℤ[ωᵉ]) → xᵉ +ℤ[ωᵉ] yᵉ ＝ᵉ yᵉ +ℤ[ωᵉ] xᵉ
commutative-add-ℤ[ωᵉ] (aᵉ ,ᵉ bᵉ) (a'ᵉ ,ᵉ b'ᵉ) =
  eq-Eq-ℤ[ωᵉ] (commutative-add-ℤᵉ aᵉ a'ᵉ) (commutative-add-ℤᵉ bᵉ b'ᵉ)

left-unit-law-mul-ℤ[ωᵉ] :
  (xᵉ : ℤ[ωᵉ]) → one-ℤ[ωᵉ] *ℤ[ωᵉ] xᵉ ＝ᵉ xᵉ
left-unit-law-mul-ℤ[ωᵉ] (aᵉ ,ᵉ bᵉ) =
  eq-Eq-ℤ[ωᵉ]
    ( right-unit-law-add-ℤᵉ aᵉ)
    ( ( right-unit-law-add-ℤᵉ (bᵉ +ℤᵉ (aᵉ *ℤᵉ zero-ℤᵉ))) ∙ᵉ
      ( ( apᵉ (bᵉ +ℤᵉ_) (right-zero-law-mul-ℤᵉ aᵉ)) ∙ᵉ
        ( right-unit-law-add-ℤᵉ bᵉ)))

right-unit-law-mul-ℤ[ωᵉ] :
  (xᵉ : ℤ[ωᵉ]) → xᵉ *ℤ[ωᵉ] one-ℤ[ωᵉ] ＝ᵉ xᵉ
right-unit-law-mul-ℤ[ωᵉ] (aᵉ ,ᵉ bᵉ) =
  eq-Eq-ℤ[ωᵉ]
    ( ( ap-add-ℤᵉ (right-unit-law-mul-ℤᵉ aᵉ) (apᵉ neg-ℤᵉ (right-zero-law-mul-ℤᵉ bᵉ))) ∙ᵉ
      ( right-unit-law-add-ℤᵉ aᵉ))
    ( ( ap-add-ℤᵉ
        ( apᵉ (_+ℤᵉ bᵉ) (right-zero-law-mul-ℤᵉ aᵉ))
        ( apᵉ neg-ℤᵉ (right-zero-law-mul-ℤᵉ bᵉ))) ∙ᵉ
      ( right-unit-law-add-ℤᵉ bᵉ))

commutative-mul-ℤ[ωᵉ] :
  (xᵉ yᵉ : ℤ[ωᵉ]) → xᵉ *ℤ[ωᵉ] yᵉ ＝ᵉ yᵉ *ℤ[ωᵉ] xᵉ
commutative-mul-ℤ[ωᵉ] (aᵉ ,ᵉ bᵉ) (cᵉ ,ᵉ dᵉ) =
  eq-Eq-ℤ[ωᵉ]
    ( ap-add-ℤᵉ (commutative-mul-ℤᵉ aᵉ cᵉ) (apᵉ neg-ℤᵉ (commutative-mul-ℤᵉ bᵉ dᵉ)))
    ( ap-add-ℤᵉ
      ( commutative-add-ℤᵉ (aᵉ *ℤᵉ dᵉ) (cᵉ *ℤᵉ bᵉ))
      ( apᵉ neg-ℤᵉ (commutative-mul-ℤᵉ bᵉ dᵉ)))

associative-mul-ℤ[ωᵉ] :
  (xᵉ yᵉ zᵉ : ℤ[ωᵉ]) → (xᵉ *ℤ[ωᵉ] yᵉ) *ℤ[ωᵉ] zᵉ ＝ᵉ xᵉ *ℤ[ωᵉ] (yᵉ *ℤ[ωᵉ] zᵉ)
associative-mul-ℤ[ωᵉ] (aᵉ ,ᵉ bᵉ) (cᵉ ,ᵉ dᵉ) (eᵉ ,ᵉ fᵉ) =
  eq-Eq-ℤ[ωᵉ]
    ( ( ap-add-ℤᵉ
        ( ( right-distributive-mul-add-ℤᵉ
            ( aᵉ *ℤᵉ cᵉ)
            ( neg-ℤᵉ (bᵉ *ℤᵉ dᵉ))
            ( eᵉ)) ∙ᵉ
          ( ap-add-ℤᵉ
            ( associative-mul-ℤᵉ aᵉ cᵉ eᵉ)
            ( ( left-negative-law-mul-ℤᵉ (bᵉ *ℤᵉ dᵉ) eᵉ) ∙ᵉ
              ( apᵉ neg-ℤᵉ (associative-mul-ℤᵉ bᵉ dᵉ eᵉ)))))
        ( ( apᵉ
            ( neg-ℤᵉ)
            ( ( right-distributive-mul-add-ℤᵉ
                ( (aᵉ *ℤᵉ dᵉ) +ℤᵉ (cᵉ *ℤᵉ bᵉ))
                ( neg-ℤᵉ (bᵉ *ℤᵉ dᵉ))
                ( fᵉ)) ∙ᵉ
              ( ap-add-ℤᵉ
                ( ( right-distributive-mul-add-ℤᵉ (aᵉ *ℤᵉ dᵉ) (cᵉ *ℤᵉ bᵉ) fᵉ) ∙ᵉ
                  ( ap-add-ℤᵉ
                    ( associative-mul-ℤᵉ aᵉ dᵉ fᵉ)
                    ( ( apᵉ (_*ℤᵉ fᵉ) (commutative-mul-ℤᵉ cᵉ bᵉ)) ∙ᵉ
                      ( associative-mul-ℤᵉ bᵉ cᵉ fᵉ))))
                ( ( left-negative-law-mul-ℤᵉ (bᵉ *ℤᵉ dᵉ) fᵉ) ∙ᵉ
                  ( apᵉ neg-ℤᵉ (associative-mul-ℤᵉ bᵉ dᵉ fᵉ)))))) ∙ᵉ
          ( ( distributive-neg-add-ℤᵉ
              ( (aᵉ *ℤᵉ (dᵉ *ℤᵉ fᵉ)) +ℤᵉ (bᵉ *ℤᵉ (cᵉ *ℤᵉ fᵉ)))
              ( neg-ℤᵉ (bᵉ *ℤᵉ (dᵉ *ℤᵉ fᵉ)))) ∙ᵉ
            ( ( ap-add-ℤᵉ
                ( distributive-neg-add-ℤᵉ
                  ( aᵉ *ℤᵉ (dᵉ *ℤᵉ fᵉ))
                  ( bᵉ *ℤᵉ (cᵉ *ℤᵉ fᵉ)))
                ( reflᵉ
                  { xᵉ = neg-ℤᵉ (neg-ℤᵉ (bᵉ *ℤᵉ (dᵉ *ℤᵉ fᵉ)))})) ∙ᵉ
              ( associative-add-ℤᵉ
                ( neg-ℤᵉ (aᵉ *ℤᵉ (dᵉ *ℤᵉ fᵉ)))
                ( neg-ℤᵉ (bᵉ *ℤᵉ (cᵉ *ℤᵉ fᵉ)))
                ( neg-ℤᵉ (neg-ℤᵉ (bᵉ *ℤᵉ (dᵉ *ℤᵉ fᵉ))))))))) ∙ᵉ
      ( ( interchange-law-add-add-ℤᵉ
          ( aᵉ *ℤᵉ (cᵉ *ℤᵉ eᵉ))
          ( neg-ℤᵉ (bᵉ *ℤᵉ (dᵉ *ℤᵉ eᵉ)))
          ( neg-ℤᵉ (aᵉ *ℤᵉ (dᵉ *ℤᵉ fᵉ)))
          ( ( neg-ℤᵉ (bᵉ *ℤᵉ (cᵉ *ℤᵉ fᵉ))) +ℤᵉ (neg-ℤᵉ (neg-ℤᵉ (bᵉ *ℤᵉ (dᵉ *ℤᵉ fᵉ)))))) ∙ᵉ
        ( ap-add-ℤᵉ
          ( ( apᵉ
              ( (aᵉ *ℤᵉ (cᵉ *ℤᵉ eᵉ)) +ℤᵉ_)
              ( invᵉ ( right-negative-law-mul-ℤᵉ aᵉ (dᵉ *ℤᵉ fᵉ)))) ∙ᵉ
            ( invᵉ
              ( left-distributive-mul-add-ℤᵉ aᵉ (cᵉ *ℤᵉ eᵉ) (neg-ℤᵉ (dᵉ *ℤᵉ fᵉ)))))
          ( ( apᵉ
              ( (neg-ℤᵉ (bᵉ *ℤᵉ (dᵉ *ℤᵉ eᵉ))) +ℤᵉ_)
              ( invᵉ
                ( distributive-neg-add-ℤᵉ
                  ( bᵉ *ℤᵉ (cᵉ *ℤᵉ fᵉ))
                  ( neg-ℤᵉ (bᵉ *ℤᵉ (dᵉ *ℤᵉ fᵉ)))))) ∙ᵉ
            ( ( invᵉ
                ( distributive-neg-add-ℤᵉ
                  ( bᵉ *ℤᵉ (dᵉ *ℤᵉ eᵉ))
                  ( (bᵉ *ℤᵉ (cᵉ *ℤᵉ fᵉ)) +ℤᵉ (neg-ℤᵉ (bᵉ *ℤᵉ (dᵉ *ℤᵉ fᵉ)))))) ∙ᵉ
              ( apᵉ
                ( neg-ℤᵉ)
                ( ( apᵉ
                    ( (bᵉ *ℤᵉ (dᵉ *ℤᵉ eᵉ)) +ℤᵉ_)
                    ( ( apᵉ
                        ( (bᵉ *ℤᵉ (cᵉ *ℤᵉ fᵉ)) +ℤᵉ_)
                        ( invᵉ (right-negative-law-mul-ℤᵉ bᵉ (dᵉ *ℤᵉ fᵉ)))) ∙ᵉ
                      ( invᵉ
                        ( left-distributive-mul-add-ℤᵉ bᵉ
                          ( cᵉ *ℤᵉ fᵉ)
                          ( neg-ℤᵉ (dᵉ *ℤᵉ fᵉ)))))) ∙ᵉ
                  ( ( invᵉ
                      ( left-distributive-mul-add-ℤᵉ bᵉ
                        ( dᵉ *ℤᵉ eᵉ)
                        ( (cᵉ *ℤᵉ fᵉ) +ℤᵉ (neg-ℤᵉ (dᵉ *ℤᵉ fᵉ))))) ∙ᵉ
                    ( apᵉ
                      ( bᵉ *ℤᵉ_)
                      ( ( invᵉ
                          ( associative-add-ℤᵉ
                            ( dᵉ *ℤᵉ eᵉ)
                            ( cᵉ *ℤᵉ fᵉ)
                            ( neg-ℤᵉ (dᵉ *ℤᵉ fᵉ)))) ∙ᵉ
                        ( apᵉ
                          ( _+ℤᵉ (neg-ℤᵉ (dᵉ *ℤᵉ fᵉ)))
                          ( ( commutative-add-ℤᵉ (dᵉ *ℤᵉ eᵉ) (cᵉ *ℤᵉ fᵉ)) ∙ᵉ
                            ( apᵉ
                              ( (cᵉ *ℤᵉ fᵉ) +ℤᵉ_)
                              ( commutative-mul-ℤᵉ dᵉ eᵉ))))))))))))))
    ( ( ap-add-ℤᵉ
        ( ( ap-add-ℤᵉ
            ( ( right-distributive-mul-add-ℤᵉ acᵉ (neg-ℤᵉ bdᵉ) fᵉ) ∙ᵉ
              ( ap-add-ℤᵉ
                ( associative-mul-ℤᵉ aᵉ cᵉ fᵉ)
                ( ( left-negative-law-mul-ℤᵉ bdᵉ fᵉ) ∙ᵉ
                  ( ( apᵉ neg-ℤᵉ (associative-mul-ℤᵉ bᵉ dᵉ fᵉ)) ∙ᵉ
                    ( ( invᵉ (right-negative-law-mul-ℤᵉ bᵉ dfᵉ)) ∙ᵉ
                      ( commutative-mul-ℤᵉ bᵉ (neg-ℤᵉ dfᵉ)))))))
            ( ( left-distributive-mul-add-ℤᵉ eᵉ (adᵉ +ℤᵉ cbᵉ) (neg-ℤᵉ bdᵉ)) ∙ᵉ
              ( ( ap-add-ℤᵉ
                  ( ( left-distributive-mul-add-ℤᵉ eᵉ adᵉ cbᵉ) ∙ᵉ
                    ( ap-add-ℤᵉ
                      ( ( commutative-mul-ℤᵉ eᵉ adᵉ) ∙ᵉ
                        ( ( associative-mul-ℤᵉ aᵉ dᵉ eᵉ) ∙ᵉ
                          ( apᵉ (aᵉ *ℤᵉ_) (commutative-mul-ℤᵉ dᵉ eᵉ))))
                      ( ( apᵉ (eᵉ *ℤᵉ_) (commutative-mul-ℤᵉ cᵉ bᵉ)) ∙ᵉ
                        ( ( commutative-mul-ℤᵉ eᵉ (bᵉ *ℤᵉ cᵉ)) ∙ᵉ
                          ( ( associative-mul-ℤᵉ bᵉ cᵉ eᵉ) ∙ᵉ
                            ( commutative-mul-ℤᵉ bᵉ ceᵉ))))))
                  ( ( right-negative-law-mul-ℤᵉ eᵉ bdᵉ) ∙ᵉ
                    ( ( apᵉ
                        ( neg-ℤᵉ)
                        ( ( commutative-mul-ℤᵉ eᵉ bdᵉ) ∙ᵉ
                          ( associative-mul-ℤᵉ bᵉ dᵉ eᵉ))) ∙ᵉ
                      ( apᵉ
                        ( neg-ℤᵉ)
                        ( apᵉ (bᵉ *ℤᵉ_) (commutative-mul-ℤᵉ dᵉ eᵉ)))))) ∙ᵉ
                ( associative-add-ℤᵉ
                  ( aᵉ *ℤᵉ edᵉ)
                  ( ceᵉ *ℤᵉ bᵉ)
                  ( neg-ℤᵉ (bᵉ *ℤᵉ edᵉ)))))) ∙ᵉ
          ( ( interchange-law-add-add-ℤᵉ
              ( aᵉ *ℤᵉ cfᵉ)
              ( (neg-ℤᵉ dfᵉ) *ℤᵉ bᵉ)
              ( aᵉ *ℤᵉ edᵉ)
              ( (ceᵉ *ℤᵉ bᵉ) +ℤᵉ (neg-ℤᵉ (bᵉ *ℤᵉ edᵉ)))) ∙ᵉ
            ( ( ap-add-ℤᵉ
                ( invᵉ (left-distributive-mul-add-ℤᵉ aᵉ cfᵉ edᵉ))
                ( ( invᵉ
                    ( associative-add-ℤᵉ
                      ( (neg-ℤᵉ dfᵉ) *ℤᵉ bᵉ)
                      ( ceᵉ *ℤᵉ bᵉ)
                      ( neg-ℤᵉ (bᵉ *ℤᵉ edᵉ)))) ∙ᵉ
                  ( apᵉ
                    ( _+ℤᵉ (neg-ℤᵉ (bᵉ *ℤᵉ edᵉ)))
                    ( ( commutative-add-ℤᵉ ((neg-ℤᵉ dfᵉ) *ℤᵉ bᵉ) (ceᵉ *ℤᵉ bᵉ)) ∙ᵉ
                      ( invᵉ
                        ( right-distributive-mul-add-ℤᵉ ceᵉ (neg-ℤᵉ dfᵉ) bᵉ)))))) ∙ᵉ
              ( ( invᵉ
                  ( associative-add-ℤᵉ
                    ( aᵉ *ℤᵉ (cfᵉ +ℤᵉ edᵉ))
                    ( (ceᵉ +ℤᵉ (neg-ℤᵉ dfᵉ)) *ℤᵉ bᵉ)
                    ( neg-ℤᵉ (bᵉ *ℤᵉ edᵉ)))) ∙ᵉ
                ( ( apᵉ
                    ( _+ℤᵉ (neg-ℤᵉ (bᵉ *ℤᵉ edᵉ)))
                    ( commutative-add-ℤᵉ
                      ( aᵉ *ℤᵉ (cfᵉ +ℤᵉ edᵉ))
                      ( (ceᵉ +ℤᵉ (neg-ℤᵉ dfᵉ)) *ℤᵉ bᵉ))) ∙ᵉ
                  ( associative-add-ℤᵉ
                    ( (ceᵉ +ℤᵉ (neg-ℤᵉ dfᵉ)) *ℤᵉ bᵉ)
                    ( aᵉ *ℤᵉ (cfᵉ +ℤᵉ edᵉ))
                    ( neg-ℤᵉ (bᵉ *ℤᵉ edᵉ))))))))
        ( ( invᵉ (left-negative-law-mul-ℤᵉ ((adᵉ +ℤᵉ cbᵉ) +ℤᵉ (neg-ℤᵉ bdᵉ)) fᵉ)) ∙ᵉ
          ( ( apᵉ
              ( _*ℤᵉ fᵉ)
              ( ( distributive-neg-add-ℤᵉ (adᵉ +ℤᵉ cbᵉ) (neg-ℤᵉ bdᵉ)) ∙ᵉ
                ( ap-add-ℤᵉ (distributive-neg-add-ℤᵉ adᵉ cbᵉ) (neg-neg-ℤᵉ bdᵉ)))) ∙ᵉ
            ( ( right-distributive-mul-add-ℤᵉ
                ( (neg-ℤᵉ adᵉ) +ℤᵉ (neg-ℤᵉ cbᵉ))
                ( bdᵉ)
                ( fᵉ)) ∙ᵉ
              ( ( ap-add-ℤᵉ
                  ( ( right-distributive-mul-add-ℤᵉ (neg-ℤᵉ adᵉ) (neg-ℤᵉ cbᵉ) fᵉ) ∙ᵉ
                    ( ap-add-ℤᵉ
                      ( ( left-negative-law-mul-ℤᵉ adᵉ fᵉ) ∙ᵉ
                        ( ( apᵉ
                            ( neg-ℤᵉ)
                            ( associative-mul-ℤᵉ aᵉ dᵉ fᵉ)) ∙ᵉ
                          ( invᵉ (right-negative-law-mul-ℤᵉ aᵉ dfᵉ))))
                      ( ( left-negative-law-mul-ℤᵉ cbᵉ fᵉ) ∙ᵉ
                        ( apᵉ
                          ( neg-ℤᵉ)
                          ( ( apᵉ
                              ( _*ℤᵉ fᵉ)
                              ( commutative-mul-ℤᵉ cᵉ bᵉ)) ∙ᵉ
                            ( associative-mul-ℤᵉ bᵉ cᵉ fᵉ))))))
                  ( ( associative-mul-ℤᵉ bᵉ dᵉ fᵉ) ∙ᵉ
                    ( ( invᵉ (neg-neg-ℤᵉ (bᵉ *ℤᵉ dfᵉ))) ∙ᵉ
                      ( apᵉ neg-ℤᵉ (invᵉ (right-negative-law-mul-ℤᵉ bᵉ dfᵉ)))))) ∙ᵉ
                ( ( associative-add-ℤᵉ
                    ( aᵉ *ℤᵉ ( neg-ℤᵉ dfᵉ))
                    ( neg-ℤᵉ (bᵉ *ℤᵉ cfᵉ))
                    ( neg-ℤᵉ (bᵉ *ℤᵉ (neg-ℤᵉ dfᵉ)))) ∙ᵉ
                  ( apᵉ
                    ( (aᵉ *ℤᵉ (neg-ℤᵉ dfᵉ)) +ℤᵉ_)
                    ( ( invᵉ
                        ( distributive-neg-add-ℤᵉ
                          ( bᵉ *ℤᵉ cfᵉ)
                          ( bᵉ *ℤᵉ (neg-ℤᵉ dfᵉ)))) ∙ᵉ
                      ( apᵉ
                        ( neg-ℤᵉ)
                        ( invᵉ
                          ( left-distributive-mul-add-ℤᵉ
                            ( bᵉ)
                            ( cfᵉ)
                            ( neg-ℤᵉ dfᵉ)))))))))))) ∙ᵉ
      ( ( associative-add-ℤᵉ
          ( (ceᵉ +ℤᵉ (neg-ℤᵉ dfᵉ)) *ℤᵉ bᵉ)
          ( (aᵉ *ℤᵉ (cfᵉ +ℤᵉ edᵉ)) +ℤᵉ (neg-ℤᵉ (bᵉ *ℤᵉ edᵉ)))
          ( (aᵉ *ℤᵉ (neg-ℤᵉ dfᵉ)) +ℤᵉ (neg-ℤᵉ (bᵉ *ℤᵉ (cfᵉ +ℤᵉ (neg-ℤᵉ dfᵉ)))))) ∙ᵉ
        ( ( ( apᵉ
              ( ((ceᵉ +ℤᵉ (neg-ℤᵉ dfᵉ)) *ℤᵉ bᵉ) +ℤᵉ_)
              ( ( interchange-law-add-add-ℤᵉ
                  ( aᵉ *ℤᵉ (cfᵉ +ℤᵉ edᵉ))
                  ( neg-ℤᵉ (bᵉ *ℤᵉ edᵉ))
                  ( aᵉ *ℤᵉ (neg-ℤᵉ dfᵉ))
                  ( neg-ℤᵉ (bᵉ *ℤᵉ (cfᵉ +ℤᵉ (neg-ℤᵉ dfᵉ))))) ∙ᵉ
                ( ap-add-ℤᵉ
                  ( invᵉ
                    ( left-distributive-mul-add-ℤᵉ aᵉ (cfᵉ +ℤᵉ edᵉ) (neg-ℤᵉ dfᵉ)))
                  ( ( invᵉ
                      ( distributive-neg-add-ℤᵉ
                        ( bᵉ *ℤᵉ edᵉ)
                        ( bᵉ *ℤᵉ (cfᵉ +ℤᵉ (neg-ℤᵉ dfᵉ))))) ∙ᵉ
                    ( apᵉ
                      ( neg-ℤᵉ)
                      ( ( invᵉ
                          ( left-distributive-mul-add-ℤᵉ bᵉ edᵉ
                            ( cfᵉ +ℤᵉ (neg-ℤᵉ dfᵉ)))) ∙ᵉ
                        ( apᵉ
                          ( bᵉ *ℤᵉ_)
                          ( ( invᵉ
                              ( associative-add-ℤᵉ edᵉ cfᵉ (neg-ℤᵉ dfᵉ))) ∙ᵉ
                            ( apᵉ
                              ( _+ℤᵉ (neg-ℤᵉ dfᵉ))
                              ( commutative-add-ℤᵉ edᵉ cfᵉ)))))))))) ∙ᵉ
            ( invᵉ
              ( associative-add-ℤᵉ
                ( (ceᵉ +ℤᵉ (neg-ℤᵉ dfᵉ)) *ℤᵉ bᵉ)
                ( aᵉ *ℤᵉ ((cfᵉ +ℤᵉ edᵉ) +ℤᵉ (neg-ℤᵉ dfᵉ)))
                ( neg-ℤᵉ (bᵉ *ℤᵉ ((cfᵉ +ℤᵉ edᵉ) +ℤᵉ (neg-ℤᵉ dfᵉ))))))) ∙ᵉ
          ( apᵉ
            ( _+ℤᵉ (neg-ℤᵉ (bᵉ *ℤᵉ ((cfᵉ +ℤᵉ edᵉ) +ℤᵉ (neg-ℤᵉ dfᵉ)))))
            ( commutative-add-ℤᵉ
              ( (ceᵉ +ℤᵉ (neg-ℤᵉ dfᵉ)) *ℤᵉ bᵉ)
              ( aᵉ *ℤᵉ ((cfᵉ +ℤᵉ edᵉ) +ℤᵉ (neg-ℤᵉ dfᵉ))))))))
    where
    acᵉ = aᵉ *ℤᵉ cᵉ
    bdᵉ = bᵉ *ℤᵉ dᵉ
    adᵉ = aᵉ *ℤᵉ dᵉ
    cbᵉ = cᵉ *ℤᵉ bᵉ
    ceᵉ = cᵉ *ℤᵉ eᵉ
    cfᵉ = cᵉ *ℤᵉ fᵉ
    edᵉ = eᵉ *ℤᵉ dᵉ
    dfᵉ = dᵉ *ℤᵉ fᵉ

left-distributive-mul-add-ℤ[ωᵉ] :
  (xᵉ yᵉ zᵉ : ℤ[ωᵉ]) →
  xᵉ *ℤ[ωᵉ] (yᵉ +ℤ[ωᵉ] zᵉ) ＝ᵉ (xᵉ *ℤ[ωᵉ] yᵉ) +ℤ[ωᵉ] (xᵉ *ℤ[ωᵉ] zᵉ)
left-distributive-mul-add-ℤ[ωᵉ] (aᵉ ,ᵉ bᵉ) (cᵉ ,ᵉ dᵉ) (eᵉ ,ᵉ fᵉ) =
  eq-Eq-ℤ[ωᵉ]
    ( ( ap-add-ℤᵉ
        ( left-distributive-mul-add-ℤᵉ aᵉ cᵉ eᵉ)
        ( ( apᵉ
            ( neg-ℤᵉ)
            ( left-distributive-mul-add-ℤᵉ bᵉ dᵉ fᵉ)) ∙ᵉ
          ( distributive-neg-add-ℤᵉ (bᵉ *ℤᵉ dᵉ) (bᵉ *ℤᵉ fᵉ)))) ∙ᵉ
      ( interchange-law-add-add-ℤᵉ
        ( aᵉ *ℤᵉ cᵉ)
        ( aᵉ *ℤᵉ eᵉ)
        ( neg-ℤᵉ (bᵉ *ℤᵉ dᵉ))
        ( neg-ℤᵉ (bᵉ *ℤᵉ fᵉ))))
    ( ( ap-add-ℤᵉ
        ( ( ap-add-ℤᵉ
            ( left-distributive-mul-add-ℤᵉ aᵉ dᵉ fᵉ)
            ( right-distributive-mul-add-ℤᵉ cᵉ eᵉ bᵉ)) ∙ᵉ
          ( interchange-law-add-add-ℤᵉ
            ( aᵉ *ℤᵉ dᵉ)
            ( aᵉ *ℤᵉ fᵉ)
            ( cᵉ *ℤᵉ bᵉ)
            ( eᵉ *ℤᵉ bᵉ)))
        ( ( apᵉ neg-ℤᵉ (left-distributive-mul-add-ℤᵉ bᵉ dᵉ fᵉ)) ∙ᵉ
          ( distributive-neg-add-ℤᵉ (bᵉ *ℤᵉ dᵉ) (bᵉ *ℤᵉ fᵉ)))) ∙ᵉ
      ( interchange-law-add-add-ℤᵉ
        ( (aᵉ *ℤᵉ dᵉ) +ℤᵉ (cᵉ *ℤᵉ bᵉ))
        ( (aᵉ *ℤᵉ fᵉ) +ℤᵉ (eᵉ *ℤᵉ bᵉ))
        ( neg-ℤᵉ (bᵉ *ℤᵉ dᵉ))
        ( neg-ℤᵉ (bᵉ *ℤᵉ fᵉ))))

right-distributive-mul-add-ℤ[ωᵉ] :
  (xᵉ yᵉ zᵉ : ℤ[ωᵉ]) →
  (xᵉ +ℤ[ωᵉ] yᵉ) *ℤ[ωᵉ] zᵉ ＝ᵉ (xᵉ *ℤ[ωᵉ] zᵉ) +ℤ[ωᵉ] (yᵉ *ℤ[ωᵉ] zᵉ)
right-distributive-mul-add-ℤ[ωᵉ] xᵉ yᵉ zᵉ =
  ( commutative-mul-ℤ[ωᵉ] (xᵉ +ℤ[ωᵉ] yᵉ) zᵉ) ∙ᵉ
  ( ( left-distributive-mul-add-ℤ[ωᵉ] zᵉ xᵉ yᵉ) ∙ᵉ
    ( ap-add-ℤ[ωᵉ] (commutative-mul-ℤ[ωᵉ] zᵉ xᵉ) (commutative-mul-ℤ[ωᵉ] zᵉ yᵉ)))

ℤ[ω]-Semigroupᵉ : Semigroupᵉ lzero
pr1ᵉ ℤ[ω]-Semigroupᵉ = product-Setᵉ ℤ-Setᵉ ℤ-Setᵉ
pr1ᵉ (pr2ᵉ ℤ[ω]-Semigroupᵉ) = add-ℤ[ωᵉ]
pr2ᵉ (pr2ᵉ ℤ[ω]-Semigroupᵉ) = associative-add-ℤ[ωᵉ]

ℤ[ω]-Groupᵉ : Groupᵉ lzero
pr1ᵉ ℤ[ω]-Groupᵉ = ℤ[ω]-Semigroupᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ ℤ[ω]-Groupᵉ)) = zero-ℤ[ωᵉ]
pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ ℤ[ω]-Groupᵉ))) = left-unit-law-add-ℤ[ωᵉ]
pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ ℤ[ω]-Groupᵉ))) = right-unit-law-add-ℤ[ωᵉ]
pr1ᵉ (pr2ᵉ (pr2ᵉ ℤ[ω]-Groupᵉ)) = neg-ℤ[ωᵉ]
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ℤ[ω]-Groupᵉ))) = left-inverse-law-add-ℤ[ωᵉ]
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ℤ[ω]-Groupᵉ))) = right-inverse-law-add-ℤ[ωᵉ]

ℤ[ω]-Abᵉ : Abᵉ lzero
pr1ᵉ ℤ[ω]-Abᵉ = ℤ[ω]-Groupᵉ
pr2ᵉ ℤ[ω]-Abᵉ = commutative-add-ℤ[ωᵉ]

ℤ[ω]-Ringᵉ : Ringᵉ lzero
pr1ᵉ ℤ[ω]-Ringᵉ = ℤ[ω]-Abᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ ℤ[ω]-Ringᵉ)) = mul-ℤ[ωᵉ]
pr2ᵉ (pr1ᵉ (pr2ᵉ ℤ[ω]-Ringᵉ)) = associative-mul-ℤ[ωᵉ]
pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ ℤ[ω]-Ringᵉ))) = one-ℤ[ωᵉ]
pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ ℤ[ω]-Ringᵉ)))) = left-unit-law-mul-ℤ[ωᵉ]
pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ ℤ[ω]-Ringᵉ)))) = right-unit-law-mul-ℤ[ωᵉ]
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ℤ[ω]-Ringᵉ))) = left-distributive-mul-add-ℤ[ωᵉ]
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ ℤ[ω]-Ringᵉ))) = right-distributive-mul-add-ℤ[ωᵉ]

ℤ[ω]-Commutative-Ringᵉ : Commutative-Ringᵉ lzero
pr1ᵉ ℤ[ω]-Commutative-Ringᵉ = ℤ[ω]-Ringᵉ
pr2ᵉ ℤ[ω]-Commutative-Ringᵉ = commutative-mul-ℤ[ωᵉ]
```