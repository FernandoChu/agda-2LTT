# Postcomposition of dependent functions

<pre class="Agda"><a id="51" class="Keyword">module</a> <a id="58" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html" class="Module">foundation.postcomposition-dependent-functionsᵉ</a> <a id="106" class="Keyword">where</a>

<a id="113" class="Keyword">open</a> <a id="118" class="Keyword">import</a> <a id="125" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html" class="Module">foundation-core.postcomposition-dependent-functionsᵉ</a> <a id="178" class="Keyword">public</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="235" class="Keyword">open</a> <a id="240" class="Keyword">import</a> <a id="247" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html" class="Module">foundation.action-on-identifications-functionsᵉ</a>
<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="foundation.function-extensionality%25E1%25B5%2589.html" class="Module">foundation.function-extensionalityᵉ</a>
<a id="343" class="Keyword">open</a> <a id="348" class="Keyword">import</a> <a id="355" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
<a id="383" class="Keyword">open</a> <a id="388" class="Keyword">import</a> <a id="395" href="foundation.whiskering-homotopies-composition%25E1%25B5%2589.html" class="Module">foundation.whiskering-homotopies-compositionᵉ</a>

<a id="442" class="Keyword">open</a> <a id="447" class="Keyword">import</a> <a id="454" href="foundation-core.commuting-squares-of-maps%25E1%25B5%2589.html" class="Module">foundation-core.commuting-squares-of-mapsᵉ</a>
<a id="497" class="Keyword">open</a> <a id="502" class="Keyword">import</a> <a id="509" href="foundation-core.function-types%25E1%25B5%2589.html" class="Module">foundation-core.function-typesᵉ</a>
<a id="541" class="Keyword">open</a> <a id="546" class="Keyword">import</a> <a id="553" href="foundation-core.identity-types%25E1%25B5%2589.html" class="Module">foundation-core.identity-typesᵉ</a>
</pre>
</details>

## Idea

Given a type `A` and a family of maps `f : {a : A} → X a → Y a`, the
{{#concept "postcomposition function" Disambiguation="of dependent functions by a family of maps" Agda=postcomp-Π}}
of dependent functions `(a : A) → X a` by the family of maps `f`

```text
  postcomp-Π A f : ((a : A) → X a) → ((a : A) → Y a)
```

is defined by `λ h x → f (h x)`.

Note that, since the definition of the family of maps `f` depends on the base
`A`, postcomposition of dependent functions does not generalize
[postcomposition of functions](foundation-core.postcomposition-functions.md) in
the same way that
[precomposition of dependent functions](foundation-core.precomposition-dependent-functions.md)
generalizes
[precomposition of functions](foundation-core.precomposition-functions.md). If
`A` can vary while keeping `f` fixed, we have necessarily reduced to the case of
[postcomposition of functions](foundation-core.postcomposition-functions.md).

## Properties

### The action on identifications of postcomposition by a family map

Consider a map `f : {x : A} → B x → C x` and two functions
`g h : (x : A) → B x`. Then the
[action on identifications](foundation.action-on-identifications-functions.md)
`ap (postcomp-Π A f)` fits in a
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
                   ap (postcomp-Π A f)
       (g ＝ h) -------------------------> (f ∘ g ＝ f ∘ h)
          |                                       |
  htpy-eq |                                       | htpy-eq
          ∨                                       ∨
       (g ~ h) --------------------------> (f ∘ g ~ f ∘ h).
                          f ·l_
```

Similarly, the action on identifications `ap (postcomp-Π A f)` fits in a
commuting square

```text
                    ap (postcomp-Π A f)
       (g ＝ h) -------------------------> (f ∘ g ＝ f ∘ h)
          ∧                                       ∧
  eq-htpy |                                       | eq-htpy
          |                                       |
       (g ~ h) --------------------------> (f ∘ g ~ f ∘ h).
                          f ·l_
```

<pre class="Agda"><a id="2733" class="Keyword">module</a> <a id="2740" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2740" class="Module">_</a>
  <a id="2744" class="Symbol">{</a><a id="2745" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2745" class="Bound">l1ᵉ</a> <a id="2749" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2749" class="Bound">l2ᵉ</a> <a id="2753" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2753" class="Bound">l3ᵉ</a> <a id="2757" class="Symbol">:</a> <a id="2759" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2764" class="Symbol">}</a> <a id="2766" class="Symbol">{</a><a id="2767" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2767" class="Bound">Aᵉ</a> <a id="2770" class="Symbol">:</a> <a id="2772" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2776" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2745" class="Bound">l1ᵉ</a><a id="2779" class="Symbol">}</a> <a id="2781" class="Symbol">{</a><a id="2782" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2782" class="Bound">Bᵉ</a> <a id="2785" class="Symbol">:</a> <a id="2787" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2767" class="Bound">Aᵉ</a> <a id="2790" class="Symbol">→</a> <a id="2792" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2796" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2749" class="Bound">l2ᵉ</a><a id="2799" class="Symbol">}</a> <a id="2801" class="Symbol">{</a><a id="2802" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2802" class="Bound">Cᵉ</a> <a id="2805" class="Symbol">:</a> <a id="2807" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2767" class="Bound">Aᵉ</a> <a id="2810" class="Symbol">→</a> <a id="2812" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2816" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2753" class="Bound">l3ᵉ</a><a id="2819" class="Symbol">}</a>
  <a id="2823" class="Symbol">(</a><a id="2824" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2824" class="Bound">fᵉ</a> <a id="2827" class="Symbol">:</a> <a id="2829" class="Symbol">{</a><a id="2830" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2830" class="Bound">xᵉ</a> <a id="2833" class="Symbol">:</a> <a id="2835" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2767" class="Bound">Aᵉ</a><a id="2837" class="Symbol">}</a> <a id="2839" class="Symbol">→</a> <a id="2841" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2782" class="Bound">Bᵉ</a> <a id="2844" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2830" class="Bound">xᵉ</a> <a id="2847" class="Symbol">→</a> <a id="2849" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2802" class="Bound">Cᵉ</a> <a id="2852" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2830" class="Bound">xᵉ</a><a id="2854" class="Symbol">)</a> <a id="2856" class="Symbol">{</a><a id="2857" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2857" class="Bound">gᵉ</a> <a id="2860" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2860" class="Bound">hᵉ</a> <a id="2863" class="Symbol">:</a> <a id="2865" class="Symbol">(</a><a id="2866" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2866" class="Bound">xᵉ</a> <a id="2869" class="Symbol">:</a> <a id="2871" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2767" class="Bound">Aᵉ</a><a id="2873" class="Symbol">)</a> <a id="2875" class="Symbol">→</a> <a id="2877" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2782" class="Bound">Bᵉ</a> <a id="2880" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2866" class="Bound">xᵉ</a><a id="2882" class="Symbol">}</a>
  <a id="2886" class="Keyword">where</a>

  <a id="2895" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2895" class="Function">compute-htpy-eq-ap-postcomp-Πᵉ</a> <a id="2926" class="Symbol">:</a>
    <a id="2932" href="foundation-core.commuting-squares-of-maps%25E1%25B5%2589.html#1341" class="Function">coherence-square-mapsᵉ</a>
      <a id="2961" class="Symbol">(</a> <a id="2963" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="2967" class="Symbol">(</a><a id="2968" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1382" class="Function">postcomp-Πᵉ</a> <a id="2980" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2767" class="Bound">Aᵉ</a> <a id="2983" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2824" class="Bound">fᵉ</a><a id="2985" class="Symbol">)</a> <a id="2987" class="Symbol">{</a><a id="2988" class="Argument">xᵉ</a> <a id="2991" class="Symbol">=</a> <a id="2993" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2857" class="Bound">gᵉ</a><a id="2995" class="Symbol">}</a> <a id="2997" class="Symbol">{</a><a id="2998" class="Argument">yᵉ</a> <a id="3001" class="Symbol">=</a> <a id="3003" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2860" class="Bound">hᵉ</a><a id="3005" class="Symbol">})</a>
      <a id="3014" class="Symbol">(</a> <a id="3016" href="foundation.function-extensionality%25E1%25B5%2589.html#1919" class="Function">htpy-eqᵉ</a><a id="3024" class="Symbol">)</a>
      <a id="3032" class="Symbol">(</a> <a id="3034" href="foundation.function-extensionality%25E1%25B5%2589.html#1919" class="Function">htpy-eqᵉ</a><a id="3042" class="Symbol">)</a>
      <a id="3050" class="Symbol">(</a> <a id="3052" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2824" class="Bound">fᵉ</a> <a id="3055" href="foundation.whiskering-homotopies-composition%25E1%25B5%2589.html#2417" class="Function Operator">·lᵉ_</a><a id="3059" class="Symbol">)</a>
  <a id="3063" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2895" class="Function">compute-htpy-eq-ap-postcomp-Πᵉ</a> <a id="3094" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a> <a id="3100" class="Symbol">=</a> <a id="3102" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a>

  <a id="3111" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#3111" class="Function">compute-eq-htpy-ap-postcomp-Πᵉ</a> <a id="3142" class="Symbol">:</a>
    <a id="3148" href="foundation-core.commuting-squares-of-maps%25E1%25B5%2589.html#1341" class="Function">coherence-square-mapsᵉ</a>
      <a id="3177" class="Symbol">(</a> <a id="3179" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2824" class="Bound">fᵉ</a> <a id="3182" href="foundation.whiskering-homotopies-composition%25E1%25B5%2589.html#2417" class="Function Operator">·lᵉ_</a><a id="3186" class="Symbol">)</a>
      <a id="3194" class="Symbol">(</a> <a id="3196" href="foundation.function-extensionality%25E1%25B5%2589.html#4062" class="Postulate">eq-htpyᵉ</a><a id="3204" class="Symbol">)</a>
      <a id="3212" class="Symbol">(</a> <a id="3214" href="foundation.function-extensionality%25E1%25B5%2589.html#4062" class="Postulate">eq-htpyᵉ</a><a id="3222" class="Symbol">)</a>
      <a id="3230" class="Symbol">(</a> <a id="3232" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="3236" class="Symbol">(</a><a id="3237" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1382" class="Function">postcomp-Πᵉ</a> <a id="3249" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2767" class="Bound">Aᵉ</a> <a id="3252" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2824" class="Bound">fᵉ</a><a id="3254" class="Symbol">))</a>
  <a id="3259" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#3111" class="Function">compute-eq-htpy-ap-postcomp-Πᵉ</a> <a id="3290" class="Symbol">=</a>
    <a id="3296" href="foundation-core.commuting-squares-of-maps%25E1%25B5%2589.html#8293" class="Function">vertical-inv-equiv-coherence-square-mapsᵉ</a>
      <a id="3344" class="Symbol">(</a> <a id="3346" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="3350" class="Symbol">(</a><a id="3351" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1382" class="Function">postcomp-Πᵉ</a> <a id="3363" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2767" class="Bound">Aᵉ</a> <a id="3366" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2824" class="Bound">fᵉ</a><a id="3368" class="Symbol">))</a>
      <a id="3377" class="Symbol">(</a> <a id="3379" href="foundation.function-extensionality%25E1%25B5%2589.html#4590" class="Function">equiv-funextᵉ</a><a id="3392" class="Symbol">)</a>
      <a id="3400" class="Symbol">(</a> <a id="3402" href="foundation.function-extensionality%25E1%25B5%2589.html#4590" class="Function">equiv-funextᵉ</a><a id="3415" class="Symbol">)</a>
      <a id="3423" class="Symbol">(</a> <a id="3425" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2824" class="Bound">fᵉ</a> <a id="3428" href="foundation.whiskering-homotopies-composition%25E1%25B5%2589.html#2417" class="Function Operator">·lᵉ_</a><a id="3432" class="Symbol">)</a>
      <a id="3440" class="Symbol">(</a> <a id="3442" href="foundation.postcomposition-dependent-functions%25E1%25B5%2589.html#2895" class="Function">compute-htpy-eq-ap-postcomp-Πᵉ</a><a id="3472" class="Symbol">)</a>
</pre>