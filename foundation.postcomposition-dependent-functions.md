# Postcomposition of dependent functions

<pre class="Agda"><a id="51" class="Keyword">module</a> <a id="58" href="foundation.postcomposition-dependent-functions.html" class="Module">foundation.postcomposition-dependent-functions</a> <a id="105" class="Keyword">where</a>

<a id="112" class="Keyword">open</a> <a id="117" class="Keyword">import</a> <a id="124" href="foundation-core.postcomposition-dependent-functions.html" class="Module">foundation-core.postcomposition-dependent-functions</a> <a id="176" class="Keyword">public</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="233" class="Keyword">open</a> <a id="238" class="Keyword">import</a> <a id="245" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="292" class="Keyword">open</a> <a id="297" class="Keyword">import</a> <a id="304" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="339" class="Keyword">open</a> <a id="344" class="Keyword">import</a> <a id="351" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="378" class="Keyword">open</a> <a id="383" class="Keyword">import</a> <a id="390" href="foundation.whiskering-homotopies-composition.html" class="Module">foundation.whiskering-homotopies-composition</a>

<a id="436" class="Keyword">open</a> <a id="441" class="Keyword">import</a> <a id="448" href="foundation-core.commuting-squares-of-maps.html" class="Module">foundation-core.commuting-squares-of-maps</a>
<a id="490" class="Keyword">open</a> <a id="495" class="Keyword">import</a> <a id="502" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="533" class="Keyword">open</a> <a id="538" class="Keyword">import</a> <a id="545" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
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

<pre class="Agda"><a id="2724" class="Keyword">module</a> <a id="2731" href="foundation.postcomposition-dependent-functions.html#2731" class="Module">_</a>
  <a id="2735" class="Symbol">{</a><a id="2736" href="foundation.postcomposition-dependent-functions.html#2736" class="Bound">l1</a> <a id="2739" href="foundation.postcomposition-dependent-functions.html#2739" class="Bound">l2</a> <a id="2742" href="foundation.postcomposition-dependent-functions.html#2742" class="Bound">l3</a> <a id="2745" class="Symbol">:</a> <a id="2747" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2752" class="Symbol">}</a> <a id="2754" class="Symbol">{</a><a id="2755" href="foundation.postcomposition-dependent-functions.html#2755" class="Bound">A</a> <a id="2757" class="Symbol">:</a> <a id="2759" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2762" href="foundation.postcomposition-dependent-functions.html#2736" class="Bound">l1</a><a id="2764" class="Symbol">}</a> <a id="2766" class="Symbol">{</a><a id="2767" href="foundation.postcomposition-dependent-functions.html#2767" class="Bound">B</a> <a id="2769" class="Symbol">:</a> <a id="2771" href="foundation.postcomposition-dependent-functions.html#2755" class="Bound">A</a> <a id="2773" class="Symbol">→</a> <a id="2775" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2778" href="foundation.postcomposition-dependent-functions.html#2739" class="Bound">l2</a><a id="2780" class="Symbol">}</a> <a id="2782" class="Symbol">{</a><a id="2783" href="foundation.postcomposition-dependent-functions.html#2783" class="Bound">C</a> <a id="2785" class="Symbol">:</a> <a id="2787" href="foundation.postcomposition-dependent-functions.html#2755" class="Bound">A</a> <a id="2789" class="Symbol">→</a> <a id="2791" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2794" href="foundation.postcomposition-dependent-functions.html#2742" class="Bound">l3</a><a id="2796" class="Symbol">}</a>
  <a id="2800" class="Symbol">(</a><a id="2801" href="foundation.postcomposition-dependent-functions.html#2801" class="Bound">f</a> <a id="2803" class="Symbol">:</a> <a id="2805" class="Symbol">{</a><a id="2806" href="foundation.postcomposition-dependent-functions.html#2806" class="Bound">x</a> <a id="2808" class="Symbol">:</a> <a id="2810" href="foundation.postcomposition-dependent-functions.html#2755" class="Bound">A</a><a id="2811" class="Symbol">}</a> <a id="2813" class="Symbol">→</a> <a id="2815" href="foundation.postcomposition-dependent-functions.html#2767" class="Bound">B</a> <a id="2817" href="foundation.postcomposition-dependent-functions.html#2806" class="Bound">x</a> <a id="2819" class="Symbol">→</a> <a id="2821" href="foundation.postcomposition-dependent-functions.html#2783" class="Bound">C</a> <a id="2823" href="foundation.postcomposition-dependent-functions.html#2806" class="Bound">x</a><a id="2824" class="Symbol">)</a> <a id="2826" class="Symbol">{</a><a id="2827" href="foundation.postcomposition-dependent-functions.html#2827" class="Bound">g</a> <a id="2829" href="foundation.postcomposition-dependent-functions.html#2829" class="Bound">h</a> <a id="2831" class="Symbol">:</a> <a id="2833" class="Symbol">(</a><a id="2834" href="foundation.postcomposition-dependent-functions.html#2834" class="Bound">x</a> <a id="2836" class="Symbol">:</a> <a id="2838" href="foundation.postcomposition-dependent-functions.html#2755" class="Bound">A</a><a id="2839" class="Symbol">)</a> <a id="2841" class="Symbol">→</a> <a id="2843" href="foundation.postcomposition-dependent-functions.html#2767" class="Bound">B</a> <a id="2845" href="foundation.postcomposition-dependent-functions.html#2834" class="Bound">x</a><a id="2846" class="Symbol">}</a>
  <a id="2850" class="Keyword">where</a>

  <a id="2859" href="foundation.postcomposition-dependent-functions.html#2859" class="Function">compute-htpy-eq-ap-postcomp-Π</a> <a id="2889" class="Symbol">:</a>
    <a id="2895" href="foundation-core.commuting-squares-of-maps.html#1303" class="Function">coherence-square-maps</a>
      <a id="2923" class="Symbol">(</a> <a id="2925" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="2928" class="Symbol">(</a><a id="2929" href="foundation-core.postcomposition-dependent-functions.html#1365" class="Function">postcomp-Π</a> <a id="2940" href="foundation.postcomposition-dependent-functions.html#2755" class="Bound">A</a> <a id="2942" href="foundation.postcomposition-dependent-functions.html#2801" class="Bound">f</a><a id="2943" class="Symbol">)</a> <a id="2945" class="Symbol">{</a><a id="2946" class="Argument">x</a> <a id="2948" class="Symbol">=</a> <a id="2950" href="foundation.postcomposition-dependent-functions.html#2827" class="Bound">g</a><a id="2951" class="Symbol">}</a> <a id="2953" class="Symbol">{</a><a id="2954" class="Argument">y</a> <a id="2956" class="Symbol">=</a> <a id="2958" href="foundation.postcomposition-dependent-functions.html#2829" class="Bound">h</a><a id="2959" class="Symbol">})</a>
      <a id="2968" class="Symbol">(</a> <a id="2970" href="foundation.function-extensionality.html#1896" class="Function">htpy-eq</a><a id="2977" class="Symbol">)</a>
      <a id="2985" class="Symbol">(</a> <a id="2987" href="foundation.function-extensionality.html#1896" class="Function">htpy-eq</a><a id="2994" class="Symbol">)</a>
      <a id="3002" class="Symbol">(</a> <a id="3004" href="foundation.postcomposition-dependent-functions.html#2801" class="Bound">f</a> <a id="3006" href="foundation.whiskering-homotopies-composition.html#2364" class="Function Operator">·l_</a><a id="3009" class="Symbol">)</a>
  <a id="3013" href="foundation.postcomposition-dependent-functions.html#2859" class="Function">compute-htpy-eq-ap-postcomp-Π</a> <a id="3043" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="3048" class="Symbol">=</a> <a id="3050" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

  <a id="3058" href="foundation.postcomposition-dependent-functions.html#3058" class="Function">compute-eq-htpy-ap-postcomp-Π</a> <a id="3088" class="Symbol">:</a>
    <a id="3094" href="foundation-core.commuting-squares-of-maps.html#1303" class="Function">coherence-square-maps</a>
      <a id="3122" class="Symbol">(</a> <a id="3124" href="foundation.postcomposition-dependent-functions.html#2801" class="Bound">f</a> <a id="3126" href="foundation.whiskering-homotopies-composition.html#2364" class="Function Operator">·l_</a><a id="3129" class="Symbol">)</a>
      <a id="3137" class="Symbol">(</a> <a id="3139" href="foundation.function-extensionality.html#3905" class="Postulate">eq-htpy</a><a id="3146" class="Symbol">)</a>
      <a id="3154" class="Symbol">(</a> <a id="3156" href="foundation.function-extensionality.html#3905" class="Postulate">eq-htpy</a><a id="3163" class="Symbol">)</a>
      <a id="3171" class="Symbol">(</a> <a id="3173" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="3176" class="Symbol">(</a><a id="3177" href="foundation-core.postcomposition-dependent-functions.html#1365" class="Function">postcomp-Π</a> <a id="3188" href="foundation.postcomposition-dependent-functions.html#2755" class="Bound">A</a> <a id="3190" href="foundation.postcomposition-dependent-functions.html#2801" class="Bound">f</a><a id="3191" class="Symbol">))</a>
  <a id="3196" href="foundation.postcomposition-dependent-functions.html#3058" class="Function">compute-eq-htpy-ap-postcomp-Π</a> <a id="3226" class="Symbol">=</a>
    <a id="3232" href="foundation-core.commuting-squares-of-maps.html#7647" class="Function">vertical-inv-equiv-coherence-square-maps</a>
      <a id="3279" class="Symbol">(</a> <a id="3281" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="3284" class="Symbol">(</a><a id="3285" href="foundation-core.postcomposition-dependent-functions.html#1365" class="Function">postcomp-Π</a> <a id="3296" href="foundation.postcomposition-dependent-functions.html#2755" class="Bound">A</a> <a id="3298" href="foundation.postcomposition-dependent-functions.html#2801" class="Bound">f</a><a id="3299" class="Symbol">))</a>
      <a id="3308" class="Symbol">(</a> <a id="3310" href="foundation.function-extensionality.html#4394" class="Function">equiv-funext</a><a id="3322" class="Symbol">)</a>
      <a id="3330" class="Symbol">(</a> <a id="3332" href="foundation.function-extensionality.html#4394" class="Function">equiv-funext</a><a id="3344" class="Symbol">)</a>
      <a id="3352" class="Symbol">(</a> <a id="3354" href="foundation.postcomposition-dependent-functions.html#2801" class="Bound">f</a> <a id="3356" href="foundation.whiskering-homotopies-composition.html#2364" class="Function Operator">·l_</a><a id="3359" class="Symbol">)</a>
      <a id="3367" class="Symbol">(</a> <a id="3369" href="foundation.postcomposition-dependent-functions.html#2859" class="Function">compute-htpy-eq-ap-postcomp-Π</a><a id="3398" class="Symbol">)</a>
</pre>