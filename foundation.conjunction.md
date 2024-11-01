# Conjunction

<pre class="Agda"><a id="24" class="Keyword">module</a> <a id="31" href="foundation.conjunction.html" class="Module">foundation.conjunction</a> <a id="54" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="110" class="Keyword">open</a> <a id="115" class="Keyword">import</a> <a id="122" href="foundation.decidable-types.html" class="Module">foundation.decidable-types</a>
<a id="149" class="Keyword">open</a> <a id="154" class="Keyword">import</a> <a id="161" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="193" class="Keyword">open</a> <a id="198" class="Keyword">import</a> <a id="205" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="237" class="Keyword">open</a> <a id="242" class="Keyword">import</a> <a id="249" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="286" class="Keyword">open</a> <a id="291" class="Keyword">import</a> <a id="298" href="foundation.universal-property-cartesian-product-types.html" class="Module">foundation.universal-property-cartesian-product-types</a>
<a id="352" class="Keyword">open</a> <a id="357" class="Keyword">import</a> <a id="364" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="392" class="Keyword">open</a> <a id="397" class="Keyword">import</a> <a id="404" href="foundation-core.cartesian-product-types.html" class="Module">foundation-core.cartesian-product-types</a>
<a id="444" class="Keyword">open</a> <a id="449" class="Keyword">import</a> <a id="456" href="foundation-core.decidable-propositions.html" class="Module">foundation-core.decidable-propositions</a>
<a id="495" class="Keyword">open</a> <a id="500" class="Keyword">import</a> <a id="507" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="536" class="Keyword">open</a> <a id="541" class="Keyword">import</a> <a id="548" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="579" class="Keyword">open</a> <a id="584" class="Keyword">import</a> <a id="591" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

The
{{#concept "conjunction" Disambiguation="of propositions" WDID=Q191081 WD="logical conjunction" Agda=conjunction-Prop}}
`P ∧ Q` of two [propositions](foundation-core.propositions.md) `P` and `Q` is
the proposition that both `P` and `Q` hold and is thus defined by the
[cartesian product](foundation-core.cartesian-product-types.md) of their
underlying types

```text
  P ∧ Q := P × Q
```

The conjunction of two propositions satisfies the universal property of the
[meet](order-theory.greatest-lower-bounds-large-posets.md) in the
[locale of propositions](foundation.large-locale-of-propositions.md). This means
that any span of propositions over `P` and `Q` factor (uniquely) through the
conjunction

```text
           R
        /  ∶  \
      /    ∶    \
    ∨      ∨      ∨
  P <--- P ∧ Q ---> Q.
```

In other words, we have a
[logical equivalence](foundation.logical-equivalences.md)

```text
  (R → P) ∧ (R → Q) ↔ (R → P ∧ Q)
```

for every proposition `R`. In fact, `R` can be any type.

The
{{#concept "recursion principle" Disambiguation"of the conjunction of propositions" Agda=elimination-principle-conjunction-Prop}}
of the conjunction of propositions states that to define a function `P ∧ Q → R`
into a proposition `R`, or indeed any type, is equivalent to defining a function
`P → Q → R`.

## Definitions

### The conjunction

<pre class="Agda"><a id="1999" class="Keyword">module</a> <a id="2006" href="foundation.conjunction.html#2006" class="Module">_</a>
  <a id="2010" class="Symbol">{</a><a id="2011" href="foundation.conjunction.html#2011" class="Bound">l1</a> <a id="2014" href="foundation.conjunction.html#2014" class="Bound">l2</a> <a id="2017" class="Symbol">:</a> <a id="2019" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2024" class="Symbol">}</a> <a id="2026" class="Symbol">(</a><a id="2027" href="foundation.conjunction.html#2027" class="Bound">P</a> <a id="2029" class="Symbol">:</a> <a id="2031" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2036" href="foundation.conjunction.html#2011" class="Bound">l1</a><a id="2038" class="Symbol">)</a> <a id="2040" class="Symbol">(</a><a id="2041" href="foundation.conjunction.html#2041" class="Bound">Q</a> <a id="2043" class="Symbol">:</a> <a id="2045" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2050" href="foundation.conjunction.html#2014" class="Bound">l2</a><a id="2052" class="Symbol">)</a>
  <a id="2056" class="Keyword">where</a>

  <a id="2065" href="foundation.conjunction.html#2065" class="Function">conjunction-Prop</a> <a id="2082" class="Symbol">:</a> <a id="2084" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2089" class="Symbol">(</a><a id="2090" href="foundation.conjunction.html#2011" class="Bound">l1</a> <a id="2093" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2095" href="foundation.conjunction.html#2014" class="Bound">l2</a><a id="2097" class="Symbol">)</a>
  <a id="2101" href="foundation.conjunction.html#2065" class="Function">conjunction-Prop</a> <a id="2118" class="Symbol">=</a> <a id="2120" href="foundation-core.propositions.html#5309" class="Function">product-Prop</a> <a id="2133" href="foundation.conjunction.html#2027" class="Bound">P</a> <a id="2135" href="foundation.conjunction.html#2041" class="Bound">Q</a>

  <a id="2140" href="foundation.conjunction.html#2140" class="Function">type-conjunction-Prop</a> <a id="2162" class="Symbol">:</a> <a id="2164" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2167" class="Symbol">(</a><a id="2168" href="foundation.conjunction.html#2011" class="Bound">l1</a> <a id="2171" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2173" href="foundation.conjunction.html#2014" class="Bound">l2</a><a id="2175" class="Symbol">)</a>
  <a id="2179" href="foundation.conjunction.html#2140" class="Function">type-conjunction-Prop</a> <a id="2201" class="Symbol">=</a> <a id="2203" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2213" href="foundation.conjunction.html#2065" class="Function">conjunction-Prop</a>

  <a id="2233" href="foundation.conjunction.html#2233" class="Function">is-prop-conjunction-Prop</a> <a id="2258" class="Symbol">:</a>
    <a id="2264" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2272" href="foundation.conjunction.html#2140" class="Function">type-conjunction-Prop</a>
  <a id="2296" href="foundation.conjunction.html#2233" class="Function">is-prop-conjunction-Prop</a> <a id="2321" class="Symbol">=</a> <a id="2323" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="2341" href="foundation.conjunction.html#2065" class="Function">conjunction-Prop</a>

  <a id="2361" class="Keyword">infixr</a> <a id="2368" class="Number">15</a> <a id="2371" href="foundation.conjunction.html#2377" class="Function Operator">_∧_</a>
  <a id="2377" href="foundation.conjunction.html#2377" class="Function Operator">_∧_</a> <a id="2381" class="Symbol">:</a> <a id="2383" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2388" class="Symbol">(</a><a id="2389" href="foundation.conjunction.html#2011" class="Bound">l1</a> <a id="2392" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2394" href="foundation.conjunction.html#2014" class="Bound">l2</a><a id="2396" class="Symbol">)</a>
  <a id="2400" href="foundation.conjunction.html#2377" class="Function Operator">_∧_</a> <a id="2404" class="Symbol">=</a> <a id="2406" href="foundation.conjunction.html#2065" class="Function">conjunction-Prop</a>
</pre>
**Note**: The symbol used for the conjunction `_∧_` is the
[logical and](https://codepoints.net/U+2227) `∧` (agda-input: `\wedge` or
`\and`).

### The conjunction of decidable propositions

<pre class="Agda"><a id="2626" class="Keyword">module</a> <a id="2633" href="foundation.conjunction.html#2633" class="Module">_</a>
  <a id="2637" class="Symbol">{</a><a id="2638" href="foundation.conjunction.html#2638" class="Bound">l1</a> <a id="2641" href="foundation.conjunction.html#2641" class="Bound">l2</a> <a id="2644" class="Symbol">:</a> <a id="2646" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2651" class="Symbol">}</a> <a id="2653" class="Symbol">(</a><a id="2654" href="foundation.conjunction.html#2654" class="Bound">P</a> <a id="2656" class="Symbol">:</a> <a id="2658" href="foundation-core.decidable-propositions.html#1922" class="Function">Decidable-Prop</a> <a id="2673" href="foundation.conjunction.html#2638" class="Bound">l1</a><a id="2675" class="Symbol">)</a> <a id="2677" class="Symbol">(</a><a id="2678" href="foundation.conjunction.html#2678" class="Bound">Q</a> <a id="2680" class="Symbol">:</a> <a id="2682" href="foundation-core.decidable-propositions.html#1922" class="Function">Decidable-Prop</a> <a id="2697" href="foundation.conjunction.html#2641" class="Bound">l2</a><a id="2699" class="Symbol">)</a>
  <a id="2703" class="Keyword">where</a>

  <a id="2712" href="foundation.conjunction.html#2712" class="Function">is-decidable-conjunction-Decidable-Prop</a> <a id="2752" class="Symbol">:</a>
    <a id="2758" href="foundation.decidable-types.html#1523" class="Function">is-decidable</a>
      <a id="2777" class="Symbol">(</a> <a id="2779" href="foundation.conjunction.html#2140" class="Function">type-conjunction-Prop</a> <a id="2801" class="Symbol">(</a><a id="2802" href="foundation-core.decidable-propositions.html#2080" class="Function">prop-Decidable-Prop</a> <a id="2822" href="foundation.conjunction.html#2654" class="Bound">P</a><a id="2823" class="Symbol">)</a> <a id="2825" class="Symbol">(</a><a id="2826" href="foundation-core.decidable-propositions.html#2080" class="Function">prop-Decidable-Prop</a> <a id="2846" href="foundation.conjunction.html#2678" class="Bound">Q</a><a id="2847" class="Symbol">))</a>
  <a id="2852" href="foundation.conjunction.html#2712" class="Function">is-decidable-conjunction-Decidable-Prop</a> <a id="2892" class="Symbol">=</a>
    <a id="2898" href="foundation.decidable-types.html#3054" class="Function">is-decidable-product</a>
      <a id="2925" class="Symbol">(</a> <a id="2927" href="foundation-core.decidable-propositions.html#2384" class="Function">is-decidable-Decidable-Prop</a> <a id="2955" href="foundation.conjunction.html#2654" class="Bound">P</a><a id="2956" class="Symbol">)</a>
      <a id="2964" class="Symbol">(</a> <a id="2966" href="foundation-core.decidable-propositions.html#2384" class="Function">is-decidable-Decidable-Prop</a> <a id="2994" href="foundation.conjunction.html#2678" class="Bound">Q</a><a id="2995" class="Symbol">)</a>

  <a id="3000" href="foundation.conjunction.html#3000" class="Function">conjunction-Decidable-Prop</a> <a id="3027" class="Symbol">:</a> <a id="3029" href="foundation-core.decidable-propositions.html#1922" class="Function">Decidable-Prop</a> <a id="3044" class="Symbol">(</a><a id="3045" href="foundation.conjunction.html#2638" class="Bound">l1</a> <a id="3048" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3050" href="foundation.conjunction.html#2641" class="Bound">l2</a><a id="3052" class="Symbol">)</a>
  <a id="3056" href="foundation.conjunction.html#3000" class="Function">conjunction-Decidable-Prop</a> <a id="3083" class="Symbol">=</a>
    <a id="3089" class="Symbol">(</a> <a id="3091" href="foundation.conjunction.html#2140" class="Function">type-conjunction-Prop</a> <a id="3113" class="Symbol">(</a><a id="3114" href="foundation-core.decidable-propositions.html#2080" class="Function">prop-Decidable-Prop</a> <a id="3134" href="foundation.conjunction.html#2654" class="Bound">P</a><a id="3135" class="Symbol">)</a> <a id="3137" class="Symbol">(</a><a id="3138" href="foundation-core.decidable-propositions.html#2080" class="Function">prop-Decidable-Prop</a> <a id="3158" href="foundation.conjunction.html#2678" class="Bound">Q</a><a id="3159" class="Symbol">)</a> <a id="3161" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="3169" href="foundation.conjunction.html#2233" class="Function">is-prop-conjunction-Prop</a> <a id="3194" class="Symbol">(</a><a id="3195" href="foundation-core.decidable-propositions.html#2080" class="Function">prop-Decidable-Prop</a> <a id="3215" href="foundation.conjunction.html#2654" class="Bound">P</a><a id="3216" class="Symbol">)</a> <a id="3218" class="Symbol">(</a><a id="3219" href="foundation-core.decidable-propositions.html#2080" class="Function">prop-Decidable-Prop</a> <a id="3239" href="foundation.conjunction.html#2678" class="Bound">Q</a><a id="3240" class="Symbol">)</a> <a id="3242" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="3250" href="foundation.conjunction.html#2712" class="Function">is-decidable-conjunction-Decidable-Prop</a><a id="3289" class="Symbol">)</a>
</pre>
### The introduction rule and projections for the conjunction of propositions

While we define the introduction rule and projections for the conjunction below,
we advice users to use the standard pairing and projection functions for the
cartesian product types: `pair`, `pr1` and `pr2`.

<pre class="Agda"><a id="3592" class="Keyword">module</a> <a id="3599" href="foundation.conjunction.html#3599" class="Module">_</a>
  <a id="3603" class="Symbol">{</a><a id="3604" href="foundation.conjunction.html#3604" class="Bound">l1</a> <a id="3607" href="foundation.conjunction.html#3607" class="Bound">l2</a> <a id="3610" class="Symbol">:</a> <a id="3612" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3617" class="Symbol">}</a> <a id="3619" class="Symbol">(</a><a id="3620" href="foundation.conjunction.html#3620" class="Bound">P</a> <a id="3622" class="Symbol">:</a> <a id="3624" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="3629" href="foundation.conjunction.html#3604" class="Bound">l1</a><a id="3631" class="Symbol">)</a> <a id="3633" class="Symbol">(</a><a id="3634" href="foundation.conjunction.html#3634" class="Bound">Q</a> <a id="3636" class="Symbol">:</a> <a id="3638" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="3643" href="foundation.conjunction.html#3607" class="Bound">l2</a><a id="3645" class="Symbol">)</a>
  <a id="3649" class="Keyword">where</a>

  <a id="3658" href="foundation.conjunction.html#3658" class="Function">intro-conjunction-Prop</a> <a id="3681" class="Symbol">:</a> <a id="3683" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="3693" href="foundation.conjunction.html#3620" class="Bound">P</a> <a id="3695" class="Symbol">→</a> <a id="3697" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="3707" href="foundation.conjunction.html#3634" class="Bound">Q</a> <a id="3709" class="Symbol">→</a> <a id="3711" href="foundation.conjunction.html#2140" class="Function">type-conjunction-Prop</a> <a id="3733" href="foundation.conjunction.html#3620" class="Bound">P</a> <a id="3735" href="foundation.conjunction.html#3634" class="Bound">Q</a>
  <a id="3739" href="foundation.conjunction.html#3658" class="Function">intro-conjunction-Prop</a> <a id="3762" class="Symbol">=</a> <a id="3764" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a>

  <a id="3772" href="foundation.conjunction.html#3772" class="Function">pr1-conjunction-Prop</a> <a id="3793" class="Symbol">:</a> <a id="3795" href="foundation.conjunction.html#2140" class="Function">type-conjunction-Prop</a> <a id="3817" href="foundation.conjunction.html#3620" class="Bound">P</a> <a id="3819" href="foundation.conjunction.html#3634" class="Bound">Q</a> <a id="3821" class="Symbol">→</a> <a id="3823" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="3833" href="foundation.conjunction.html#3620" class="Bound">P</a>
  <a id="3837" href="foundation.conjunction.html#3772" class="Function">pr1-conjunction-Prop</a> <a id="3858" class="Symbol">=</a> <a id="3860" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a>

  <a id="3867" href="foundation.conjunction.html#3867" class="Function">pr2-conjunction-Prop</a> <a id="3888" class="Symbol">:</a> <a id="3890" href="foundation.conjunction.html#2140" class="Function">type-conjunction-Prop</a> <a id="3912" href="foundation.conjunction.html#3620" class="Bound">P</a> <a id="3914" href="foundation.conjunction.html#3634" class="Bound">Q</a> <a id="3916" class="Symbol">→</a> <a id="3918" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="3928" href="foundation.conjunction.html#3634" class="Bound">Q</a>
  <a id="3932" href="foundation.conjunction.html#3867" class="Function">pr2-conjunction-Prop</a> <a id="3953" class="Symbol">=</a> <a id="3955" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a>
</pre>
### The elimination principle of the conjunction

<pre class="Agda"><a id="4022" class="Keyword">module</a> <a id="4029" href="foundation.conjunction.html#4029" class="Module">_</a>
  <a id="4033" class="Symbol">{</a><a id="4034" href="foundation.conjunction.html#4034" class="Bound">l1</a> <a id="4037" href="foundation.conjunction.html#4037" class="Bound">l2</a> <a id="4040" class="Symbol">:</a> <a id="4042" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4047" class="Symbol">}</a> <a id="4049" class="Symbol">(</a><a id="4050" href="foundation.conjunction.html#4050" class="Bound">P</a> <a id="4052" class="Symbol">:</a> <a id="4054" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="4059" href="foundation.conjunction.html#4034" class="Bound">l1</a><a id="4061" class="Symbol">)</a> <a id="4063" class="Symbol">(</a><a id="4064" href="foundation.conjunction.html#4064" class="Bound">Q</a> <a id="4066" class="Symbol">:</a> <a id="4068" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="4073" href="foundation.conjunction.html#4037" class="Bound">l2</a><a id="4075" class="Symbol">)</a>
  <a id="4079" class="Keyword">where</a>

  <a id="4088" href="foundation.conjunction.html#4088" class="Function">ev-conjunction-Prop</a> <a id="4108" class="Symbol">:</a>
    <a id="4114" class="Symbol">{</a><a id="4115" href="foundation.conjunction.html#4115" class="Bound">l</a> <a id="4117" class="Symbol">:</a> <a id="4119" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4124" class="Symbol">}</a> <a id="4126" class="Symbol">(</a><a id="4127" href="foundation.conjunction.html#4127" class="Bound">R</a> <a id="4129" class="Symbol">:</a> <a id="4131" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="4136" href="foundation.conjunction.html#4115" class="Bound">l</a><a id="4137" class="Symbol">)</a> <a id="4139" class="Symbol">→</a> <a id="4141" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="4151" class="Symbol">(((</a><a id="4154" href="foundation.conjunction.html#4050" class="Bound">P</a> <a id="4156" href="foundation.conjunction.html#2377" class="Function Operator">∧</a> <a id="4158" href="foundation.conjunction.html#4064" class="Bound">Q</a><a id="4159" class="Symbol">)</a> <a id="4161" href="foundation-core.propositions.html#7965" class="Function Operator">⇒</a> <a id="4163" href="foundation.conjunction.html#4127" class="Bound">R</a><a id="4164" class="Symbol">)</a> <a id="4166" href="foundation-core.propositions.html#7965" class="Function Operator">⇒</a> <a id="4168" href="foundation.conjunction.html#4050" class="Bound">P</a> <a id="4170" href="foundation-core.propositions.html#7965" class="Function Operator">⇒</a> <a id="4172" href="foundation.conjunction.html#4064" class="Bound">Q</a> <a id="4174" href="foundation-core.propositions.html#7965" class="Function Operator">⇒</a> <a id="4176" href="foundation.conjunction.html#4127" class="Bound">R</a><a id="4177" class="Symbol">)</a>
  <a id="4181" href="foundation.conjunction.html#4088" class="Function">ev-conjunction-Prop</a> <a id="4201" href="foundation.conjunction.html#4201" class="Bound">R</a> <a id="4203" class="Symbol">=</a> <a id="4205" href="foundation.dependent-pair-types.html#1278" class="Function">ev-pair</a>

  <a id="4216" href="foundation.conjunction.html#4216" class="Function">elimination-principle-conjunction-Prop</a> <a id="4255" class="Symbol">:</a> <a id="4257" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="4263" href="foundation.conjunction.html#4216" class="Function">elimination-principle-conjunction-Prop</a> <a id="4302" class="Symbol">=</a>
    <a id="4308" class="Symbol">{</a><a id="4309" href="foundation.conjunction.html#4309" class="Bound">l</a> <a id="4311" class="Symbol">:</a> <a id="4313" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4318" class="Symbol">}</a> <a id="4320" class="Symbol">(</a><a id="4321" href="foundation.conjunction.html#4321" class="Bound">R</a> <a id="4323" class="Symbol">:</a> <a id="4325" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="4330" href="foundation.conjunction.html#4309" class="Bound">l</a><a id="4331" class="Symbol">)</a> <a id="4333" class="Symbol">→</a> <a id="4335" href="foundation.logical-equivalences.html#1533" class="Function">has-converse</a> <a id="4348" class="Symbol">(</a><a id="4349" href="foundation.conjunction.html#4088" class="Function">ev-conjunction-Prop</a> <a id="4369" href="foundation.conjunction.html#4321" class="Bound">R</a><a id="4370" class="Symbol">)</a>
</pre>
## Properties

### The conjunction satisfies the recursion principle of the conjunction

<pre class="Agda"><a id="4474" class="Keyword">module</a> <a id="4481" href="foundation.conjunction.html#4481" class="Module">_</a>
  <a id="4485" class="Symbol">{</a><a id="4486" href="foundation.conjunction.html#4486" class="Bound">l1</a> <a id="4489" href="foundation.conjunction.html#4489" class="Bound">l2</a> <a id="4492" class="Symbol">:</a> <a id="4494" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4499" class="Symbol">}</a> <a id="4501" class="Symbol">(</a><a id="4502" href="foundation.conjunction.html#4502" class="Bound">P</a> <a id="4504" class="Symbol">:</a> <a id="4506" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="4511" href="foundation.conjunction.html#4486" class="Bound">l1</a><a id="4513" class="Symbol">)</a> <a id="4515" class="Symbol">(</a><a id="4516" href="foundation.conjunction.html#4516" class="Bound">Q</a> <a id="4518" class="Symbol">:</a> <a id="4520" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="4525" href="foundation.conjunction.html#4489" class="Bound">l2</a><a id="4527" class="Symbol">)</a>
  <a id="4531" class="Keyword">where</a>

  <a id="4540" href="foundation.conjunction.html#4540" class="Function">elim-conjunction-Prop</a> <a id="4562" class="Symbol">:</a> <a id="4564" href="foundation.conjunction.html#4216" class="Function">elimination-principle-conjunction-Prop</a> <a id="4603" href="foundation.conjunction.html#4502" class="Bound">P</a> <a id="4605" href="foundation.conjunction.html#4516" class="Bound">Q</a>
  <a id="4609" href="foundation.conjunction.html#4540" class="Function">elim-conjunction-Prop</a> <a id="4631" href="foundation.conjunction.html#4631" class="Bound">R</a> <a id="4633" href="foundation.conjunction.html#4633" class="Bound">f</a> <a id="4635" class="Symbol">(</a><a id="4636" href="foundation.conjunction.html#4636" class="Bound">p</a> <a id="4638" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="4640" href="foundation.conjunction.html#4640" class="Bound">q</a><a id="4641" class="Symbol">)</a> <a id="4643" class="Symbol">=</a> <a id="4645" href="foundation.conjunction.html#4633" class="Bound">f</a> <a id="4647" href="foundation.conjunction.html#4636" class="Bound">p</a> <a id="4649" href="foundation.conjunction.html#4640" class="Bound">q</a>
</pre>
### The conjunction is the meet in the locale of propositions

<pre class="Agda"><a id="4727" class="Keyword">module</a> <a id="4734" href="foundation.conjunction.html#4734" class="Module">_</a>
  <a id="4738" class="Symbol">{</a><a id="4739" href="foundation.conjunction.html#4739" class="Bound">l1</a> <a id="4742" href="foundation.conjunction.html#4742" class="Bound">l2</a> <a id="4745" href="foundation.conjunction.html#4745" class="Bound">l3</a> <a id="4748" class="Symbol">:</a> <a id="4750" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4755" class="Symbol">}</a> <a id="4757" class="Symbol">(</a><a id="4758" href="foundation.conjunction.html#4758" class="Bound">P</a> <a id="4760" class="Symbol">:</a> <a id="4762" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="4767" href="foundation.conjunction.html#4739" class="Bound">l1</a><a id="4769" class="Symbol">)</a> <a id="4771" class="Symbol">(</a><a id="4772" href="foundation.conjunction.html#4772" class="Bound">Q</a> <a id="4774" class="Symbol">:</a> <a id="4776" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="4781" href="foundation.conjunction.html#4742" class="Bound">l2</a><a id="4783" class="Symbol">)</a> <a id="4785" class="Symbol">(</a><a id="4786" href="foundation.conjunction.html#4786" class="Bound">C</a> <a id="4788" class="Symbol">:</a> <a id="4790" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4793" href="foundation.conjunction.html#4745" class="Bound">l3</a><a id="4795" class="Symbol">)</a>
  <a id="4799" class="Keyword">where</a>

  <a id="4808" href="foundation.conjunction.html#4808" class="Function">map-distributive-conjunction-Prop</a> <a id="4842" class="Symbol">:</a>
    <a id="4848" href="foundation.conjunction.html#2140" class="Function">type-conjunction-Prop</a> <a id="4870" class="Symbol">(</a><a id="4871" href="foundation-core.propositions.html#7365" class="Function">function-Prop</a> <a id="4885" href="foundation.conjunction.html#4786" class="Bound">C</a> <a id="4887" href="foundation.conjunction.html#4758" class="Bound">P</a><a id="4888" class="Symbol">)</a> <a id="4890" class="Symbol">(</a><a id="4891" href="foundation-core.propositions.html#7365" class="Function">function-Prop</a> <a id="4905" href="foundation.conjunction.html#4786" class="Bound">C</a> <a id="4907" href="foundation.conjunction.html#4772" class="Bound">Q</a><a id="4908" class="Symbol">)</a> <a id="4910" class="Symbol">→</a>
    <a id="4916" href="foundation.conjunction.html#4786" class="Bound">C</a> <a id="4918" class="Symbol">→</a> <a id="4920" href="foundation.conjunction.html#2140" class="Function">type-conjunction-Prop</a> <a id="4942" href="foundation.conjunction.html#4758" class="Bound">P</a> <a id="4944" href="foundation.conjunction.html#4772" class="Bound">Q</a>
  <a id="4948" href="foundation.conjunction.html#4808" class="Function">map-distributive-conjunction-Prop</a> <a id="4982" class="Symbol">(</a><a id="4983" href="foundation.conjunction.html#4983" class="Bound">f</a> <a id="4985" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="4987" href="foundation.conjunction.html#4987" class="Bound">g</a><a id="4988" class="Symbol">)</a> <a id="4990" href="foundation.conjunction.html#4990" class="Bound">y</a> <a id="4992" class="Symbol">=</a> <a id="4994" class="Symbol">(</a><a id="4995" href="foundation.conjunction.html#4983" class="Bound">f</a> <a id="4997" href="foundation.conjunction.html#4990" class="Bound">y</a> <a id="4999" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="5001" href="foundation.conjunction.html#4987" class="Bound">g</a> <a id="5003" href="foundation.conjunction.html#4990" class="Bound">y</a><a id="5004" class="Symbol">)</a>

  <a id="5009" href="foundation.conjunction.html#5009" class="Function">map-inv-distributive-conjunction-Prop</a> <a id="5047" class="Symbol">:</a>
    <a id="5053" class="Symbol">(</a><a id="5054" href="foundation.conjunction.html#4786" class="Bound">C</a> <a id="5056" class="Symbol">→</a> <a id="5058" href="foundation.conjunction.html#2140" class="Function">type-conjunction-Prop</a> <a id="5080" href="foundation.conjunction.html#4758" class="Bound">P</a> <a id="5082" href="foundation.conjunction.html#4772" class="Bound">Q</a><a id="5083" class="Symbol">)</a> <a id="5085" class="Symbol">→</a>
    <a id="5091" href="foundation.conjunction.html#2140" class="Function">type-conjunction-Prop</a> <a id="5113" class="Symbol">(</a><a id="5114" href="foundation-core.propositions.html#7365" class="Function">function-Prop</a> <a id="5128" href="foundation.conjunction.html#4786" class="Bound">C</a> <a id="5130" href="foundation.conjunction.html#4758" class="Bound">P</a><a id="5131" class="Symbol">)</a> <a id="5133" class="Symbol">(</a><a id="5134" href="foundation-core.propositions.html#7365" class="Function">function-Prop</a> <a id="5148" href="foundation.conjunction.html#4786" class="Bound">C</a> <a id="5150" href="foundation.conjunction.html#4772" class="Bound">Q</a><a id="5151" class="Symbol">)</a>
  <a id="5155" href="foundation.conjunction.html#5009" class="Function">map-inv-distributive-conjunction-Prop</a> <a id="5193" href="foundation.conjunction.html#5193" class="Bound">f</a> <a id="5195" class="Symbol">=</a> <a id="5197" class="Symbol">(</a><a id="5198" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5202" href="foundation-core.function-types.html#455" class="Function Operator">∘</a> <a id="5204" href="foundation.conjunction.html#5193" class="Bound">f</a> <a id="5206" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="5208" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5212" href="foundation-core.function-types.html#455" class="Function Operator">∘</a> <a id="5214" href="foundation.conjunction.html#5193" class="Bound">f</a><a id="5215" class="Symbol">)</a>

  <a id="5220" href="foundation.conjunction.html#5220" class="Function">is-equiv-map-distributive-conjunction-Prop</a> <a id="5263" class="Symbol">:</a>
    <a id="5269" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="5278" href="foundation.conjunction.html#4808" class="Function">map-distributive-conjunction-Prop</a>
  <a id="5314" href="foundation.conjunction.html#5220" class="Function">is-equiv-map-distributive-conjunction-Prop</a> <a id="5357" class="Symbol">=</a>
    <a id="5363" href="foundation.logical-equivalences.html#4962" class="Function">is-equiv-has-converse</a>
      <a id="5391" class="Symbol">(</a> <a id="5393" href="foundation.conjunction.html#2065" class="Function">conjunction-Prop</a> <a id="5410" class="Symbol">(</a><a id="5411" href="foundation-core.propositions.html#7365" class="Function">function-Prop</a> <a id="5425" href="foundation.conjunction.html#4786" class="Bound">C</a> <a id="5427" href="foundation.conjunction.html#4758" class="Bound">P</a><a id="5428" class="Symbol">)</a> <a id="5430" class="Symbol">(</a><a id="5431" href="foundation-core.propositions.html#7365" class="Function">function-Prop</a> <a id="5445" href="foundation.conjunction.html#4786" class="Bound">C</a> <a id="5447" href="foundation.conjunction.html#4772" class="Bound">Q</a><a id="5448" class="Symbol">))</a>
      <a id="5457" class="Symbol">(</a> <a id="5459" href="foundation-core.propositions.html#7365" class="Function">function-Prop</a> <a id="5473" href="foundation.conjunction.html#4786" class="Bound">C</a> <a id="5475" class="Symbol">(</a><a id="5476" href="foundation.conjunction.html#2065" class="Function">conjunction-Prop</a> <a id="5493" href="foundation.conjunction.html#4758" class="Bound">P</a> <a id="5495" href="foundation.conjunction.html#4772" class="Bound">Q</a><a id="5496" class="Symbol">))</a>
      <a id="5505" class="Symbol">(</a> <a id="5507" href="foundation.conjunction.html#5009" class="Function">map-inv-distributive-conjunction-Prop</a><a id="5544" class="Symbol">)</a>

  <a id="5549" href="foundation.conjunction.html#5549" class="Function">distributive-conjunction-Prop</a> <a id="5579" class="Symbol">:</a>
    <a id="5585" href="foundation.conjunction.html#2140" class="Function">type-conjunction-Prop</a> <a id="5607" class="Symbol">(</a><a id="5608" href="foundation-core.propositions.html#7365" class="Function">function-Prop</a> <a id="5622" href="foundation.conjunction.html#4786" class="Bound">C</a> <a id="5624" href="foundation.conjunction.html#4758" class="Bound">P</a><a id="5625" class="Symbol">)</a> <a id="5627" class="Symbol">(</a><a id="5628" href="foundation-core.propositions.html#7365" class="Function">function-Prop</a> <a id="5642" href="foundation.conjunction.html#4786" class="Bound">C</a> <a id="5644" href="foundation.conjunction.html#4772" class="Bound">Q</a><a id="5645" class="Symbol">)</a> <a id="5647" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="5653" class="Symbol">(</a><a id="5654" href="foundation.conjunction.html#4786" class="Bound">C</a> <a id="5656" class="Symbol">→</a> <a id="5658" href="foundation.conjunction.html#2140" class="Function">type-conjunction-Prop</a> <a id="5680" href="foundation.conjunction.html#4758" class="Bound">P</a> <a id="5682" href="foundation.conjunction.html#4772" class="Bound">Q</a><a id="5683" class="Symbol">)</a>
  <a id="5687" href="foundation.conjunction.html#5549" class="Function">distributive-conjunction-Prop</a> <a id="5717" class="Symbol">=</a>
    <a id="5723" class="Symbol">(</a> <a id="5725" href="foundation.conjunction.html#4808" class="Function">map-distributive-conjunction-Prop</a> <a id="5759" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="5767" href="foundation.conjunction.html#5220" class="Function">is-equiv-map-distributive-conjunction-Prop</a><a id="5809" class="Symbol">)</a>

<a id="5812" class="Keyword">module</a> <a id="5819" href="foundation.conjunction.html#5819" class="Module">_</a>
  <a id="5823" class="Symbol">{</a><a id="5824" href="foundation.conjunction.html#5824" class="Bound">l1</a> <a id="5827" href="foundation.conjunction.html#5827" class="Bound">l2</a> <a id="5830" href="foundation.conjunction.html#5830" class="Bound">l3</a> <a id="5833" class="Symbol">:</a> <a id="5835" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5840" class="Symbol">}</a> <a id="5842" class="Symbol">(</a><a id="5843" href="foundation.conjunction.html#5843" class="Bound">P</a> <a id="5845" class="Symbol">:</a> <a id="5847" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="5852" href="foundation.conjunction.html#5824" class="Bound">l1</a><a id="5854" class="Symbol">)</a> <a id="5856" class="Symbol">(</a><a id="5857" href="foundation.conjunction.html#5857" class="Bound">Q</a> <a id="5859" class="Symbol">:</a> <a id="5861" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="5866" href="foundation.conjunction.html#5827" class="Bound">l2</a><a id="5868" class="Symbol">)</a> <a id="5870" class="Symbol">(</a><a id="5871" href="foundation.conjunction.html#5871" class="Bound">R</a> <a id="5873" class="Symbol">:</a> <a id="5875" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="5880" href="foundation.conjunction.html#5830" class="Bound">l3</a><a id="5882" class="Symbol">)</a>
  <a id="5886" class="Keyword">where</a>

  <a id="5895" href="foundation.conjunction.html#5895" class="Function">is-greatest-binary-lower-bound-conjunction-Prop</a> <a id="5943" class="Symbol">:</a>
    <a id="5949" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="5959" class="Symbol">(((</a><a id="5962" href="foundation.conjunction.html#5871" class="Bound">R</a> <a id="5964" href="foundation-core.propositions.html#7965" class="Function Operator">⇒</a> <a id="5966" href="foundation.conjunction.html#5843" class="Bound">P</a><a id="5967" class="Symbol">)</a> <a id="5969" href="foundation.conjunction.html#2377" class="Function Operator">∧</a> <a id="5971" class="Symbol">(</a><a id="5972" href="foundation.conjunction.html#5871" class="Bound">R</a> <a id="5974" href="foundation-core.propositions.html#7965" class="Function Operator">⇒</a> <a id="5976" href="foundation.conjunction.html#5857" class="Bound">Q</a><a id="5977" class="Symbol">))</a> <a id="5980" href="foundation.logical-equivalences.html#2857" class="Function Operator">⇔</a> <a id="5982" class="Symbol">(</a><a id="5983" href="foundation.conjunction.html#5871" class="Bound">R</a> <a id="5985" href="foundation-core.propositions.html#7965" class="Function Operator">⇒</a> <a id="5987" href="foundation.conjunction.html#5843" class="Bound">P</a> <a id="5989" href="foundation.conjunction.html#2377" class="Function Operator">∧</a> <a id="5991" href="foundation.conjunction.html#5857" class="Bound">Q</a><a id="5992" class="Symbol">))</a>
  <a id="5997" href="foundation.conjunction.html#5895" class="Function">is-greatest-binary-lower-bound-conjunction-Prop</a> <a id="6045" class="Symbol">=</a>
    <a id="6051" class="Symbol">(</a> <a id="6053" href="foundation.conjunction.html#4808" class="Function">map-distributive-conjunction-Prop</a> <a id="6087" href="foundation.conjunction.html#5843" class="Bound">P</a> <a id="6089" href="foundation.conjunction.html#5857" class="Bound">Q</a> <a id="6091" class="Symbol">(</a><a id="6092" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="6102" href="foundation.conjunction.html#5871" class="Bound">R</a><a id="6103" class="Symbol">)</a> <a id="6105" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="6113" href="foundation.conjunction.html#5009" class="Function">map-inv-distributive-conjunction-Prop</a> <a id="6151" href="foundation.conjunction.html#5843" class="Bound">P</a> <a id="6153" href="foundation.conjunction.html#5857" class="Bound">Q</a> <a id="6155" class="Symbol">(</a><a id="6156" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="6166" href="foundation.conjunction.html#5871" class="Bound">R</a><a id="6167" class="Symbol">))</a>
</pre>
## See also

- The indexed counterpart to conjunction is
  [universal quantification](foundation.universal-quantification.md).

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}

## External links

- [logical conjunction](https://ncatlab.org/nlab/show/logical+conjunction) at
  $n$Lab
- [Logical conjunction](https://en.wikipedia.org/wiki/Logical_conjunction) at
  Wikipedia
