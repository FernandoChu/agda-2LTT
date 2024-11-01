# Commuting squares of identifications

<pre class="Agda"><a id="49" class="Keyword">module</a> <a id="56" href="foundation.commuting-squares-of-identifications.html" class="Module">foundation.commuting-squares-of-identifications</a> <a id="104" class="Keyword">where</a>

<a id="111" class="Keyword">open</a> <a id="116" class="Keyword">import</a> <a id="123" href="foundation-core.commuting-squares-of-identifications.html" class="Module">foundation-core.commuting-squares-of-identifications</a> <a id="176" class="Keyword">public</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="233" class="Keyword">open</a> <a id="238" class="Keyword">import</a> <a id="245" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="277" class="Keyword">open</a> <a id="282" class="Keyword">import</a> <a id="289" href="foundation.path-algebra.html" class="Module">foundation.path-algebra</a>
<a id="313" class="Keyword">open</a> <a id="318" class="Keyword">import</a> <a id="325" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="353" class="Keyword">open</a> <a id="358" class="Keyword">import</a> <a id="365" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="394" class="Keyword">open</a> <a id="399" class="Keyword">import</a> <a id="406" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
</pre>
</details>

## Idea

A square of [identifications](foundation-core.identity-types.md)

```text
           top
       x -------> y
       |          |
  left |          | right
       ∨          ∨
       z -------> w
          bottom
```

is said to be a
{{#concept "commuting square" Disambiguation="identifications" Agda=coherence-square-identifications}}
if there is an identification `left ∙ bottom ＝ top ∙ right`. Such an
identification is called a
{{#concept "coherence" Disambiguation="commuting square of identifications" Agda=coherence-square-identifications}}
of the square.

### Concatenating identifications of edges and coherences of commuting squares of identifications

Consider a commuting square of identifications and an identification of one of
the four sides with another identification, as for example in the diagram below:

```text
             top
       a ---------> b
       |           | |
  left |     right |=| right'
       ∨           ∨ ∨
       c ---------> d.
           bottom
```

Then any identification witnessing that the square commutes can be concatenated
with the identification on the side, to obtain a new commuting square of
identifications.

#### Concatenating identifications of the top edge with a coherence of a commuting square of identifications

Consider a commuting diagram of identifications

```text
           top'
         ------->
       x -------> y
       |   top    |
  left |          | right
       ∨          ∨
       z -------> w.
          bottom
```

with an identification `top ＝ top'`. Then we get an equivalence

```text
           top                             top'
       x -------> y                    x -------> y
       |          |                    |          |
  left |          | right    ≃    left |          | right
       ∨          ∨                    ∨          ∨
       z -------> w                    z -------> w.
          bottom                          bottom
```

<pre class="Agda"><a id="2407" class="Keyword">module</a> <a id="2414" href="foundation.commuting-squares-of-identifications.html#2414" class="Module">_</a>
  <a id="2418" class="Symbol">{</a><a id="2419" href="foundation.commuting-squares-of-identifications.html#2419" class="Bound">l</a> <a id="2421" class="Symbol">:</a> <a id="2423" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2428" class="Symbol">}</a> <a id="2430" class="Symbol">{</a><a id="2431" href="foundation.commuting-squares-of-identifications.html#2431" class="Bound">A</a> <a id="2433" class="Symbol">:</a> <a id="2435" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2438" href="foundation.commuting-squares-of-identifications.html#2419" class="Bound">l</a><a id="2439" class="Symbol">}</a> <a id="2441" class="Symbol">{</a><a id="2442" href="foundation.commuting-squares-of-identifications.html#2442" class="Bound">x</a> <a id="2444" href="foundation.commuting-squares-of-identifications.html#2444" class="Bound">y</a> <a id="2446" href="foundation.commuting-squares-of-identifications.html#2446" class="Bound">z</a> <a id="2448" href="foundation.commuting-squares-of-identifications.html#2448" class="Bound">w</a> <a id="2450" class="Symbol">:</a> <a id="2452" href="foundation.commuting-squares-of-identifications.html#2431" class="Bound">A</a><a id="2453" class="Symbol">}</a>
  <a id="2457" class="Symbol">(</a><a id="2458" href="foundation.commuting-squares-of-identifications.html#2458" class="Bound">top</a> <a id="2462" class="Symbol">:</a> <a id="2464" href="foundation.commuting-squares-of-identifications.html#2442" class="Bound">x</a> <a id="2466" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2468" href="foundation.commuting-squares-of-identifications.html#2444" class="Bound">y</a><a id="2469" class="Symbol">)</a> <a id="2471" class="Symbol">(</a><a id="2472" href="foundation.commuting-squares-of-identifications.html#2472" class="Bound">left</a> <a id="2477" class="Symbol">:</a> <a id="2479" href="foundation.commuting-squares-of-identifications.html#2442" class="Bound">x</a> <a id="2481" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2483" href="foundation.commuting-squares-of-identifications.html#2446" class="Bound">z</a><a id="2484" class="Symbol">)</a> <a id="2486" class="Symbol">(</a><a id="2487" href="foundation.commuting-squares-of-identifications.html#2487" class="Bound">right</a> <a id="2493" class="Symbol">:</a> <a id="2495" href="foundation.commuting-squares-of-identifications.html#2444" class="Bound">y</a> <a id="2497" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2499" href="foundation.commuting-squares-of-identifications.html#2448" class="Bound">w</a><a id="2500" class="Symbol">)</a> <a id="2502" class="Symbol">(</a><a id="2503" href="foundation.commuting-squares-of-identifications.html#2503" class="Bound">bottom</a> <a id="2510" class="Symbol">:</a> <a id="2512" href="foundation.commuting-squares-of-identifications.html#2446" class="Bound">z</a> <a id="2514" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2516" href="foundation.commuting-squares-of-identifications.html#2448" class="Bound">w</a><a id="2517" class="Symbol">)</a>
  <a id="2521" class="Symbol">{</a><a id="2522" href="foundation.commuting-squares-of-identifications.html#2522" class="Bound">top&#39;</a> <a id="2527" class="Symbol">:</a> <a id="2529" href="foundation.commuting-squares-of-identifications.html#2442" class="Bound">x</a> <a id="2531" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2533" href="foundation.commuting-squares-of-identifications.html#2444" class="Bound">y</a><a id="2534" class="Symbol">}</a> <a id="2536" class="Symbol">(</a><a id="2537" href="foundation.commuting-squares-of-identifications.html#2537" class="Bound">s</a> <a id="2539" class="Symbol">:</a> <a id="2541" href="foundation.commuting-squares-of-identifications.html#2458" class="Bound">top</a> <a id="2545" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2547" href="foundation.commuting-squares-of-identifications.html#2522" class="Bound">top&#39;</a><a id="2551" class="Symbol">)</a>
  <a id="2555" class="Keyword">where</a>

  <a id="2564" class="Keyword">abstract</a>
    <a id="2577" href="foundation.commuting-squares-of-identifications.html#2577" class="Function">is-equiv-concat-top-identification-coherence-square-identifications</a> <a id="2645" class="Symbol">:</a>
      <a id="2653" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a>
        <a id="2670" class="Symbol">(</a> <a id="2672" href="foundation-core.commuting-squares-of-identifications.html#9010" class="Function">concat-top-identification-coherence-square-identifications</a>
            <a id="2743" href="foundation.commuting-squares-of-identifications.html#2458" class="Bound">top</a> <a id="2747" href="foundation.commuting-squares-of-identifications.html#2472" class="Bound">left</a> <a id="2752" href="foundation.commuting-squares-of-identifications.html#2487" class="Bound">right</a> <a id="2758" href="foundation.commuting-squares-of-identifications.html#2503" class="Bound">bottom</a> <a id="2765" href="foundation.commuting-squares-of-identifications.html#2537" class="Bound">s</a><a id="2766" class="Symbol">)</a>
    <a id="2772" href="foundation.commuting-squares-of-identifications.html#2577" class="Function">is-equiv-concat-top-identification-coherence-square-identifications</a> <a id="2840" class="Symbol">=</a>
      <a id="2848" href="foundation-core.equivalences.html#4851" class="Function">is-equiv-is-invertible</a>
        <a id="2879" class="Symbol">(</a> <a id="2881" href="foundation-core.commuting-squares-of-identifications.html#9291" class="Function">inv-concat-top-identification-coherence-square-identifications</a>
            <a id="2956" href="foundation.commuting-squares-of-identifications.html#2458" class="Bound">top</a> <a id="2960" href="foundation.commuting-squares-of-identifications.html#2472" class="Bound">left</a> <a id="2965" href="foundation.commuting-squares-of-identifications.html#2487" class="Bound">right</a> <a id="2971" href="foundation.commuting-squares-of-identifications.html#2503" class="Bound">bottom</a> <a id="2978" href="foundation.commuting-squares-of-identifications.html#2537" class="Bound">s</a><a id="2979" class="Symbol">)</a>
        <a id="2989" class="Symbol">(</a> <a id="2991" href="foundation-core.commuting-squares-of-identifications.html#9586" class="Function">is-section-inv-concat-top-identification-coherence-square-identifications</a>
            <a id="3077" href="foundation.commuting-squares-of-identifications.html#2458" class="Bound">top</a> <a id="3081" href="foundation.commuting-squares-of-identifications.html#2472" class="Bound">left</a> <a id="3086" href="foundation.commuting-squares-of-identifications.html#2487" class="Bound">right</a> <a id="3092" href="foundation.commuting-squares-of-identifications.html#2503" class="Bound">bottom</a> <a id="3099" href="foundation.commuting-squares-of-identifications.html#2537" class="Bound">s</a><a id="3100" class="Symbol">)</a>
        <a id="3110" class="Symbol">(</a> <a id="3112" href="foundation-core.commuting-squares-of-identifications.html#9944" class="Function">is-retraction-inv-concat-top-identification-coherence-square-identifications</a>
            <a id="3201" href="foundation.commuting-squares-of-identifications.html#2458" class="Bound">top</a> <a id="3205" href="foundation.commuting-squares-of-identifications.html#2472" class="Bound">left</a> <a id="3210" href="foundation.commuting-squares-of-identifications.html#2487" class="Bound">right</a> <a id="3216" href="foundation.commuting-squares-of-identifications.html#2503" class="Bound">bottom</a> <a id="3223" href="foundation.commuting-squares-of-identifications.html#2537" class="Bound">s</a><a id="3224" class="Symbol">)</a>

  <a id="3229" href="foundation.commuting-squares-of-identifications.html#3229" class="Function">equiv-concat-top-identification-coherence-square-identifications</a> <a id="3294" class="Symbol">:</a>
    <a id="3300" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="3333" href="foundation.commuting-squares-of-identifications.html#2458" class="Bound">top</a> <a id="3337" href="foundation.commuting-squares-of-identifications.html#2472" class="Bound">left</a> <a id="3342" href="foundation.commuting-squares-of-identifications.html#2487" class="Bound">right</a> <a id="3348" href="foundation.commuting-squares-of-identifications.html#2503" class="Bound">bottom</a> <a id="3355" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="3361" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="3394" href="foundation.commuting-squares-of-identifications.html#2522" class="Bound">top&#39;</a> <a id="3399" href="foundation.commuting-squares-of-identifications.html#2472" class="Bound">left</a> <a id="3404" href="foundation.commuting-squares-of-identifications.html#2487" class="Bound">right</a> <a id="3410" href="foundation.commuting-squares-of-identifications.html#2503" class="Bound">bottom</a>
  <a id="3419" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3423" href="foundation.commuting-squares-of-identifications.html#3229" class="Function">equiv-concat-top-identification-coherence-square-identifications</a> <a id="3488" class="Symbol">=</a>
    <a id="3494" href="foundation-core.commuting-squares-of-identifications.html#9010" class="Function">concat-top-identification-coherence-square-identifications</a>
      <a id="3559" href="foundation.commuting-squares-of-identifications.html#2458" class="Bound">top</a> <a id="3563" href="foundation.commuting-squares-of-identifications.html#2472" class="Bound">left</a> <a id="3568" href="foundation.commuting-squares-of-identifications.html#2487" class="Bound">right</a> <a id="3574" href="foundation.commuting-squares-of-identifications.html#2503" class="Bound">bottom</a> <a id="3581" href="foundation.commuting-squares-of-identifications.html#2537" class="Bound">s</a>
  <a id="3585" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3589" href="foundation.commuting-squares-of-identifications.html#3229" class="Function">equiv-concat-top-identification-coherence-square-identifications</a> <a id="3654" class="Symbol">=</a>
    <a id="3660" href="foundation.commuting-squares-of-identifications.html#2577" class="Function">is-equiv-concat-top-identification-coherence-square-identifications</a>
</pre>
#### Concatenating identifications of the left edge with a coherence of a commuting square of identifications

Consider a commuting diagram of identifications

```text
              top
         x -------> y
        | |         |
  left' | | left    | right
        ∨ ∨         ∨
         z -------> w.
            bottom
```

with an identification `left ＝ left'`. Then we get an equivalence

```text
           top                              top
       x -------> y                     x -------> y
       |          |                     |          |
  left |          | right    ≃    left' |          | right
       ∨          ∨                     ∨          ∨
       z -------> w                     z -------> w.
          bottom                           bottom
```

<pre class="Agda"><a id="4518" class="Keyword">module</a> <a id="4525" href="foundation.commuting-squares-of-identifications.html#4525" class="Module">_</a>
  <a id="4529" class="Symbol">{</a><a id="4530" href="foundation.commuting-squares-of-identifications.html#4530" class="Bound">l</a> <a id="4532" class="Symbol">:</a> <a id="4534" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4539" class="Symbol">}</a> <a id="4541" class="Symbol">{</a><a id="4542" href="foundation.commuting-squares-of-identifications.html#4542" class="Bound">A</a> <a id="4544" class="Symbol">:</a> <a id="4546" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4549" href="foundation.commuting-squares-of-identifications.html#4530" class="Bound">l</a><a id="4550" class="Symbol">}</a> <a id="4552" class="Symbol">{</a><a id="4553" href="foundation.commuting-squares-of-identifications.html#4553" class="Bound">x</a> <a id="4555" href="foundation.commuting-squares-of-identifications.html#4555" class="Bound">y</a> <a id="4557" href="foundation.commuting-squares-of-identifications.html#4557" class="Bound">z</a> <a id="4559" href="foundation.commuting-squares-of-identifications.html#4559" class="Bound">w</a> <a id="4561" class="Symbol">:</a> <a id="4563" href="foundation.commuting-squares-of-identifications.html#4542" class="Bound">A</a><a id="4564" class="Symbol">}</a>
  <a id="4568" class="Symbol">(</a><a id="4569" href="foundation.commuting-squares-of-identifications.html#4569" class="Bound">top</a> <a id="4573" class="Symbol">:</a> <a id="4575" href="foundation.commuting-squares-of-identifications.html#4553" class="Bound">x</a> <a id="4577" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="4579" href="foundation.commuting-squares-of-identifications.html#4555" class="Bound">y</a><a id="4580" class="Symbol">)</a> <a id="4582" class="Symbol">(</a><a id="4583" href="foundation.commuting-squares-of-identifications.html#4583" class="Bound">left</a> <a id="4588" class="Symbol">:</a> <a id="4590" href="foundation.commuting-squares-of-identifications.html#4553" class="Bound">x</a> <a id="4592" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="4594" href="foundation.commuting-squares-of-identifications.html#4557" class="Bound">z</a><a id="4595" class="Symbol">)</a> <a id="4597" class="Symbol">(</a><a id="4598" href="foundation.commuting-squares-of-identifications.html#4598" class="Bound">right</a> <a id="4604" class="Symbol">:</a> <a id="4606" href="foundation.commuting-squares-of-identifications.html#4555" class="Bound">y</a> <a id="4608" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="4610" href="foundation.commuting-squares-of-identifications.html#4559" class="Bound">w</a><a id="4611" class="Symbol">)</a> <a id="4613" class="Symbol">(</a><a id="4614" href="foundation.commuting-squares-of-identifications.html#4614" class="Bound">bottom</a> <a id="4621" class="Symbol">:</a> <a id="4623" href="foundation.commuting-squares-of-identifications.html#4557" class="Bound">z</a> <a id="4625" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="4627" href="foundation.commuting-squares-of-identifications.html#4559" class="Bound">w</a><a id="4628" class="Symbol">)</a>
  <a id="4632" class="Symbol">{</a><a id="4633" href="foundation.commuting-squares-of-identifications.html#4633" class="Bound">left&#39;</a> <a id="4639" class="Symbol">:</a> <a id="4641" href="foundation.commuting-squares-of-identifications.html#4553" class="Bound">x</a> <a id="4643" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="4645" href="foundation.commuting-squares-of-identifications.html#4557" class="Bound">z</a><a id="4646" class="Symbol">}</a> <a id="4648" class="Symbol">(</a><a id="4649" href="foundation.commuting-squares-of-identifications.html#4649" class="Bound">s</a> <a id="4651" class="Symbol">:</a> <a id="4653" href="foundation.commuting-squares-of-identifications.html#4583" class="Bound">left</a> <a id="4658" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="4660" href="foundation.commuting-squares-of-identifications.html#4633" class="Bound">left&#39;</a><a id="4665" class="Symbol">)</a>
  <a id="4669" class="Keyword">where</a>

  <a id="4678" class="Keyword">abstract</a>
    <a id="4691" href="foundation.commuting-squares-of-identifications.html#4691" class="Function">is-equiv-concat-left-identification-coherence-square-identifications</a> <a id="4760" class="Symbol">:</a>
      <a id="4768" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a>
        <a id="4785" class="Symbol">(</a> <a id="4787" href="foundation-core.commuting-squares-of-identifications.html#11421" class="Function">concat-left-identification-coherence-square-identifications</a>
            <a id="4859" href="foundation.commuting-squares-of-identifications.html#4569" class="Bound">top</a> <a id="4863" href="foundation.commuting-squares-of-identifications.html#4583" class="Bound">left</a> <a id="4868" href="foundation.commuting-squares-of-identifications.html#4598" class="Bound">right</a> <a id="4874" href="foundation.commuting-squares-of-identifications.html#4614" class="Bound">bottom</a> <a id="4881" href="foundation.commuting-squares-of-identifications.html#4649" class="Bound">s</a><a id="4882" class="Symbol">)</a>
    <a id="4888" href="foundation.commuting-squares-of-identifications.html#4691" class="Function">is-equiv-concat-left-identification-coherence-square-identifications</a> <a id="4957" class="Symbol">=</a>
      <a id="4965" href="foundation-core.equivalences.html#4851" class="Function">is-equiv-is-invertible</a>
        <a id="4996" class="Symbol">(</a> <a id="4998" href="foundation-core.commuting-squares-of-identifications.html#11711" class="Function">inv-concat-left-identification-coherence-square-identifications</a>
            <a id="5074" href="foundation.commuting-squares-of-identifications.html#4569" class="Bound">top</a> <a id="5078" href="foundation.commuting-squares-of-identifications.html#4583" class="Bound">left</a> <a id="5083" href="foundation.commuting-squares-of-identifications.html#4598" class="Bound">right</a> <a id="5089" href="foundation.commuting-squares-of-identifications.html#4614" class="Bound">bottom</a> <a id="5096" href="foundation.commuting-squares-of-identifications.html#4649" class="Bound">s</a><a id="5097" class="Symbol">)</a>
        <a id="5107" class="Symbol">(</a> <a id="5109" href="foundation-core.commuting-squares-of-identifications.html#12003" class="Function">is-section-inv-concat-left-identification-coherence-square-identifications</a>
            <a id="5196" href="foundation.commuting-squares-of-identifications.html#4569" class="Bound">top</a> <a id="5200" href="foundation.commuting-squares-of-identifications.html#4583" class="Bound">left</a> <a id="5205" href="foundation.commuting-squares-of-identifications.html#4598" class="Bound">right</a> <a id="5211" href="foundation.commuting-squares-of-identifications.html#4614" class="Bound">bottom</a> <a id="5218" href="foundation.commuting-squares-of-identifications.html#4649" class="Bound">s</a><a id="5219" class="Symbol">)</a>
        <a id="5229" class="Symbol">(</a> <a id="5231" href="foundation-core.commuting-squares-of-identifications.html#12368" class="Function">is-retraction-inv-concat-left-identification-coherence-square-identifications</a>
            <a id="5321" href="foundation.commuting-squares-of-identifications.html#4569" class="Bound">top</a> <a id="5325" href="foundation.commuting-squares-of-identifications.html#4583" class="Bound">left</a> <a id="5330" href="foundation.commuting-squares-of-identifications.html#4598" class="Bound">right</a> <a id="5336" href="foundation.commuting-squares-of-identifications.html#4614" class="Bound">bottom</a> <a id="5343" href="foundation.commuting-squares-of-identifications.html#4649" class="Bound">s</a><a id="5344" class="Symbol">)</a>

  <a id="5349" href="foundation.commuting-squares-of-identifications.html#5349" class="Function">equiv-concat-left-identification-coherence-square-identifications</a> <a id="5415" class="Symbol">:</a>
    <a id="5421" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="5454" href="foundation.commuting-squares-of-identifications.html#4569" class="Bound">top</a> <a id="5458" href="foundation.commuting-squares-of-identifications.html#4583" class="Bound">left</a> <a id="5463" href="foundation.commuting-squares-of-identifications.html#4598" class="Bound">right</a> <a id="5469" href="foundation.commuting-squares-of-identifications.html#4614" class="Bound">bottom</a> <a id="5476" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="5482" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="5515" href="foundation.commuting-squares-of-identifications.html#4569" class="Bound">top</a> <a id="5519" href="foundation.commuting-squares-of-identifications.html#4633" class="Bound">left&#39;</a> <a id="5525" href="foundation.commuting-squares-of-identifications.html#4598" class="Bound">right</a> <a id="5531" href="foundation.commuting-squares-of-identifications.html#4614" class="Bound">bottom</a>
  <a id="5540" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5544" href="foundation.commuting-squares-of-identifications.html#5349" class="Function">equiv-concat-left-identification-coherence-square-identifications</a> <a id="5610" class="Symbol">=</a>
    <a id="5616" href="foundation-core.commuting-squares-of-identifications.html#11421" class="Function">concat-left-identification-coherence-square-identifications</a>
        <a id="5684" href="foundation.commuting-squares-of-identifications.html#4569" class="Bound">top</a> <a id="5688" href="foundation.commuting-squares-of-identifications.html#4583" class="Bound">left</a> <a id="5693" href="foundation.commuting-squares-of-identifications.html#4598" class="Bound">right</a> <a id="5699" href="foundation.commuting-squares-of-identifications.html#4614" class="Bound">bottom</a> <a id="5706" href="foundation.commuting-squares-of-identifications.html#4649" class="Bound">s</a>
  <a id="5710" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5714" href="foundation.commuting-squares-of-identifications.html#5349" class="Function">equiv-concat-left-identification-coherence-square-identifications</a> <a id="5780" class="Symbol">=</a>
    <a id="5786" href="foundation.commuting-squares-of-identifications.html#4691" class="Function">is-equiv-concat-left-identification-coherence-square-identifications</a>
</pre>
#### Concatenating identifications of the right edge with a coherence of a commuting square of identifications

Consider a commuting diagram of identifications

```text
            top
       x -------> y
       |         | |
  left |   right | | right'
       ∨         ∨ ∨
       z -------> w.
          bottom
```

with an identification `right ＝ right'`. Then we get an equivalence

```text
           top                             top
       x -------> y                    x -------> y
       |          |                    |          |
  left |          | right    ≃    left |          | right'
       ∨          ∨                    ∨          ∨
       z -------> w                    z -------> w.
          bottom                          bottom
```

<pre class="Agda"><a id="6632" class="Keyword">module</a> <a id="6639" href="foundation.commuting-squares-of-identifications.html#6639" class="Module">_</a>
  <a id="6643" class="Symbol">{</a><a id="6644" href="foundation.commuting-squares-of-identifications.html#6644" class="Bound">l</a> <a id="6646" class="Symbol">:</a> <a id="6648" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6653" class="Symbol">}</a> <a id="6655" class="Symbol">{</a><a id="6656" href="foundation.commuting-squares-of-identifications.html#6656" class="Bound">A</a> <a id="6658" class="Symbol">:</a> <a id="6660" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="6663" href="foundation.commuting-squares-of-identifications.html#6644" class="Bound">l</a><a id="6664" class="Symbol">}</a> <a id="6666" class="Symbol">{</a><a id="6667" href="foundation.commuting-squares-of-identifications.html#6667" class="Bound">x</a> <a id="6669" href="foundation.commuting-squares-of-identifications.html#6669" class="Bound">y</a> <a id="6671" href="foundation.commuting-squares-of-identifications.html#6671" class="Bound">z</a> <a id="6673" href="foundation.commuting-squares-of-identifications.html#6673" class="Bound">w</a> <a id="6675" class="Symbol">:</a> <a id="6677" href="foundation.commuting-squares-of-identifications.html#6656" class="Bound">A</a><a id="6678" class="Symbol">}</a>
  <a id="6682" class="Symbol">(</a><a id="6683" href="foundation.commuting-squares-of-identifications.html#6683" class="Bound">top</a> <a id="6687" class="Symbol">:</a> <a id="6689" href="foundation.commuting-squares-of-identifications.html#6667" class="Bound">x</a> <a id="6691" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="6693" href="foundation.commuting-squares-of-identifications.html#6669" class="Bound">y</a><a id="6694" class="Symbol">)</a> <a id="6696" class="Symbol">(</a><a id="6697" href="foundation.commuting-squares-of-identifications.html#6697" class="Bound">left</a> <a id="6702" class="Symbol">:</a> <a id="6704" href="foundation.commuting-squares-of-identifications.html#6667" class="Bound">x</a> <a id="6706" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="6708" href="foundation.commuting-squares-of-identifications.html#6671" class="Bound">z</a><a id="6709" class="Symbol">)</a> <a id="6711" class="Symbol">(</a><a id="6712" href="foundation.commuting-squares-of-identifications.html#6712" class="Bound">right</a> <a id="6718" class="Symbol">:</a> <a id="6720" href="foundation.commuting-squares-of-identifications.html#6669" class="Bound">y</a> <a id="6722" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="6724" href="foundation.commuting-squares-of-identifications.html#6673" class="Bound">w</a><a id="6725" class="Symbol">)</a> <a id="6727" class="Symbol">(</a><a id="6728" href="foundation.commuting-squares-of-identifications.html#6728" class="Bound">bottom</a> <a id="6735" class="Symbol">:</a> <a id="6737" href="foundation.commuting-squares-of-identifications.html#6671" class="Bound">z</a> <a id="6739" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="6741" href="foundation.commuting-squares-of-identifications.html#6673" class="Bound">w</a><a id="6742" class="Symbol">)</a>
  <a id="6746" class="Symbol">{</a><a id="6747" href="foundation.commuting-squares-of-identifications.html#6747" class="Bound">right&#39;</a> <a id="6754" class="Symbol">:</a> <a id="6756" href="foundation.commuting-squares-of-identifications.html#6669" class="Bound">y</a> <a id="6758" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="6760" href="foundation.commuting-squares-of-identifications.html#6673" class="Bound">w</a><a id="6761" class="Symbol">}</a> <a id="6763" class="Symbol">(</a><a id="6764" href="foundation.commuting-squares-of-identifications.html#6764" class="Bound">s</a> <a id="6766" class="Symbol">:</a> <a id="6768" href="foundation.commuting-squares-of-identifications.html#6712" class="Bound">right</a> <a id="6774" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="6776" href="foundation.commuting-squares-of-identifications.html#6747" class="Bound">right&#39;</a><a id="6782" class="Symbol">)</a>
  <a id="6786" class="Keyword">where</a>

  <a id="6795" class="Keyword">abstract</a>
    <a id="6808" href="foundation.commuting-squares-of-identifications.html#6808" class="Function">is-equiv-concat-right-identification-coherence-square-identifications</a> <a id="6878" class="Symbol">:</a>
      <a id="6886" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a>
        <a id="6903" class="Symbol">(</a> <a id="6905" href="foundation-core.commuting-squares-of-identifications.html#13836" class="Function">concat-right-identification-coherence-square-identifications</a>
            <a id="6978" href="foundation.commuting-squares-of-identifications.html#6683" class="Bound">top</a> <a id="6982" href="foundation.commuting-squares-of-identifications.html#6697" class="Bound">left</a> <a id="6987" href="foundation.commuting-squares-of-identifications.html#6712" class="Bound">right</a> <a id="6993" href="foundation.commuting-squares-of-identifications.html#6728" class="Bound">bottom</a> <a id="7000" href="foundation.commuting-squares-of-identifications.html#6764" class="Bound">s</a><a id="7001" class="Symbol">)</a>
    <a id="7007" href="foundation.commuting-squares-of-identifications.html#6808" class="Function">is-equiv-concat-right-identification-coherence-square-identifications</a> <a id="7077" class="Symbol">=</a>
      <a id="7085" href="foundation-core.equivalences.html#4851" class="Function">is-equiv-is-invertible</a>
        <a id="7116" class="Symbol">(</a> <a id="7118" href="foundation-core.commuting-squares-of-identifications.html#14118" class="Function">inv-concat-right-identification-coherence-square-identifications</a>
            <a id="7195" href="foundation.commuting-squares-of-identifications.html#6683" class="Bound">top</a> <a id="7199" href="foundation.commuting-squares-of-identifications.html#6697" class="Bound">left</a> <a id="7204" href="foundation.commuting-squares-of-identifications.html#6712" class="Bound">right</a> <a id="7210" href="foundation.commuting-squares-of-identifications.html#6728" class="Bound">bottom</a> <a id="7217" href="foundation.commuting-squares-of-identifications.html#6764" class="Bound">s</a><a id="7218" class="Symbol">)</a>
        <a id="7228" class="Symbol">(</a> <a id="7230" href="foundation-core.commuting-squares-of-identifications.html#14414" class="Function">is-section-inv-concat-right-identification-coherence-square-identifications</a>
            <a id="7318" href="foundation.commuting-squares-of-identifications.html#6683" class="Bound">top</a> <a id="7322" href="foundation.commuting-squares-of-identifications.html#6697" class="Bound">left</a> <a id="7327" href="foundation.commuting-squares-of-identifications.html#6712" class="Bound">right</a> <a id="7333" href="foundation.commuting-squares-of-identifications.html#6728" class="Bound">bottom</a> <a id="7340" href="foundation.commuting-squares-of-identifications.html#6764" class="Bound">s</a><a id="7341" class="Symbol">)</a>
        <a id="7351" class="Symbol">(</a> <a id="7353" href="foundation-core.commuting-squares-of-identifications.html#14777" class="Function">is-retraction-inv-concat-right-identification-coherence-square-identifications</a>
            <a id="7444" href="foundation.commuting-squares-of-identifications.html#6683" class="Bound">top</a> <a id="7448" href="foundation.commuting-squares-of-identifications.html#6697" class="Bound">left</a> <a id="7453" href="foundation.commuting-squares-of-identifications.html#6712" class="Bound">right</a> <a id="7459" href="foundation.commuting-squares-of-identifications.html#6728" class="Bound">bottom</a> <a id="7466" href="foundation.commuting-squares-of-identifications.html#6764" class="Bound">s</a><a id="7467" class="Symbol">)</a>

  <a id="7472" href="foundation.commuting-squares-of-identifications.html#7472" class="Function">equiv-concat-right-identification-coherence-square-identifications</a> <a id="7539" class="Symbol">:</a>
    <a id="7545" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="7578" href="foundation.commuting-squares-of-identifications.html#6683" class="Bound">top</a> <a id="7582" href="foundation.commuting-squares-of-identifications.html#6697" class="Bound">left</a> <a id="7587" href="foundation.commuting-squares-of-identifications.html#6712" class="Bound">right</a> <a id="7593" href="foundation.commuting-squares-of-identifications.html#6728" class="Bound">bottom</a> <a id="7600" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="7606" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="7639" href="foundation.commuting-squares-of-identifications.html#6683" class="Bound">top</a> <a id="7643" href="foundation.commuting-squares-of-identifications.html#6697" class="Bound">left</a> <a id="7648" href="foundation.commuting-squares-of-identifications.html#6747" class="Bound">right&#39;</a> <a id="7655" href="foundation.commuting-squares-of-identifications.html#6728" class="Bound">bottom</a>
  <a id="7664" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="7668" href="foundation.commuting-squares-of-identifications.html#7472" class="Function">equiv-concat-right-identification-coherence-square-identifications</a> <a id="7735" class="Symbol">=</a>
    <a id="7741" href="foundation-core.commuting-squares-of-identifications.html#13836" class="Function">concat-right-identification-coherence-square-identifications</a>
      <a id="7808" href="foundation.commuting-squares-of-identifications.html#6683" class="Bound">top</a> <a id="7812" href="foundation.commuting-squares-of-identifications.html#6697" class="Bound">left</a> <a id="7817" href="foundation.commuting-squares-of-identifications.html#6712" class="Bound">right</a> <a id="7823" href="foundation.commuting-squares-of-identifications.html#6728" class="Bound">bottom</a> <a id="7830" href="foundation.commuting-squares-of-identifications.html#6764" class="Bound">s</a>
  <a id="7834" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="7838" href="foundation.commuting-squares-of-identifications.html#7472" class="Function">equiv-concat-right-identification-coherence-square-identifications</a> <a id="7905" class="Symbol">=</a>
    <a id="7911" href="foundation.commuting-squares-of-identifications.html#6808" class="Function">is-equiv-concat-right-identification-coherence-square-identifications</a>
</pre>
#### Concatenating identifications of the bottom edge with a coherence of a commuting square of identifications

Consider a commuting diagram of identifications

```text
            top
       x -------> y
       |          |
  left |          | right
       ∨  bottom  ∨
       z -------> w.
         ------->
          bottom'
```

with an identification `bottom ＝ bottom'`. Then we get an equivalence

```text
           top                             top
       x -------> y                    x -------> y
       |          |                    |          |
  left |          | right    ≃    left |          | right
       ∨          ∨                    ∨          ∨
       z -------> w                    z -------> w.
          bottom                          bottom'
```

<pre class="Agda"><a id="8776" class="Keyword">module</a> <a id="8783" href="foundation.commuting-squares-of-identifications.html#8783" class="Module">_</a>
  <a id="8787" class="Symbol">{</a><a id="8788" href="foundation.commuting-squares-of-identifications.html#8788" class="Bound">l</a> <a id="8790" class="Symbol">:</a> <a id="8792" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="8797" class="Symbol">}</a> <a id="8799" class="Symbol">{</a><a id="8800" href="foundation.commuting-squares-of-identifications.html#8800" class="Bound">A</a> <a id="8802" class="Symbol">:</a> <a id="8804" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="8807" href="foundation.commuting-squares-of-identifications.html#8788" class="Bound">l</a><a id="8808" class="Symbol">}</a> <a id="8810" class="Symbol">{</a><a id="8811" href="foundation.commuting-squares-of-identifications.html#8811" class="Bound">x</a> <a id="8813" href="foundation.commuting-squares-of-identifications.html#8813" class="Bound">y</a> <a id="8815" href="foundation.commuting-squares-of-identifications.html#8815" class="Bound">z</a> <a id="8817" href="foundation.commuting-squares-of-identifications.html#8817" class="Bound">w</a> <a id="8819" class="Symbol">:</a> <a id="8821" href="foundation.commuting-squares-of-identifications.html#8800" class="Bound">A</a><a id="8822" class="Symbol">}</a>
  <a id="8826" class="Symbol">(</a><a id="8827" href="foundation.commuting-squares-of-identifications.html#8827" class="Bound">top</a> <a id="8831" class="Symbol">:</a> <a id="8833" href="foundation.commuting-squares-of-identifications.html#8811" class="Bound">x</a> <a id="8835" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="8837" href="foundation.commuting-squares-of-identifications.html#8813" class="Bound">y</a><a id="8838" class="Symbol">)</a> <a id="8840" class="Symbol">(</a><a id="8841" href="foundation.commuting-squares-of-identifications.html#8841" class="Bound">left</a> <a id="8846" class="Symbol">:</a> <a id="8848" href="foundation.commuting-squares-of-identifications.html#8811" class="Bound">x</a> <a id="8850" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="8852" href="foundation.commuting-squares-of-identifications.html#8815" class="Bound">z</a><a id="8853" class="Symbol">)</a> <a id="8855" class="Symbol">(</a><a id="8856" href="foundation.commuting-squares-of-identifications.html#8856" class="Bound">right</a> <a id="8862" class="Symbol">:</a> <a id="8864" href="foundation.commuting-squares-of-identifications.html#8813" class="Bound">y</a> <a id="8866" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="8868" href="foundation.commuting-squares-of-identifications.html#8817" class="Bound">w</a><a id="8869" class="Symbol">)</a> <a id="8871" class="Symbol">(</a><a id="8872" href="foundation.commuting-squares-of-identifications.html#8872" class="Bound">bottom</a> <a id="8879" class="Symbol">:</a> <a id="8881" href="foundation.commuting-squares-of-identifications.html#8815" class="Bound">z</a> <a id="8883" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="8885" href="foundation.commuting-squares-of-identifications.html#8817" class="Bound">w</a><a id="8886" class="Symbol">)</a>
  <a id="8890" class="Symbol">{</a><a id="8891" href="foundation.commuting-squares-of-identifications.html#8891" class="Bound">bottom&#39;</a> <a id="8899" class="Symbol">:</a> <a id="8901" href="foundation.commuting-squares-of-identifications.html#8815" class="Bound">z</a> <a id="8903" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="8905" href="foundation.commuting-squares-of-identifications.html#8817" class="Bound">w</a><a id="8906" class="Symbol">}</a> <a id="8908" class="Symbol">(</a><a id="8909" href="foundation.commuting-squares-of-identifications.html#8909" class="Bound">s</a> <a id="8911" class="Symbol">:</a> <a id="8913" href="foundation.commuting-squares-of-identifications.html#8872" class="Bound">bottom</a> <a id="8920" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="8922" href="foundation.commuting-squares-of-identifications.html#8891" class="Bound">bottom&#39;</a><a id="8929" class="Symbol">)</a>
  <a id="8933" class="Keyword">where</a>

  <a id="8942" href="foundation.commuting-squares-of-identifications.html#8942" class="Function">is-equiv-concat-bottom-identification-coherence-square-identifications</a> <a id="9013" class="Symbol">:</a>
    <a id="9019" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a>
      <a id="9034" class="Symbol">(</a> <a id="9036" href="foundation-core.commuting-squares-of-identifications.html#16270" class="Function">concat-bottom-identification-coherence-square-identifications</a>
          <a id="9108" href="foundation.commuting-squares-of-identifications.html#8827" class="Bound">top</a> <a id="9112" href="foundation.commuting-squares-of-identifications.html#8841" class="Bound">left</a> <a id="9117" href="foundation.commuting-squares-of-identifications.html#8856" class="Bound">right</a> <a id="9123" href="foundation.commuting-squares-of-identifications.html#8872" class="Bound">bottom</a> <a id="9130" href="foundation.commuting-squares-of-identifications.html#8909" class="Bound">s</a><a id="9131" class="Symbol">)</a>
  <a id="9135" href="foundation.commuting-squares-of-identifications.html#8942" class="Function">is-equiv-concat-bottom-identification-coherence-square-identifications</a> <a id="9206" class="Symbol">=</a>
    <a id="9212" href="foundation-core.equivalences.html#4851" class="Function">is-equiv-is-invertible</a>
      <a id="9241" class="Symbol">(</a> <a id="9243" href="foundation-core.commuting-squares-of-identifications.html#16561" class="Function">inv-concat-bottom-identification-coherence-square-identifications</a>
          <a id="9319" href="foundation.commuting-squares-of-identifications.html#8827" class="Bound">top</a> <a id="9323" href="foundation.commuting-squares-of-identifications.html#8841" class="Bound">left</a> <a id="9328" href="foundation.commuting-squares-of-identifications.html#8856" class="Bound">right</a> <a id="9334" href="foundation.commuting-squares-of-identifications.html#8872" class="Bound">bottom</a> <a id="9341" href="foundation.commuting-squares-of-identifications.html#8909" class="Bound">s</a><a id="9342" class="Symbol">)</a>
      <a id="9350" class="Symbol">(</a> <a id="9352" href="foundation-core.commuting-squares-of-identifications.html#16854" class="Function">is-section-inv-concat-bottom-identification-coherence-square-identifications</a>
          <a id="9439" href="foundation.commuting-squares-of-identifications.html#8827" class="Bound">top</a> <a id="9443" href="foundation.commuting-squares-of-identifications.html#8841" class="Bound">left</a> <a id="9448" href="foundation.commuting-squares-of-identifications.html#8856" class="Bound">right</a> <a id="9454" href="foundation.commuting-squares-of-identifications.html#8872" class="Bound">bottom</a> <a id="9461" href="foundation.commuting-squares-of-identifications.html#8909" class="Bound">s</a><a id="9462" class="Symbol">)</a>
      <a id="9470" class="Symbol">(</a> <a id="9472" href="foundation-core.commuting-squares-of-identifications.html#17224" class="Function">is-retraction-inv-concat-bottom-identification-coherence-square-identifications</a>
          <a id="9562" href="foundation.commuting-squares-of-identifications.html#8827" class="Bound">top</a> <a id="9566" href="foundation.commuting-squares-of-identifications.html#8841" class="Bound">left</a> <a id="9571" href="foundation.commuting-squares-of-identifications.html#8856" class="Bound">right</a> <a id="9577" href="foundation.commuting-squares-of-identifications.html#8872" class="Bound">bottom</a> <a id="9584" href="foundation.commuting-squares-of-identifications.html#8909" class="Bound">s</a><a id="9585" class="Symbol">)</a>

  <a id="9590" href="foundation.commuting-squares-of-identifications.html#9590" class="Function">equiv-concat-bottom-identification-coherence-square-identifications</a> <a id="9658" class="Symbol">:</a>
    <a id="9664" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="9697" href="foundation.commuting-squares-of-identifications.html#8827" class="Bound">top</a> <a id="9701" href="foundation.commuting-squares-of-identifications.html#8841" class="Bound">left</a> <a id="9706" href="foundation.commuting-squares-of-identifications.html#8856" class="Bound">right</a> <a id="9712" href="foundation.commuting-squares-of-identifications.html#8872" class="Bound">bottom</a> <a id="9719" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="9725" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="9758" href="foundation.commuting-squares-of-identifications.html#8827" class="Bound">top</a> <a id="9762" href="foundation.commuting-squares-of-identifications.html#8841" class="Bound">left</a> <a id="9767" href="foundation.commuting-squares-of-identifications.html#8856" class="Bound">right</a> <a id="9773" href="foundation.commuting-squares-of-identifications.html#8891" class="Bound">bottom&#39;</a>
  <a id="9783" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="9787" href="foundation.commuting-squares-of-identifications.html#9590" class="Function">equiv-concat-bottom-identification-coherence-square-identifications</a> <a id="9855" class="Symbol">=</a>
    <a id="9861" href="foundation-core.commuting-squares-of-identifications.html#16270" class="Function">concat-bottom-identification-coherence-square-identifications</a>
        <a id="9931" href="foundation.commuting-squares-of-identifications.html#8827" class="Bound">top</a> <a id="9935" href="foundation.commuting-squares-of-identifications.html#8841" class="Bound">left</a> <a id="9940" href="foundation.commuting-squares-of-identifications.html#8856" class="Bound">right</a> <a id="9946" href="foundation.commuting-squares-of-identifications.html#8872" class="Bound">bottom</a> <a id="9953" href="foundation.commuting-squares-of-identifications.html#8909" class="Bound">s</a>
  <a id="9957" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="9961" href="foundation.commuting-squares-of-identifications.html#9590" class="Function">equiv-concat-bottom-identification-coherence-square-identifications</a> <a id="10029" class="Symbol">=</a>
    <a id="10035" href="foundation.commuting-squares-of-identifications.html#8942" class="Function">is-equiv-concat-bottom-identification-coherence-square-identifications</a>
</pre>
### Whiskering and splicing coherences of commuting squares of identifications

Given a commuting square of identifications

```text
           top
       x -------> y
       |          |
  left |          | right
       ∨          ∨
       z -------> w,
          bottom
```

we may consider four ways of attaching new identifications to it:

1. Prepending `p : u ＝ x` to the left gives us a commuting square

   ```text
                p ∙ top
              u -------> y
              |          |
     p ∙ left |          | right
              ∨          ∨
              z -------> w.
                 bottom
   ```

   More precisely, we have an equivalence

   ```text
     (left ∙ bottom ＝ top ∙ right) ≃ ((p ∙ left) ∙ bottom ＝ (p ∙ top) ∙ right).
   ```

2. Appending an identification `p : w ＝ u` to the right gives a commuting
   square of identifications

   ```text
                   top
           x ------------> y
           |               |
      left |               | right ∙ p
           ∨               ∨
           z ------------> u.
              bottom ∙ p
   ```

   More precisely, we have an equivalence

   ```text
     (left ∙ bottom ＝ top ∙ right) ≃ (left ∙ (bottom ∙ p) ＝ top ∙ (right ∙ p)).
   ```

3. Splicing an identification `p : z ＝ u` and its inverse into the middle gives
   a commuting square of identifications

   ```text
                      top
              x --------------> y
              |                 |
     left ∙ p |                 | right
              ∨                 ∨
              u --------------> w.
                 p⁻¹ ∙ bottom
   ```

   More precisely, we have an equivalence

   ```text
     (left ∙ bottom ＝ top ∙ right) ≃ ((left ∙ p) ∙ (p⁻¹ ∙ bottom) ＝ top ∙ right).
   ```

   Similarly, we have an equivalence

   ```text
     (left ∙ bottom ＝ top ∙ right) ≃ ((left ∙ p⁻¹) ∙ (p ∙ bottom) ＝ top ∙ right).
   ```

4. Splicing an identification `p : y ＝ u` and its inverse into the middle gives
   a commuting square of identifications

   ```text
             top ∙ p
          x --------> u
          |           |
     left |           | p⁻¹ ∙ right
          ∨           ∨
          z --------> w.
             bottom
   ```

   More precisely, we have an equivalence

   ```text
     (left ∙ bottom ＝ top ∙ right) ≃ (left ∙ bottom ＝ (top ∙ p) ∙ (p⁻¹ ∙ right)).
   ```

   Similarly, we have an equivalence

   ```text
     (left ∙ bottom ＝ top ∙ right) ≃ (left ∙ bottom ＝ (top ∙ p⁻¹) ∙ (p ∙ right)).
   ```

These operations are useful in proofs involving path algebra, because taking
`equiv-right-whisker-concat-coherence-square-identifications` as an example, it
provides us with two maps: the forward direction states
`(p ∙ r ＝ q ∙ s) → (p ∙ (r ∙ t)) ＝ q ∙ (s ∙ t))`, which allows one to append
an identification without needing to reassociate on the right, and the backwards
direction conversely allows one to cancel out an identification in parentheses.

#### Left whiskering coherences of commuting squares of identifications

For any identification `p : u ＝ x` we obtain an equivalence

```text
           top                                p ∙ top
       x -------> y                         u -------> y
       |          |                         |          |
  left |          | right    ≃     p ∙ left |          | right
       ∨          ∨                         ∨          ∨
       z -------> w                         z -------> w
          bottom                               bottom
```

of coherences of commuting squares of identifications.

<pre class="Agda"><a id="13659" class="Keyword">module</a> <a id="13666" href="foundation.commuting-squares-of-identifications.html#13666" class="Module">_</a>
  <a id="13670" class="Symbol">{</a><a id="13671" href="foundation.commuting-squares-of-identifications.html#13671" class="Bound">l</a> <a id="13673" class="Symbol">:</a> <a id="13675" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="13680" class="Symbol">}</a> <a id="13682" class="Symbol">{</a><a id="13683" href="foundation.commuting-squares-of-identifications.html#13683" class="Bound">A</a> <a id="13685" class="Symbol">:</a> <a id="13687" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="13690" href="foundation.commuting-squares-of-identifications.html#13671" class="Bound">l</a><a id="13691" class="Symbol">}</a> <a id="13693" class="Symbol">{</a><a id="13694" href="foundation.commuting-squares-of-identifications.html#13694" class="Bound">x</a> <a id="13696" href="foundation.commuting-squares-of-identifications.html#13696" class="Bound">y</a> <a id="13698" href="foundation.commuting-squares-of-identifications.html#13698" class="Bound">z</a> <a id="13700" href="foundation.commuting-squares-of-identifications.html#13700" class="Bound">w</a> <a id="13702" href="foundation.commuting-squares-of-identifications.html#13702" class="Bound">u</a> <a id="13704" class="Symbol">:</a> <a id="13706" href="foundation.commuting-squares-of-identifications.html#13683" class="Bound">A</a><a id="13707" class="Symbol">}</a>
  <a id="13711" class="Keyword">where</a>

  <a id="13720" href="foundation.commuting-squares-of-identifications.html#13720" class="Function">equiv-left-whisker-concat-coherence-square-identifications</a> <a id="13779" class="Symbol">:</a>
    <a id="13785" class="Symbol">(</a><a id="13786" href="foundation.commuting-squares-of-identifications.html#13786" class="Bound">p</a> <a id="13788" class="Symbol">:</a> <a id="13790" href="foundation.commuting-squares-of-identifications.html#13702" class="Bound">u</a> <a id="13792" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="13794" href="foundation.commuting-squares-of-identifications.html#13694" class="Bound">x</a><a id="13795" class="Symbol">)</a>
    <a id="13801" class="Symbol">(</a><a id="13802" href="foundation.commuting-squares-of-identifications.html#13802" class="Bound">top</a> <a id="13806" class="Symbol">:</a> <a id="13808" href="foundation.commuting-squares-of-identifications.html#13694" class="Bound">x</a> <a id="13810" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="13812" href="foundation.commuting-squares-of-identifications.html#13696" class="Bound">y</a><a id="13813" class="Symbol">)</a> <a id="13815" class="Symbol">(</a><a id="13816" href="foundation.commuting-squares-of-identifications.html#13816" class="Bound">left</a> <a id="13821" class="Symbol">:</a> <a id="13823" href="foundation.commuting-squares-of-identifications.html#13694" class="Bound">x</a> <a id="13825" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="13827" href="foundation.commuting-squares-of-identifications.html#13698" class="Bound">z</a><a id="13828" class="Symbol">)</a> <a id="13830" class="Symbol">(</a><a id="13831" href="foundation.commuting-squares-of-identifications.html#13831" class="Bound">right</a> <a id="13837" class="Symbol">:</a> <a id="13839" href="foundation.commuting-squares-of-identifications.html#13696" class="Bound">y</a> <a id="13841" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="13843" href="foundation.commuting-squares-of-identifications.html#13700" class="Bound">w</a><a id="13844" class="Symbol">)</a> <a id="13846" class="Symbol">(</a><a id="13847" href="foundation.commuting-squares-of-identifications.html#13847" class="Bound">bottom</a> <a id="13854" class="Symbol">:</a> <a id="13856" href="foundation.commuting-squares-of-identifications.html#13698" class="Bound">z</a> <a id="13858" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="13860" href="foundation.commuting-squares-of-identifications.html#13700" class="Bound">w</a><a id="13861" class="Symbol">)</a> <a id="13863" class="Symbol">→</a>
    <a id="13869" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="13902" href="foundation.commuting-squares-of-identifications.html#13802" class="Bound">top</a> <a id="13906" href="foundation.commuting-squares-of-identifications.html#13816" class="Bound">left</a> <a id="13911" href="foundation.commuting-squares-of-identifications.html#13831" class="Bound">right</a> <a id="13917" href="foundation.commuting-squares-of-identifications.html#13847" class="Bound">bottom</a> <a id="13924" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="13930" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="13963" class="Symbol">(</a><a id="13964" href="foundation.commuting-squares-of-identifications.html#13786" class="Bound">p</a> <a id="13966" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="13968" href="foundation.commuting-squares-of-identifications.html#13802" class="Bound">top</a><a id="13971" class="Symbol">)</a> <a id="13973" class="Symbol">(</a><a id="13974" href="foundation.commuting-squares-of-identifications.html#13786" class="Bound">p</a> <a id="13976" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="13978" href="foundation.commuting-squares-of-identifications.html#13816" class="Bound">left</a><a id="13982" class="Symbol">)</a> <a id="13984" href="foundation.commuting-squares-of-identifications.html#13831" class="Bound">right</a> <a id="13990" href="foundation.commuting-squares-of-identifications.html#13847" class="Bound">bottom</a>
  <a id="13999" href="foundation.commuting-squares-of-identifications.html#13720" class="Function">equiv-left-whisker-concat-coherence-square-identifications</a>
    <a id="14062" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="14067" href="foundation.commuting-squares-of-identifications.html#14067" class="Bound">top</a> <a id="14071" href="foundation.commuting-squares-of-identifications.html#14071" class="Bound">left</a> <a id="14076" href="foundation.commuting-squares-of-identifications.html#14076" class="Bound">right</a> <a id="14082" href="foundation.commuting-squares-of-identifications.html#14082" class="Bound">bottom</a> <a id="14089" class="Symbol">=</a>
    <a id="14095" href="foundation-core.equivalences.html#3922" class="Function">id-equiv</a>
</pre>
#### Right whiskering coherences of commuting squares of identifications

For any identification `p : w ＝ u` we obtain an equivalence

```text
           top                                 top
       x -------> y                     x ------------> y
       |          |                     |               |
  left |          | right    ≃     left |               | right ∙ p
       ∨          ∨                     ∨               ∨
       z -------> w                     z ------------> w
          bottom                           bottom ∙ p
```

of coherences of commuting squares of identifications.

<pre class="Agda"><a id="14726" class="Keyword">module</a> <a id="14733" href="foundation.commuting-squares-of-identifications.html#14733" class="Module">_</a>
  <a id="14737" class="Symbol">{</a><a id="14738" href="foundation.commuting-squares-of-identifications.html#14738" class="Bound">l</a> <a id="14740" class="Symbol">:</a> <a id="14742" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="14747" class="Symbol">}</a> <a id="14749" class="Symbol">{</a><a id="14750" href="foundation.commuting-squares-of-identifications.html#14750" class="Bound">A</a> <a id="14752" class="Symbol">:</a> <a id="14754" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="14757" href="foundation.commuting-squares-of-identifications.html#14738" class="Bound">l</a><a id="14758" class="Symbol">}</a> <a id="14760" class="Symbol">{</a><a id="14761" href="foundation.commuting-squares-of-identifications.html#14761" class="Bound">x</a> <a id="14763" href="foundation.commuting-squares-of-identifications.html#14763" class="Bound">y</a> <a id="14765" href="foundation.commuting-squares-of-identifications.html#14765" class="Bound">z</a> <a id="14767" href="foundation.commuting-squares-of-identifications.html#14767" class="Bound">w</a> <a id="14769" class="Symbol">:</a> <a id="14771" href="foundation.commuting-squares-of-identifications.html#14750" class="Bound">A</a><a id="14772" class="Symbol">}</a>
  <a id="14776" class="Symbol">(</a><a id="14777" href="foundation.commuting-squares-of-identifications.html#14777" class="Bound">top</a> <a id="14781" class="Symbol">:</a> <a id="14783" href="foundation.commuting-squares-of-identifications.html#14761" class="Bound">x</a> <a id="14785" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="14787" href="foundation.commuting-squares-of-identifications.html#14763" class="Bound">y</a><a id="14788" class="Symbol">)</a> <a id="14790" class="Symbol">(</a><a id="14791" href="foundation.commuting-squares-of-identifications.html#14791" class="Bound">left</a> <a id="14796" class="Symbol">:</a> <a id="14798" href="foundation.commuting-squares-of-identifications.html#14761" class="Bound">x</a> <a id="14800" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="14802" href="foundation.commuting-squares-of-identifications.html#14765" class="Bound">z</a><a id="14803" class="Symbol">)</a> <a id="14805" class="Symbol">(</a><a id="14806" href="foundation.commuting-squares-of-identifications.html#14806" class="Bound">right</a> <a id="14812" class="Symbol">:</a> <a id="14814" href="foundation.commuting-squares-of-identifications.html#14763" class="Bound">y</a> <a id="14816" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="14818" href="foundation.commuting-squares-of-identifications.html#14767" class="Bound">w</a><a id="14819" class="Symbol">)</a> <a id="14821" class="Symbol">(</a><a id="14822" href="foundation.commuting-squares-of-identifications.html#14822" class="Bound">bottom</a> <a id="14829" class="Symbol">:</a> <a id="14831" href="foundation.commuting-squares-of-identifications.html#14765" class="Bound">z</a> <a id="14833" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="14835" href="foundation.commuting-squares-of-identifications.html#14767" class="Bound">w</a><a id="14836" class="Symbol">)</a>
  <a id="14840" class="Keyword">where</a>

  <a id="14849" href="foundation.commuting-squares-of-identifications.html#14849" class="Function">equiv-right-whisker-concat-coherence-square-identifications</a> <a id="14909" class="Symbol">:</a>
    <a id="14915" class="Symbol">{</a><a id="14916" href="foundation.commuting-squares-of-identifications.html#14916" class="Bound">u</a> <a id="14918" class="Symbol">:</a> <a id="14920" href="foundation.commuting-squares-of-identifications.html#14750" class="Bound">A</a><a id="14921" class="Symbol">}</a> <a id="14923" class="Symbol">(</a><a id="14924" href="foundation.commuting-squares-of-identifications.html#14924" class="Bound">p</a> <a id="14926" class="Symbol">:</a> <a id="14928" href="foundation.commuting-squares-of-identifications.html#14767" class="Bound">w</a> <a id="14930" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="14932" href="foundation.commuting-squares-of-identifications.html#14916" class="Bound">u</a><a id="14933" class="Symbol">)</a> <a id="14935" class="Symbol">→</a>
    <a id="14941" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="14974" href="foundation.commuting-squares-of-identifications.html#14777" class="Bound">top</a> <a id="14978" href="foundation.commuting-squares-of-identifications.html#14791" class="Bound">left</a> <a id="14983" href="foundation.commuting-squares-of-identifications.html#14806" class="Bound">right</a> <a id="14989" href="foundation.commuting-squares-of-identifications.html#14822" class="Bound">bottom</a> <a id="14996" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="15002" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="15035" href="foundation.commuting-squares-of-identifications.html#14777" class="Bound">top</a> <a id="15039" href="foundation.commuting-squares-of-identifications.html#14791" class="Bound">left</a> <a id="15044" class="Symbol">(</a><a id="15045" href="foundation.commuting-squares-of-identifications.html#14806" class="Bound">right</a> <a id="15051" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="15053" href="foundation.commuting-squares-of-identifications.html#14924" class="Bound">p</a><a id="15054" class="Symbol">)</a> <a id="15056" class="Symbol">(</a><a id="15057" href="foundation.commuting-squares-of-identifications.html#14822" class="Bound">bottom</a> <a id="15064" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="15066" href="foundation.commuting-squares-of-identifications.html#14924" class="Bound">p</a><a id="15067" class="Symbol">)</a>
  <a id="15071" href="foundation.commuting-squares-of-identifications.html#14849" class="Function">equiv-right-whisker-concat-coherence-square-identifications</a> <a id="15131" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="15136" class="Symbol">=</a>
    <a id="15142" class="Symbol">(</a> <a id="15144" href="foundation.commuting-squares-of-identifications.html#9590" class="Function">equiv-concat-bottom-identification-coherence-square-identifications</a>
      <a id="15218" class="Symbol">(</a> <a id="15220" href="foundation.commuting-squares-of-identifications.html#14777" class="Bound">top</a><a id="15223" class="Symbol">)</a>
      <a id="15231" class="Symbol">(</a> <a id="15233" href="foundation.commuting-squares-of-identifications.html#14791" class="Bound">left</a><a id="15237" class="Symbol">)</a>
      <a id="15245" class="Symbol">(</a> <a id="15247" href="foundation.commuting-squares-of-identifications.html#14806" class="Bound">right</a> <a id="15253" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="15255" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="15259" class="Symbol">)</a>
      <a id="15267" class="Symbol">(</a> <a id="15269" href="foundation.commuting-squares-of-identifications.html#14822" class="Bound">bottom</a><a id="15275" class="Symbol">)</a>
      <a id="15283" class="Symbol">(</a> <a id="15285" href="foundation-core.identity-types.html#6168" class="Function">inv</a> <a id="15289" href="foundation-core.identity-types.html#8258" class="Function">right-unit</a><a id="15299" class="Symbol">))</a> <a id="15302" href="foundation-core.equivalences.html#13323" class="Function Operator">∘e</a>
    <a id="15309" class="Symbol">(</a> <a id="15311" href="foundation.commuting-squares-of-identifications.html#7472" class="Function">equiv-concat-right-identification-coherence-square-identifications</a>
      <a id="15384" class="Symbol">(</a> <a id="15386" href="foundation.commuting-squares-of-identifications.html#14777" class="Bound">top</a><a id="15389" class="Symbol">)</a>
      <a id="15397" class="Symbol">(</a> <a id="15399" href="foundation.commuting-squares-of-identifications.html#14791" class="Bound">left</a><a id="15403" class="Symbol">)</a>
      <a id="15411" class="Symbol">(</a> <a id="15413" href="foundation.commuting-squares-of-identifications.html#14806" class="Bound">right</a><a id="15418" class="Symbol">)</a>
      <a id="15426" class="Symbol">(</a> <a id="15428" href="foundation.commuting-squares-of-identifications.html#14822" class="Bound">bottom</a><a id="15434" class="Symbol">)</a>
      <a id="15442" class="Symbol">(</a> <a id="15444" href="foundation-core.identity-types.html#6168" class="Function">inv</a> <a id="15448" href="foundation-core.identity-types.html#8258" class="Function">right-unit</a><a id="15458" class="Symbol">))</a>
</pre>
#### Left splicing coherences of commuting squares of identifications

For any inverse pair of identifications `p : y ＝ u` and `q : u ＝ y` equipped
with `α : inv p ＝ q` we obtain an equivalence

```text
           top                                    top
       x -------> y                         x -----------> y
       |          |                         |              |
  left |          | right    ≃     left ∙ p |              | right
       ∨          ∨                         ∨              ∨
       z -------> w                         u -----------> w
          bottom                               q ∙ bottom
```

of coherences of commuting squares of identifications.

<pre class="Agda"><a id="16161" class="Keyword">module</a> <a id="16168" href="foundation.commuting-squares-of-identifications.html#16168" class="Module">_</a>
  <a id="16172" class="Symbol">{</a><a id="16173" href="foundation.commuting-squares-of-identifications.html#16173" class="Bound">l</a> <a id="16175" class="Symbol">:</a> <a id="16177" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="16182" class="Symbol">}</a> <a id="16184" class="Symbol">{</a><a id="16185" href="foundation.commuting-squares-of-identifications.html#16185" class="Bound">A</a> <a id="16187" class="Symbol">:</a> <a id="16189" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="16192" href="foundation.commuting-squares-of-identifications.html#16173" class="Bound">l</a><a id="16193" class="Symbol">}</a> <a id="16195" class="Symbol">{</a><a id="16196" href="foundation.commuting-squares-of-identifications.html#16196" class="Bound">x</a> <a id="16198" href="foundation.commuting-squares-of-identifications.html#16198" class="Bound">y</a> <a id="16200" href="foundation.commuting-squares-of-identifications.html#16200" class="Bound">z</a> <a id="16202" href="foundation.commuting-squares-of-identifications.html#16202" class="Bound">w</a> <a id="16204" class="Symbol">:</a> <a id="16206" href="foundation.commuting-squares-of-identifications.html#16185" class="Bound">A</a><a id="16207" class="Symbol">}</a>
  <a id="16211" class="Symbol">(</a><a id="16212" href="foundation.commuting-squares-of-identifications.html#16212" class="Bound">top</a> <a id="16216" class="Symbol">:</a> <a id="16218" href="foundation.commuting-squares-of-identifications.html#16196" class="Bound">x</a> <a id="16220" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="16222" href="foundation.commuting-squares-of-identifications.html#16198" class="Bound">y</a><a id="16223" class="Symbol">)</a> <a id="16225" class="Symbol">(</a><a id="16226" href="foundation.commuting-squares-of-identifications.html#16226" class="Bound">left</a> <a id="16231" class="Symbol">:</a> <a id="16233" href="foundation.commuting-squares-of-identifications.html#16196" class="Bound">x</a> <a id="16235" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="16237" href="foundation.commuting-squares-of-identifications.html#16200" class="Bound">z</a><a id="16238" class="Symbol">)</a> <a id="16240" class="Symbol">(</a><a id="16241" href="foundation.commuting-squares-of-identifications.html#16241" class="Bound">right</a> <a id="16247" class="Symbol">:</a> <a id="16249" href="foundation.commuting-squares-of-identifications.html#16198" class="Bound">y</a> <a id="16251" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="16253" href="foundation.commuting-squares-of-identifications.html#16202" class="Bound">w</a><a id="16254" class="Symbol">)</a> <a id="16256" class="Symbol">(</a><a id="16257" href="foundation.commuting-squares-of-identifications.html#16257" class="Bound">bottom</a> <a id="16264" class="Symbol">:</a> <a id="16266" href="foundation.commuting-squares-of-identifications.html#16200" class="Bound">z</a> <a id="16268" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="16270" href="foundation.commuting-squares-of-identifications.html#16202" class="Bound">w</a><a id="16271" class="Symbol">)</a>
  <a id="16275" class="Keyword">where</a>

  <a id="16284" href="foundation.commuting-squares-of-identifications.html#16284" class="Function">equiv-left-splice-coherence-square-identifications</a> <a id="16335" class="Symbol">:</a>
    <a id="16341" class="Symbol">{</a><a id="16342" href="foundation.commuting-squares-of-identifications.html#16342" class="Bound">u</a> <a id="16344" class="Symbol">:</a> <a id="16346" href="foundation.commuting-squares-of-identifications.html#16185" class="Bound">A</a><a id="16347" class="Symbol">}</a> <a id="16349" class="Symbol">(</a><a id="16350" href="foundation.commuting-squares-of-identifications.html#16350" class="Bound">p</a> <a id="16352" class="Symbol">:</a> <a id="16354" href="foundation.commuting-squares-of-identifications.html#16200" class="Bound">z</a> <a id="16356" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="16358" href="foundation.commuting-squares-of-identifications.html#16342" class="Bound">u</a><a id="16359" class="Symbol">)</a> <a id="16361" class="Symbol">(</a><a id="16362" href="foundation.commuting-squares-of-identifications.html#16362" class="Bound">q</a> <a id="16364" class="Symbol">:</a> <a id="16366" href="foundation.commuting-squares-of-identifications.html#16342" class="Bound">u</a> <a id="16368" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="16370" href="foundation.commuting-squares-of-identifications.html#16200" class="Bound">z</a><a id="16371" class="Symbol">)</a> <a id="16373" class="Symbol">(</a><a id="16374" href="foundation.commuting-squares-of-identifications.html#16374" class="Bound">α</a> <a id="16376" class="Symbol">:</a> <a id="16378" href="foundation-core.identity-types.html#6168" class="Function">inv</a> <a id="16382" href="foundation.commuting-squares-of-identifications.html#16350" class="Bound">p</a> <a id="16384" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="16386" href="foundation.commuting-squares-of-identifications.html#16362" class="Bound">q</a><a id="16387" class="Symbol">)</a> <a id="16389" class="Symbol">→</a>
    <a id="16395" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="16428" href="foundation.commuting-squares-of-identifications.html#16212" class="Bound">top</a> <a id="16432" href="foundation.commuting-squares-of-identifications.html#16226" class="Bound">left</a> <a id="16437" href="foundation.commuting-squares-of-identifications.html#16241" class="Bound">right</a> <a id="16443" href="foundation.commuting-squares-of-identifications.html#16257" class="Bound">bottom</a> <a id="16450" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="16456" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="16489" href="foundation.commuting-squares-of-identifications.html#16212" class="Bound">top</a> <a id="16493" class="Symbol">(</a><a id="16494" href="foundation.commuting-squares-of-identifications.html#16226" class="Bound">left</a> <a id="16499" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="16501" href="foundation.commuting-squares-of-identifications.html#16350" class="Bound">p</a><a id="16502" class="Symbol">)</a> <a id="16504" href="foundation.commuting-squares-of-identifications.html#16241" class="Bound">right</a> <a id="16510" class="Symbol">(</a><a id="16511" href="foundation.commuting-squares-of-identifications.html#16362" class="Bound">q</a> <a id="16513" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="16515" href="foundation.commuting-squares-of-identifications.html#16257" class="Bound">bottom</a><a id="16521" class="Symbol">)</a>
  <a id="16525" href="foundation.commuting-squares-of-identifications.html#16284" class="Function">equiv-left-splice-coherence-square-identifications</a> <a id="16576" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="16581" class="DottedPattern Symbol">.</a><a id="16582" href="foundation-core.identity-types.html#2682" class="DottedPattern InductiveConstructor">refl</a> <a id="16587" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="16592" class="Symbol">=</a>
    <a id="16598" href="foundation.commuting-squares-of-identifications.html#5349" class="Function">equiv-concat-left-identification-coherence-square-identifications</a>
      <a id="16670" class="Symbol">(</a> <a id="16672" href="foundation.commuting-squares-of-identifications.html#16212" class="Bound">top</a><a id="16675" class="Symbol">)</a>
      <a id="16683" class="Symbol">(</a> <a id="16685" href="foundation.commuting-squares-of-identifications.html#16226" class="Bound">left</a><a id="16689" class="Symbol">)</a>
      <a id="16697" class="Symbol">(</a> <a id="16699" href="foundation.commuting-squares-of-identifications.html#16241" class="Bound">right</a><a id="16704" class="Symbol">)</a>
      <a id="16712" class="Symbol">(</a> <a id="16714" href="foundation.commuting-squares-of-identifications.html#16257" class="Bound">bottom</a><a id="16720" class="Symbol">)</a>
      <a id="16728" class="Symbol">(</a> <a id="16730" href="foundation-core.identity-types.html#6168" class="Function">inv</a> <a id="16734" href="foundation-core.identity-types.html#8258" class="Function">right-unit</a><a id="16744" class="Symbol">)</a>
</pre>
#### Right splicing coherences of commuting squares of identifications

For any inverse pair of identifications `p : y ＝ u` and `q : u ＝ y` equipped
with `α : inv p ＝ q` we obtain an equivalence

```text
           top                             top ∙ p
       x -------> y                     x --------> u
       |          |                     |           |
  left |          | right    ≃     left |           | q ∙ right
       ∨          ∨                     ∨           ∨
       z -------> w                     z --------> w
          bottom                           bottom
```

of coherences of commuting squares of identifications.

<pre class="Agda"><a id="17405" class="Keyword">module</a> <a id="17412" href="foundation.commuting-squares-of-identifications.html#17412" class="Module">_</a>
  <a id="17416" class="Symbol">{</a><a id="17417" href="foundation.commuting-squares-of-identifications.html#17417" class="Bound">l</a> <a id="17419" class="Symbol">:</a> <a id="17421" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="17426" class="Symbol">}</a> <a id="17428" class="Symbol">{</a><a id="17429" href="foundation.commuting-squares-of-identifications.html#17429" class="Bound">A</a> <a id="17431" class="Symbol">:</a> <a id="17433" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="17436" href="foundation.commuting-squares-of-identifications.html#17417" class="Bound">l</a><a id="17437" class="Symbol">}</a> <a id="17439" class="Symbol">{</a><a id="17440" href="foundation.commuting-squares-of-identifications.html#17440" class="Bound">x</a> <a id="17442" href="foundation.commuting-squares-of-identifications.html#17442" class="Bound">y</a> <a id="17444" href="foundation.commuting-squares-of-identifications.html#17444" class="Bound">z</a> <a id="17446" href="foundation.commuting-squares-of-identifications.html#17446" class="Bound">w</a> <a id="17448" class="Symbol">:</a> <a id="17450" href="foundation.commuting-squares-of-identifications.html#17429" class="Bound">A</a><a id="17451" class="Symbol">}</a>
  <a id="17455" class="Symbol">(</a><a id="17456" href="foundation.commuting-squares-of-identifications.html#17456" class="Bound">top</a> <a id="17460" class="Symbol">:</a> <a id="17462" href="foundation.commuting-squares-of-identifications.html#17440" class="Bound">x</a> <a id="17464" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="17466" href="foundation.commuting-squares-of-identifications.html#17442" class="Bound">y</a><a id="17467" class="Symbol">)</a> <a id="17469" class="Symbol">(</a><a id="17470" href="foundation.commuting-squares-of-identifications.html#17470" class="Bound">left</a> <a id="17475" class="Symbol">:</a> <a id="17477" href="foundation.commuting-squares-of-identifications.html#17440" class="Bound">x</a> <a id="17479" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="17481" href="foundation.commuting-squares-of-identifications.html#17444" class="Bound">z</a><a id="17482" class="Symbol">)</a> <a id="17484" class="Symbol">(</a><a id="17485" href="foundation.commuting-squares-of-identifications.html#17485" class="Bound">right</a> <a id="17491" class="Symbol">:</a> <a id="17493" href="foundation.commuting-squares-of-identifications.html#17442" class="Bound">y</a> <a id="17495" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="17497" href="foundation.commuting-squares-of-identifications.html#17446" class="Bound">w</a><a id="17498" class="Symbol">)</a> <a id="17500" class="Symbol">(</a><a id="17501" href="foundation.commuting-squares-of-identifications.html#17501" class="Bound">bottom</a> <a id="17508" class="Symbol">:</a> <a id="17510" href="foundation.commuting-squares-of-identifications.html#17444" class="Bound">z</a> <a id="17512" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="17514" href="foundation.commuting-squares-of-identifications.html#17446" class="Bound">w</a><a id="17515" class="Symbol">)</a>
  <a id="17519" class="Keyword">where</a>

  <a id="17528" href="foundation.commuting-squares-of-identifications.html#17528" class="Function">equiv-right-splice-coherence-square-identifications</a> <a id="17580" class="Symbol">:</a>
    <a id="17586" class="Symbol">{</a><a id="17587" href="foundation.commuting-squares-of-identifications.html#17587" class="Bound">u</a> <a id="17589" class="Symbol">:</a> <a id="17591" href="foundation.commuting-squares-of-identifications.html#17429" class="Bound">A</a><a id="17592" class="Symbol">}</a> <a id="17594" class="Symbol">(</a><a id="17595" href="foundation.commuting-squares-of-identifications.html#17595" class="Bound">p</a> <a id="17597" class="Symbol">:</a> <a id="17599" href="foundation.commuting-squares-of-identifications.html#17442" class="Bound">y</a> <a id="17601" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="17603" href="foundation.commuting-squares-of-identifications.html#17587" class="Bound">u</a><a id="17604" class="Symbol">)</a> <a id="17606" class="Symbol">(</a><a id="17607" href="foundation.commuting-squares-of-identifications.html#17607" class="Bound">q</a> <a id="17609" class="Symbol">:</a> <a id="17611" href="foundation.commuting-squares-of-identifications.html#17587" class="Bound">u</a> <a id="17613" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="17615" href="foundation.commuting-squares-of-identifications.html#17442" class="Bound">y</a><a id="17616" class="Symbol">)</a> <a id="17618" class="Symbol">(</a><a id="17619" href="foundation.commuting-squares-of-identifications.html#17619" class="Bound">α</a> <a id="17621" class="Symbol">:</a> <a id="17623" href="foundation-core.identity-types.html#6168" class="Function">inv</a> <a id="17627" href="foundation.commuting-squares-of-identifications.html#17595" class="Bound">p</a> <a id="17629" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="17631" href="foundation.commuting-squares-of-identifications.html#17607" class="Bound">q</a><a id="17632" class="Symbol">)</a> <a id="17634" class="Symbol">→</a>
    <a id="17640" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="17673" href="foundation.commuting-squares-of-identifications.html#17456" class="Bound">top</a> <a id="17677" href="foundation.commuting-squares-of-identifications.html#17470" class="Bound">left</a> <a id="17682" href="foundation.commuting-squares-of-identifications.html#17485" class="Bound">right</a> <a id="17688" href="foundation.commuting-squares-of-identifications.html#17501" class="Bound">bottom</a> <a id="17695" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="17701" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="17734" class="Symbol">(</a><a id="17735" href="foundation.commuting-squares-of-identifications.html#17456" class="Bound">top</a> <a id="17739" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="17741" href="foundation.commuting-squares-of-identifications.html#17595" class="Bound">p</a><a id="17742" class="Symbol">)</a> <a id="17744" href="foundation.commuting-squares-of-identifications.html#17470" class="Bound">left</a> <a id="17749" class="Symbol">(</a><a id="17750" href="foundation-core.identity-types.html#6168" class="Function">inv</a> <a id="17754" href="foundation.commuting-squares-of-identifications.html#17595" class="Bound">p</a> <a id="17756" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="17758" href="foundation.commuting-squares-of-identifications.html#17485" class="Bound">right</a><a id="17763" class="Symbol">)</a> <a id="17765" href="foundation.commuting-squares-of-identifications.html#17501" class="Bound">bottom</a>
  <a id="17774" href="foundation.commuting-squares-of-identifications.html#17528" class="Function">equiv-right-splice-coherence-square-identifications</a> <a id="17826" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="17831" class="DottedPattern Symbol">.</a><a id="17832" href="foundation-core.identity-types.html#2682" class="DottedPattern InductiveConstructor">refl</a> <a id="17837" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="17842" class="Symbol">=</a>
    <a id="17848" href="foundation.commuting-squares-of-identifications.html#3229" class="Function">equiv-concat-top-identification-coherence-square-identifications</a>
      <a id="17919" class="Symbol">(</a> <a id="17921" href="foundation.commuting-squares-of-identifications.html#17456" class="Bound">top</a><a id="17924" class="Symbol">)</a>
      <a id="17932" class="Symbol">(</a> <a id="17934" href="foundation.commuting-squares-of-identifications.html#17470" class="Bound">left</a><a id="17938" class="Symbol">)</a>
      <a id="17946" class="Symbol">(</a> <a id="17948" href="foundation.commuting-squares-of-identifications.html#17485" class="Bound">right</a><a id="17953" class="Symbol">)</a>
      <a id="17961" class="Symbol">(</a> <a id="17963" href="foundation.commuting-squares-of-identifications.html#17501" class="Bound">bottom</a><a id="17969" class="Symbol">)</a>
      <a id="17977" class="Symbol">(</a> <a id="17979" href="foundation-core.identity-types.html#6168" class="Function">inv</a> <a id="17983" href="foundation-core.identity-types.html#8258" class="Function">right-unit</a><a id="17993" class="Symbol">)</a>
</pre>
### Double whiskering of commuting squares of identifications

<pre class="Agda"><a id="18071" class="Keyword">module</a> <a id="18078" href="foundation.commuting-squares-of-identifications.html#18078" class="Module">_</a>
  <a id="18082" class="Symbol">{</a><a id="18083" href="foundation.commuting-squares-of-identifications.html#18083" class="Bound">l</a> <a id="18085" class="Symbol">:</a> <a id="18087" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="18092" class="Symbol">}</a> <a id="18094" class="Symbol">{</a><a id="18095" href="foundation.commuting-squares-of-identifications.html#18095" class="Bound">A</a> <a id="18097" class="Symbol">:</a> <a id="18099" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="18102" href="foundation.commuting-squares-of-identifications.html#18083" class="Bound">l</a><a id="18103" class="Symbol">}</a> <a id="18105" class="Symbol">{</a><a id="18106" href="foundation.commuting-squares-of-identifications.html#18106" class="Bound">x</a> <a id="18108" href="foundation.commuting-squares-of-identifications.html#18108" class="Bound">y</a> <a id="18110" href="foundation.commuting-squares-of-identifications.html#18110" class="Bound">z</a> <a id="18112" href="foundation.commuting-squares-of-identifications.html#18112" class="Bound">u</a> <a id="18114" href="foundation.commuting-squares-of-identifications.html#18114" class="Bound">v</a> <a id="18116" href="foundation.commuting-squares-of-identifications.html#18116" class="Bound">w</a> <a id="18118" class="Symbol">:</a> <a id="18120" href="foundation.commuting-squares-of-identifications.html#18095" class="Bound">A</a><a id="18121" class="Symbol">}</a>
  <a id="18125" class="Keyword">where</a>

  <a id="18134" href="foundation.commuting-squares-of-identifications.html#18134" class="Function">equiv-double-whisker-coherence-square-identifications</a> <a id="18188" class="Symbol">:</a>
    <a id="18194" class="Symbol">(</a><a id="18195" href="foundation.commuting-squares-of-identifications.html#18195" class="Bound">p</a> <a id="18197" class="Symbol">:</a> <a id="18199" href="foundation.commuting-squares-of-identifications.html#18106" class="Bound">x</a> <a id="18201" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="18203" href="foundation.commuting-squares-of-identifications.html#18108" class="Bound">y</a><a id="18204" class="Symbol">)</a>
    <a id="18210" class="Symbol">(</a><a id="18211" href="foundation.commuting-squares-of-identifications.html#18211" class="Bound">top</a> <a id="18215" class="Symbol">:</a> <a id="18217" href="foundation.commuting-squares-of-identifications.html#18108" class="Bound">y</a> <a id="18219" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="18221" href="foundation.commuting-squares-of-identifications.html#18112" class="Bound">u</a><a id="18222" class="Symbol">)</a> <a id="18224" class="Symbol">(</a><a id="18225" href="foundation.commuting-squares-of-identifications.html#18225" class="Bound">left</a> <a id="18230" class="Symbol">:</a> <a id="18232" href="foundation.commuting-squares-of-identifications.html#18108" class="Bound">y</a> <a id="18234" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="18236" href="foundation.commuting-squares-of-identifications.html#18110" class="Bound">z</a><a id="18237" class="Symbol">)</a> <a id="18239" class="Symbol">(</a><a id="18240" href="foundation.commuting-squares-of-identifications.html#18240" class="Bound">right</a> <a id="18246" class="Symbol">:</a> <a id="18248" href="foundation.commuting-squares-of-identifications.html#18112" class="Bound">u</a> <a id="18250" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="18252" href="foundation.commuting-squares-of-identifications.html#18114" class="Bound">v</a><a id="18253" class="Symbol">)</a> <a id="18255" class="Symbol">(</a><a id="18256" href="foundation.commuting-squares-of-identifications.html#18256" class="Bound">bottom</a> <a id="18263" class="Symbol">:</a> <a id="18265" href="foundation.commuting-squares-of-identifications.html#18110" class="Bound">z</a> <a id="18267" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="18269" href="foundation.commuting-squares-of-identifications.html#18114" class="Bound">v</a><a id="18270" class="Symbol">)</a>
    <a id="18276" class="Symbol">(</a><a id="18277" href="foundation.commuting-squares-of-identifications.html#18277" class="Bound">s</a> <a id="18279" class="Symbol">:</a> <a id="18281" href="foundation.commuting-squares-of-identifications.html#18114" class="Bound">v</a> <a id="18283" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="18285" href="foundation.commuting-squares-of-identifications.html#18116" class="Bound">w</a><a id="18286" class="Symbol">)</a> <a id="18288" class="Symbol">→</a>
    <a id="18294" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="18327" href="foundation.commuting-squares-of-identifications.html#18211" class="Bound">top</a> <a id="18331" href="foundation.commuting-squares-of-identifications.html#18225" class="Bound">left</a> <a id="18336" href="foundation.commuting-squares-of-identifications.html#18240" class="Bound">right</a> <a id="18342" href="foundation.commuting-squares-of-identifications.html#18256" class="Bound">bottom</a> <a id="18349" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="18355" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a>
      <a id="18394" class="Symbol">(</a> <a id="18396" href="foundation.commuting-squares-of-identifications.html#18195" class="Bound">p</a> <a id="18398" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="18400" href="foundation.commuting-squares-of-identifications.html#18211" class="Bound">top</a><a id="18403" class="Symbol">)</a>
      <a id="18411" class="Symbol">(</a> <a id="18413" href="foundation.commuting-squares-of-identifications.html#18195" class="Bound">p</a> <a id="18415" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="18417" href="foundation.commuting-squares-of-identifications.html#18225" class="Bound">left</a><a id="18421" class="Symbol">)</a>
      <a id="18429" class="Symbol">(</a> <a id="18431" href="foundation.commuting-squares-of-identifications.html#18240" class="Bound">right</a> <a id="18437" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="18439" href="foundation.commuting-squares-of-identifications.html#18277" class="Bound">s</a><a id="18440" class="Symbol">)</a>
      <a id="18448" class="Symbol">(</a> <a id="18450" href="foundation.commuting-squares-of-identifications.html#18256" class="Bound">bottom</a> <a id="18457" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="18459" href="foundation.commuting-squares-of-identifications.html#18277" class="Bound">s</a><a id="18460" class="Symbol">)</a>
  <a id="18464" href="foundation.commuting-squares-of-identifications.html#18134" class="Function">equiv-double-whisker-coherence-square-identifications</a>
    <a id="18522" href="foundation.commuting-squares-of-identifications.html#18522" class="Bound">p</a> <a id="18524" href="foundation.commuting-squares-of-identifications.html#18524" class="Bound">top</a> <a id="18528" href="foundation.commuting-squares-of-identifications.html#18528" class="Bound">left</a> <a id="18533" href="foundation.commuting-squares-of-identifications.html#18533" class="Bound">right</a> <a id="18539" href="foundation.commuting-squares-of-identifications.html#18539" class="Bound">bottom</a> <a id="18546" href="foundation.commuting-squares-of-identifications.html#18546" class="Bound">q</a> <a id="18548" class="Symbol">=</a>
    <a id="18554" href="foundation.commuting-squares-of-identifications.html#13720" class="Function">equiv-left-whisker-concat-coherence-square-identifications</a> <a id="18613" href="foundation.commuting-squares-of-identifications.html#18522" class="Bound">p</a> <a id="18615" href="foundation.commuting-squares-of-identifications.html#18524" class="Bound">top</a> <a id="18619" href="foundation.commuting-squares-of-identifications.html#18528" class="Bound">left</a>
      <a id="18630" class="Symbol">(</a> <a id="18632" href="foundation.commuting-squares-of-identifications.html#18533" class="Bound">right</a> <a id="18638" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="18640" href="foundation.commuting-squares-of-identifications.html#18546" class="Bound">q</a><a id="18641" class="Symbol">)</a>
      <a id="18649" class="Symbol">(</a> <a id="18651" href="foundation.commuting-squares-of-identifications.html#18539" class="Bound">bottom</a> <a id="18658" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="18660" href="foundation.commuting-squares-of-identifications.html#18546" class="Bound">q</a><a id="18661" class="Symbol">)</a> <a id="18663" href="foundation-core.equivalences.html#13323" class="Function Operator">∘e</a>
    <a id="18670" href="foundation.commuting-squares-of-identifications.html#14849" class="Function">equiv-right-whisker-concat-coherence-square-identifications</a>
      <a id="18736" class="Symbol">(</a> <a id="18738" href="foundation.commuting-squares-of-identifications.html#18524" class="Bound">top</a><a id="18741" class="Symbol">)</a>
      <a id="18749" class="Symbol">(</a> <a id="18751" href="foundation.commuting-squares-of-identifications.html#18528" class="Bound">left</a><a id="18755" class="Symbol">)</a>
      <a id="18763" class="Symbol">(</a> <a id="18765" href="foundation.commuting-squares-of-identifications.html#18533" class="Bound">right</a><a id="18770" class="Symbol">)</a>
      <a id="18778" class="Symbol">(</a> <a id="18780" href="foundation.commuting-squares-of-identifications.html#18539" class="Bound">bottom</a><a id="18786" class="Symbol">)</a>
      <a id="18794" class="Symbol">(</a> <a id="18796" href="foundation.commuting-squares-of-identifications.html#18546" class="Bound">q</a><a id="18797" class="Symbol">)</a>
</pre>
### Computing the pasting of squares with `refl` on opposite sides

Consider two squares of identifications as in the diagram

```text
                  refl
              a --------> a
              |           |
     top-left |           | top-right
              ∨   refl    ∨
              b --------> b
              |           |
  bottom-left |           | bottom-right
              ∨           ∨
              c --------> c
                  refl
```

Then the pasted square can be computed in terms of the horizontal concatenation
of the filler squares

<pre class="Agda"><a id="19376" class="Keyword">module</a> <a id="19383" href="foundation.commuting-squares-of-identifications.html#19383" class="Module">_</a>
  <a id="19387" class="Symbol">{</a><a id="19388" href="foundation.commuting-squares-of-identifications.html#19388" class="Bound">l</a> <a id="19390" class="Symbol">:</a> <a id="19392" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="19397" class="Symbol">}</a> <a id="19399" class="Symbol">{</a><a id="19400" href="foundation.commuting-squares-of-identifications.html#19400" class="Bound">A</a> <a id="19402" class="Symbol">:</a> <a id="19404" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="19407" href="foundation.commuting-squares-of-identifications.html#19388" class="Bound">l</a><a id="19408" class="Symbol">}</a> <a id="19410" class="Symbol">{</a><a id="19411" href="foundation.commuting-squares-of-identifications.html#19411" class="Bound">a</a> <a id="19413" href="foundation.commuting-squares-of-identifications.html#19413" class="Bound">b</a> <a id="19415" href="foundation.commuting-squares-of-identifications.html#19415" class="Bound">c</a> <a id="19417" class="Symbol">:</a> <a id="19419" href="foundation.commuting-squares-of-identifications.html#19400" class="Bound">A</a><a id="19420" class="Symbol">}</a>
  <a id="19424" class="Keyword">where</a>

  <a id="19433" href="foundation.commuting-squares-of-identifications.html#19433" class="Function">vertical-pasting-coherence-square-identifications-horizontal-refl</a> <a id="19499" class="Symbol">:</a>
    <a id="19505" class="Symbol">(</a><a id="19506" href="foundation.commuting-squares-of-identifications.html#19506" class="Bound">top-left</a> <a id="19515" class="Symbol">:</a> <a id="19517" href="foundation.commuting-squares-of-identifications.html#19411" class="Bound">a</a> <a id="19519" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="19521" href="foundation.commuting-squares-of-identifications.html#19413" class="Bound">b</a><a id="19522" class="Symbol">)</a> <a id="19524" class="Symbol">(</a><a id="19525" href="foundation.commuting-squares-of-identifications.html#19525" class="Bound">top-right</a> <a id="19535" class="Symbol">:</a> <a id="19537" href="foundation.commuting-squares-of-identifications.html#19411" class="Bound">a</a> <a id="19539" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="19541" href="foundation.commuting-squares-of-identifications.html#19413" class="Bound">b</a><a id="19542" class="Symbol">)</a>
    <a id="19548" class="Symbol">(</a><a id="19549" href="foundation.commuting-squares-of-identifications.html#19549" class="Bound">bottom-left</a> <a id="19561" class="Symbol">:</a> <a id="19563" href="foundation.commuting-squares-of-identifications.html#19413" class="Bound">b</a> <a id="19565" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="19567" href="foundation.commuting-squares-of-identifications.html#19415" class="Bound">c</a><a id="19568" class="Symbol">)</a> <a id="19570" class="Symbol">(</a><a id="19571" href="foundation.commuting-squares-of-identifications.html#19571" class="Bound">bottom-right</a> <a id="19584" class="Symbol">:</a> <a id="19586" href="foundation.commuting-squares-of-identifications.html#19413" class="Bound">b</a> <a id="19588" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="19590" href="foundation.commuting-squares-of-identifications.html#19415" class="Bound">c</a><a id="19591" class="Symbol">)</a>
    <a id="19597" class="Symbol">(</a><a id="19598" href="foundation.commuting-squares-of-identifications.html#19598" class="Bound">α</a> <a id="19600" class="Symbol">:</a> <a id="19602" href="foundation.commuting-squares-of-identifications.html#19506" class="Bound">top-left</a> <a id="19611" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="19613" href="foundation.commuting-squares-of-identifications.html#19525" class="Bound">top-right</a><a id="19622" class="Symbol">)</a> <a id="19624" class="Symbol">(</a><a id="19625" href="foundation.commuting-squares-of-identifications.html#19625" class="Bound">β</a> <a id="19627" class="Symbol">:</a> <a id="19629" href="foundation.commuting-squares-of-identifications.html#19549" class="Bound">bottom-left</a> <a id="19641" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="19643" href="foundation.commuting-squares-of-identifications.html#19571" class="Bound">bottom-right</a><a id="19655" class="Symbol">)</a> <a id="19657" class="Symbol">→</a>
    <a id="19663" class="Symbol">(</a> <a id="19665" href="foundation-core.commuting-squares-of-identifications.html#3253" class="Function">inv-coherence-square-identifications-horizontal-refl</a>
      <a id="19724" class="Symbol">(</a> <a id="19726" href="foundation.commuting-squares-of-identifications.html#19506" class="Bound">top-left</a> <a id="19735" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="19737" href="foundation.commuting-squares-of-identifications.html#19549" class="Bound">bottom-left</a><a id="19748" class="Symbol">)</a>
      <a id="19756" class="Symbol">(</a> <a id="19758" href="foundation.commuting-squares-of-identifications.html#19525" class="Bound">top-right</a> <a id="19768" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="19770" href="foundation.commuting-squares-of-identifications.html#19571" class="Bound">bottom-right</a><a id="19782" class="Symbol">)</a>
      <a id="19790" class="Symbol">(</a> <a id="19792" href="foundation-core.commuting-squares-of-identifications.html#30587" class="Function">vertical-pasting-coherence-square-identifications</a>
        <a id="19850" class="Symbol">(</a> <a id="19852" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="19856" class="Symbol">)</a>
        <a id="19866" class="Symbol">(</a> <a id="19868" href="foundation.commuting-squares-of-identifications.html#19506" class="Bound">top-left</a><a id="19876" class="Symbol">)</a>
        <a id="19886" class="Symbol">(</a> <a id="19888" href="foundation.commuting-squares-of-identifications.html#19525" class="Bound">top-right</a><a id="19897" class="Symbol">)</a>
        <a id="19907" class="Symbol">(</a> <a id="19909" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="19913" class="Symbol">)</a>
        <a id="19923" class="Symbol">(</a> <a id="19925" href="foundation.commuting-squares-of-identifications.html#19549" class="Bound">bottom-left</a><a id="19936" class="Symbol">)</a>
        <a id="19946" class="Symbol">(</a> <a id="19948" href="foundation.commuting-squares-of-identifications.html#19571" class="Bound">bottom-right</a><a id="19960" class="Symbol">)</a>
        <a id="19970" class="Symbol">(</a> <a id="19972" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="19976" class="Symbol">)</a>
        <a id="19986" class="Symbol">(</a> <a id="19988" href="foundation-core.commuting-squares-of-identifications.html#2931" class="Function">coherence-square-identifications-horizontal-refl</a>
          <a id="20047" class="Symbol">(</a> <a id="20049" href="foundation.commuting-squares-of-identifications.html#19506" class="Bound">top-left</a><a id="20057" class="Symbol">)</a>
          <a id="20069" class="Symbol">(</a> <a id="20071" href="foundation.commuting-squares-of-identifications.html#19525" class="Bound">top-right</a><a id="20080" class="Symbol">)</a>
          <a id="20092" class="Symbol">(</a> <a id="20094" href="foundation.commuting-squares-of-identifications.html#19598" class="Bound">α</a><a id="20095" class="Symbol">))</a>
        <a id="20106" class="Symbol">(</a> <a id="20108" href="foundation-core.commuting-squares-of-identifications.html#2931" class="Function">coherence-square-identifications-horizontal-refl</a>
          <a id="20167" class="Symbol">(</a> <a id="20169" href="foundation.commuting-squares-of-identifications.html#19549" class="Bound">bottom-left</a><a id="20180" class="Symbol">)</a>
          <a id="20192" class="Symbol">(</a> <a id="20194" href="foundation.commuting-squares-of-identifications.html#19571" class="Bound">bottom-right</a><a id="20206" class="Symbol">)</a>
          <a id="20218" class="Symbol">(</a> <a id="20220" href="foundation.commuting-squares-of-identifications.html#19625" class="Bound">β</a><a id="20221" class="Symbol">))))</a> <a id="20226" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
      <a id="20234" class="Symbol">(</a> <a id="20236" href="foundation.path-algebra.html#4339" class="Function">horizontal-concat-Id²</a> <a id="20258" href="foundation.commuting-squares-of-identifications.html#19598" class="Bound">α</a> <a id="20260" href="foundation.commuting-squares-of-identifications.html#19625" class="Bound">β</a><a id="20261" class="Symbol">)</a>
  <a id="20265" href="foundation.commuting-squares-of-identifications.html#19433" class="Function">vertical-pasting-coherence-square-identifications-horizontal-refl</a>
    <a id="20335" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="20340" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="20345" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="20350" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="20355" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="20360" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="20365" class="Symbol">=</a>
      <a id="20373" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

  <a id="20381" href="foundation.commuting-squares-of-identifications.html#20381" class="Function">vertical-pasting-inv-coherence-square-identifications-horizontal-refl</a> <a id="20451" class="Symbol">:</a>
    <a id="20457" class="Symbol">(</a><a id="20458" href="foundation.commuting-squares-of-identifications.html#20458" class="Bound">top-left</a> <a id="20467" class="Symbol">:</a> <a id="20469" href="foundation.commuting-squares-of-identifications.html#19411" class="Bound">a</a> <a id="20471" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="20473" href="foundation.commuting-squares-of-identifications.html#19413" class="Bound">b</a><a id="20474" class="Symbol">)</a> <a id="20476" class="Symbol">(</a><a id="20477" href="foundation.commuting-squares-of-identifications.html#20477" class="Bound">top-right</a> <a id="20487" class="Symbol">:</a> <a id="20489" href="foundation.commuting-squares-of-identifications.html#19411" class="Bound">a</a> <a id="20491" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="20493" href="foundation.commuting-squares-of-identifications.html#19413" class="Bound">b</a><a id="20494" class="Symbol">)</a>
    <a id="20500" class="Symbol">(</a><a id="20501" href="foundation.commuting-squares-of-identifications.html#20501" class="Bound">bottom-left</a> <a id="20513" class="Symbol">:</a> <a id="20515" href="foundation.commuting-squares-of-identifications.html#19413" class="Bound">b</a> <a id="20517" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="20519" href="foundation.commuting-squares-of-identifications.html#19415" class="Bound">c</a><a id="20520" class="Symbol">)</a> <a id="20522" class="Symbol">(</a><a id="20523" href="foundation.commuting-squares-of-identifications.html#20523" class="Bound">bottom-right</a> <a id="20536" class="Symbol">:</a> <a id="20538" href="foundation.commuting-squares-of-identifications.html#19413" class="Bound">b</a> <a id="20540" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="20542" href="foundation.commuting-squares-of-identifications.html#19415" class="Bound">c</a><a id="20543" class="Symbol">)</a>
    <a id="20549" class="Symbol">(</a><a id="20550" href="foundation.commuting-squares-of-identifications.html#20550" class="Bound">α</a> <a id="20552" class="Symbol">:</a> <a id="20554" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="20587" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="20592" href="foundation.commuting-squares-of-identifications.html#20458" class="Bound">top-left</a> <a id="20601" href="foundation.commuting-squares-of-identifications.html#20477" class="Bound">top-right</a> <a id="20611" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="20615" class="Symbol">)</a>
    <a id="20621" class="Symbol">(</a><a id="20622" href="foundation.commuting-squares-of-identifications.html#20622" class="Bound">β</a> <a id="20624" class="Symbol">:</a> <a id="20626" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a> <a id="20659" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="20664" href="foundation.commuting-squares-of-identifications.html#20501" class="Bound">bottom-left</a> <a id="20676" href="foundation.commuting-squares-of-identifications.html#20523" class="Bound">bottom-right</a> <a id="20689" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="20693" class="Symbol">)</a> <a id="20695" class="Symbol">→</a>
    <a id="20701" class="Symbol">(</a> <a id="20703" href="foundation-core.commuting-squares-of-identifications.html#3253" class="Function">inv-coherence-square-identifications-horizontal-refl</a>
      <a id="20762" class="Symbol">(</a> <a id="20764" href="foundation.commuting-squares-of-identifications.html#20458" class="Bound">top-left</a> <a id="20773" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="20775" href="foundation.commuting-squares-of-identifications.html#20501" class="Bound">bottom-left</a><a id="20786" class="Symbol">)</a>
      <a id="20794" class="Symbol">(</a> <a id="20796" href="foundation.commuting-squares-of-identifications.html#20477" class="Bound">top-right</a> <a id="20806" href="foundation-core.identity-types.html#5864" class="Function Operator">∙</a> <a id="20808" href="foundation.commuting-squares-of-identifications.html#20523" class="Bound">bottom-right</a><a id="20820" class="Symbol">)</a>
      <a id="20828" class="Symbol">(</a> <a id="20830" href="foundation-core.commuting-squares-of-identifications.html#30587" class="Function">vertical-pasting-coherence-square-identifications</a>
        <a id="20888" class="Symbol">(</a> <a id="20890" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="20894" class="Symbol">)</a>
        <a id="20904" class="Symbol">(</a> <a id="20906" href="foundation.commuting-squares-of-identifications.html#20458" class="Bound">top-left</a><a id="20914" class="Symbol">)</a>
        <a id="20924" class="Symbol">(</a> <a id="20926" href="foundation.commuting-squares-of-identifications.html#20477" class="Bound">top-right</a><a id="20935" class="Symbol">)</a>
        <a id="20945" class="Symbol">(</a> <a id="20947" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="20951" class="Symbol">)</a>
        <a id="20961" class="Symbol">(</a> <a id="20963" href="foundation.commuting-squares-of-identifications.html#20501" class="Bound">bottom-left</a><a id="20974" class="Symbol">)</a>
        <a id="20984" class="Symbol">(</a> <a id="20986" href="foundation.commuting-squares-of-identifications.html#20523" class="Bound">bottom-right</a><a id="20998" class="Symbol">)</a>
        <a id="21008" class="Symbol">(</a> <a id="21010" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="21014" class="Symbol">)</a>
        <a id="21024" class="Symbol">(</a> <a id="21026" href="foundation.commuting-squares-of-identifications.html#20550" class="Bound">α</a><a id="21027" class="Symbol">)</a>
        <a id="21037" class="Symbol">(</a> <a id="21039" href="foundation.commuting-squares-of-identifications.html#20622" class="Bound">β</a><a id="21040" class="Symbol">)))</a> <a id="21044" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
      <a id="21052" class="Symbol">(</a> <a id="21054" href="foundation.path-algebra.html#4339" class="Function">horizontal-concat-Id²</a>
        <a id="21084" class="Symbol">(</a> <a id="21086" href="foundation-core.commuting-squares-of-identifications.html#3253" class="Function">inv-coherence-square-identifications-horizontal-refl</a>
          <a id="21149" class="Symbol">(</a> <a id="21151" href="foundation.commuting-squares-of-identifications.html#20458" class="Bound">top-left</a><a id="21159" class="Symbol">)</a>
          <a id="21171" class="Symbol">(</a> <a id="21173" href="foundation.commuting-squares-of-identifications.html#20477" class="Bound">top-right</a><a id="21182" class="Symbol">)</a>
          <a id="21194" class="Symbol">(</a> <a id="21196" href="foundation.commuting-squares-of-identifications.html#20550" class="Bound">α</a><a id="21197" class="Symbol">))</a>
        <a id="21208" class="Symbol">(</a> <a id="21210" href="foundation-core.commuting-squares-of-identifications.html#3253" class="Function">inv-coherence-square-identifications-horizontal-refl</a>
          <a id="21273" class="Symbol">(</a> <a id="21275" href="foundation.commuting-squares-of-identifications.html#20501" class="Bound">bottom-left</a><a id="21286" class="Symbol">)</a>
          <a id="21298" class="Symbol">(</a> <a id="21300" href="foundation.commuting-squares-of-identifications.html#20523" class="Bound">bottom-right</a><a id="21312" class="Symbol">)</a>
          <a id="21324" class="Symbol">(</a> <a id="21326" href="foundation.commuting-squares-of-identifications.html#20622" class="Bound">β</a><a id="21327" class="Symbol">)))</a>
  <a id="21333" href="foundation.commuting-squares-of-identifications.html#20381" class="Function">vertical-pasting-inv-coherence-square-identifications-horizontal-refl</a>
    <a id="21407" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="21412" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="21417" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="21422" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="21427" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="21432" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="21437" class="Symbol">=</a>
      <a id="21445" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>