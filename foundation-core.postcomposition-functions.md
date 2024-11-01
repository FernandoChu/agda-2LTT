# Postcomposition of functions

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="foundation-core.postcomposition-functions.html" class="Module">foundation-core.postcomposition-functions</a> <a id="90" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="146" class="Keyword">open</a> <a id="151" class="Keyword">import</a> <a id="158" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="186" class="Keyword">open</a> <a id="191" class="Keyword">import</a> <a id="198" href="foundation-core.postcomposition-dependent-functions.html" class="Module">foundation-core.postcomposition-dependent-functions</a>
</pre>
</details>

## Idea

Given a map `f : X → Y` and a type `A`, the
{{#concept "postcomposition function" Agda=postcomp}}

```text
  f ∘ - : (A → X) → (A → Y)
```

is defined by `λ h x → f (h x)`.

## Definitions

<pre class="Agda"><a id="474" class="Keyword">module</a> <a id="481" href="foundation-core.postcomposition-functions.html#481" class="Module">_</a>
  <a id="485" class="Symbol">{</a><a id="486" href="foundation-core.postcomposition-functions.html#486" class="Bound">l1</a> <a id="489" href="foundation-core.postcomposition-functions.html#489" class="Bound">l2</a> <a id="492" href="foundation-core.postcomposition-functions.html#492" class="Bound">l3</a> <a id="495" class="Symbol">:</a> <a id="497" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="502" class="Symbol">}</a> <a id="504" class="Symbol">(</a><a id="505" href="foundation-core.postcomposition-functions.html#505" class="Bound">A</a> <a id="507" class="Symbol">:</a> <a id="509" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="512" href="foundation-core.postcomposition-functions.html#486" class="Bound">l1</a><a id="514" class="Symbol">)</a> <a id="516" class="Symbol">{</a><a id="517" href="foundation-core.postcomposition-functions.html#517" class="Bound">X</a> <a id="519" class="Symbol">:</a> <a id="521" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="524" href="foundation-core.postcomposition-functions.html#489" class="Bound">l2</a><a id="526" class="Symbol">}</a> <a id="528" class="Symbol">{</a><a id="529" href="foundation-core.postcomposition-functions.html#529" class="Bound">Y</a> <a id="531" class="Symbol">:</a> <a id="533" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="536" href="foundation-core.postcomposition-functions.html#492" class="Bound">l3</a><a id="538" class="Symbol">}</a>
  <a id="542" class="Keyword">where</a>

  <a id="551" href="foundation-core.postcomposition-functions.html#551" class="Function">postcomp</a> <a id="560" class="Symbol">:</a> <a id="562" class="Symbol">(</a><a id="563" href="foundation-core.postcomposition-functions.html#517" class="Bound">X</a> <a id="565" class="Symbol">→</a> <a id="567" href="foundation-core.postcomposition-functions.html#529" class="Bound">Y</a><a id="568" class="Symbol">)</a> <a id="570" class="Symbol">→</a> <a id="572" class="Symbol">(</a><a id="573" href="foundation-core.postcomposition-functions.html#505" class="Bound">A</a> <a id="575" class="Symbol">→</a> <a id="577" href="foundation-core.postcomposition-functions.html#517" class="Bound">X</a><a id="578" class="Symbol">)</a> <a id="580" class="Symbol">→</a> <a id="582" class="Symbol">(</a><a id="583" href="foundation-core.postcomposition-functions.html#505" class="Bound">A</a> <a id="585" class="Symbol">→</a> <a id="587" href="foundation-core.postcomposition-functions.html#529" class="Bound">Y</a><a id="588" class="Symbol">)</a>
  <a id="592" href="foundation-core.postcomposition-functions.html#551" class="Function">postcomp</a> <a id="601" href="foundation-core.postcomposition-functions.html#601" class="Bound">f</a> <a id="603" class="Symbol">=</a> <a id="605" href="foundation-core.postcomposition-dependent-functions.html#1365" class="Function">postcomp-Π</a> <a id="616" href="foundation-core.postcomposition-functions.html#505" class="Bound">A</a> <a id="618" href="foundation-core.postcomposition-functions.html#601" class="Bound">f</a>
</pre>