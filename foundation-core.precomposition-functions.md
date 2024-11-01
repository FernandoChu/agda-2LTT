# Precomposition of functions

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="foundation-core.precomposition-functions.html" class="Module">foundation-core.precomposition-functions</a> <a id="88" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="144" class="Keyword">open</a> <a id="149" class="Keyword">import</a> <a id="156" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="184" class="Keyword">open</a> <a id="189" class="Keyword">import</a> <a id="196" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
</pre>
</details>

## Idea

Given a function `f : A → B` and a type `X`, the **precomposition function** by
`f`

```text
  - ∘ f : (B → X) → (A → X)
```

is defined by `λ h x → h (f x)`.

## Definitions

### The precomposition operation on ordinary functions

<pre class="Agda"><a id="493" class="Keyword">module</a> <a id="500" href="foundation-core.precomposition-functions.html#500" class="Module">_</a>
  <a id="504" class="Symbol">{</a><a id="505" href="foundation-core.precomposition-functions.html#505" class="Bound">l1</a> <a id="508" href="foundation-core.precomposition-functions.html#508" class="Bound">l2</a> <a id="511" href="foundation-core.precomposition-functions.html#511" class="Bound">l3</a> <a id="514" class="Symbol">:</a> <a id="516" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="521" class="Symbol">}</a> <a id="523" class="Symbol">{</a><a id="524" href="foundation-core.precomposition-functions.html#524" class="Bound">A</a> <a id="526" class="Symbol">:</a> <a id="528" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="531" href="foundation-core.precomposition-functions.html#505" class="Bound">l1</a><a id="533" class="Symbol">}</a> <a id="535" class="Symbol">{</a><a id="536" href="foundation-core.precomposition-functions.html#536" class="Bound">B</a> <a id="538" class="Symbol">:</a> <a id="540" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="543" href="foundation-core.precomposition-functions.html#508" class="Bound">l2</a><a id="545" class="Symbol">}</a> <a id="547" class="Symbol">(</a><a id="548" href="foundation-core.precomposition-functions.html#548" class="Bound">f</a> <a id="550" class="Symbol">:</a> <a id="552" href="foundation-core.precomposition-functions.html#524" class="Bound">A</a> <a id="554" class="Symbol">→</a> <a id="556" href="foundation-core.precomposition-functions.html#536" class="Bound">B</a><a id="557" class="Symbol">)</a> <a id="559" class="Symbol">(</a><a id="560" href="foundation-core.precomposition-functions.html#560" class="Bound">C</a> <a id="562" class="Symbol">:</a> <a id="564" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="567" href="foundation-core.precomposition-functions.html#511" class="Bound">l3</a><a id="569" class="Symbol">)</a>
  <a id="573" class="Keyword">where</a>

  <a id="582" href="foundation-core.precomposition-functions.html#582" class="Function">precomp</a> <a id="590" class="Symbol">:</a> <a id="592" class="Symbol">(</a><a id="593" href="foundation-core.precomposition-functions.html#536" class="Bound">B</a> <a id="595" class="Symbol">→</a> <a id="597" href="foundation-core.precomposition-functions.html#560" class="Bound">C</a><a id="598" class="Symbol">)</a> <a id="600" class="Symbol">→</a> <a id="602" class="Symbol">(</a><a id="603" href="foundation-core.precomposition-functions.html#524" class="Bound">A</a> <a id="605" class="Symbol">→</a> <a id="607" href="foundation-core.precomposition-functions.html#560" class="Bound">C</a><a id="608" class="Symbol">)</a>
  <a id="612" href="foundation-core.precomposition-functions.html#582" class="Function">precomp</a> <a id="620" class="Symbol">=</a> <a id="622" href="foundation-core.function-types.html#455" class="Function Operator">_∘</a> <a id="625" href="foundation-core.precomposition-functions.html#548" class="Bound">f</a>
</pre>