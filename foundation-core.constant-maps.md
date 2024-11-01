# Constant maps

<pre class="Agda"><a id="26" class="Keyword">module</a> <a id="33" href="foundation-core.constant-maps.html" class="Module">foundation-core.constant-maps</a> <a id="63" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="119" class="Keyword">open</a> <a id="124" class="Keyword">import</a> <a id="131" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The {{#concept "constant map" Agda=const}} from `A` to `B` at an element `b : B`
is the function `x ↦ b` mapping every element `x : A` to the given element
`b : B`. In common type theoretic notation, the constant map at `b` is the
function

```text
  λ x → b.
```

## Definition

<pre class="Agda"><a id="const"></a><a id="472" href="foundation-core.constant-maps.html#472" class="Function">const</a> <a id="478" class="Symbol">:</a> <a id="480" class="Symbol">{</a><a id="481" href="foundation-core.constant-maps.html#481" class="Bound">l1</a> <a id="484" href="foundation-core.constant-maps.html#484" class="Bound">l2</a> <a id="487" class="Symbol">:</a> <a id="489" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="494" class="Symbol">}</a> <a id="496" class="Symbol">(</a><a id="497" href="foundation-core.constant-maps.html#497" class="Bound">A</a> <a id="499" class="Symbol">:</a> <a id="501" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="504" href="foundation-core.constant-maps.html#481" class="Bound">l1</a><a id="506" class="Symbol">)</a> <a id="508" class="Symbol">{</a><a id="509" href="foundation-core.constant-maps.html#509" class="Bound">B</a> <a id="511" class="Symbol">:</a> <a id="513" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="516" href="foundation-core.constant-maps.html#484" class="Bound">l2</a><a id="518" class="Symbol">}</a> <a id="520" class="Symbol">→</a> <a id="522" href="foundation-core.constant-maps.html#509" class="Bound">B</a> <a id="524" class="Symbol">→</a> <a id="526" href="foundation-core.constant-maps.html#497" class="Bound">A</a> <a id="528" class="Symbol">→</a> <a id="530" href="foundation-core.constant-maps.html#509" class="Bound">B</a>
<a id="532" href="foundation-core.constant-maps.html#472" class="Function">const</a> <a id="538" href="foundation-core.constant-maps.html#538" class="Bound">A</a> <a id="540" href="foundation-core.constant-maps.html#540" class="Bound">b</a> <a id="542" href="foundation-core.constant-maps.html#542" class="Bound">x</a> <a id="544" class="Symbol">=</a> <a id="546" href="foundation-core.constant-maps.html#540" class="Bound">b</a>
</pre>
## See also

- [Constant pointed maps](structured-types.constant-pointed-maps.md)
