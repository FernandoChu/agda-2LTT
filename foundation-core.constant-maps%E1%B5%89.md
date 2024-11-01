# Constant maps

<pre class="Agda"><a id="26" class="Keyword">module</a> <a id="33" href="foundation-core.constant-maps%25E1%25B5%2589.html" class="Module">foundation-core.constant-mapsᵉ</a> <a id="64" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="120" class="Keyword">open</a> <a id="125" class="Keyword">import</a> <a id="132" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
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

<pre class="Agda"><a id="constᵉ"></a><a id="474" href="foundation-core.constant-maps%25E1%25B5%2589.html#474" class="Function">constᵉ</a> <a id="481" class="Symbol">:</a> <a id="483" class="Symbol">{</a><a id="484" href="foundation-core.constant-maps%25E1%25B5%2589.html#484" class="Bound">l1ᵉ</a> <a id="488" href="foundation-core.constant-maps%25E1%25B5%2589.html#488" class="Bound">l2ᵉ</a> <a id="492" class="Symbol">:</a> <a id="494" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="499" class="Symbol">}</a> <a id="501" class="Symbol">(</a><a id="502" href="foundation-core.constant-maps%25E1%25B5%2589.html#502" class="Bound">Aᵉ</a> <a id="505" class="Symbol">:</a> <a id="507" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="511" href="foundation-core.constant-maps%25E1%25B5%2589.html#484" class="Bound">l1ᵉ</a><a id="514" class="Symbol">)</a> <a id="516" class="Symbol">{</a><a id="517" href="foundation-core.constant-maps%25E1%25B5%2589.html#517" class="Bound">Bᵉ</a> <a id="520" class="Symbol">:</a> <a id="522" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="526" href="foundation-core.constant-maps%25E1%25B5%2589.html#488" class="Bound">l2ᵉ</a><a id="529" class="Symbol">}</a> <a id="531" class="Symbol">→</a> <a id="533" href="foundation-core.constant-maps%25E1%25B5%2589.html#517" class="Bound">Bᵉ</a> <a id="536" class="Symbol">→</a> <a id="538" href="foundation-core.constant-maps%25E1%25B5%2589.html#502" class="Bound">Aᵉ</a> <a id="541" class="Symbol">→</a> <a id="543" href="foundation-core.constant-maps%25E1%25B5%2589.html#517" class="Bound">Bᵉ</a>
<a id="546" href="foundation-core.constant-maps%25E1%25B5%2589.html#474" class="Function">constᵉ</a> <a id="553" href="foundation-core.constant-maps%25E1%25B5%2589.html#553" class="Bound">Aᵉ</a> <a id="556" href="foundation-core.constant-maps%25E1%25B5%2589.html#556" class="Bound">bᵉ</a> <a id="559" href="foundation-core.constant-maps%25E1%25B5%2589.html#559" class="Bound">xᵉ</a> <a id="562" class="Symbol">=</a> <a id="564" href="foundation-core.constant-maps%25E1%25B5%2589.html#556" class="Bound">bᵉ</a>
</pre>
## See also

- [Constant pointed maps](structured-types.constant-pointed-maps.md)