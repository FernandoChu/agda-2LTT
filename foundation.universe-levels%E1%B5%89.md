# Universe levels

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a> <a id="63" class="Keyword">where</a>

<a id="70" class="Keyword">open</a> <a id="75" class="Keyword">import</a> <a id="82" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>
  <a id="99" class="Keyword">using</a> <a id="105" class="Symbol">(</a><a id="106" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="112" class="Symbol">;</a> <a id="114" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="120" class="Symbol">;</a> <a id="122" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="127" class="Symbol">;</a> <a id="129" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="132" class="Symbol">)</a>
  <a id="136" class="Keyword">renaming</a> <a id="145" class="Symbol">(</a><a id="146" href="Agda.Primitive.html#429" class="Primitive">SSet</a> <a id="151" class="Symbol">to</a> <a id="154" class="Primitive">UUᵉ</a> <a id="158" class="Symbol">;</a> <a id="160" href="Agda.Primitive.html#553" class="Primitive">SSetω</a> <a id="166" class="Symbol">to</a> <a id="169" class="Primitive">UUωᵉ</a><a id="173" class="Symbol">)</a>
  <a id="177" class="Keyword">public</a>
</pre>
## Idea

We import Agda's built in mechanism of universe levels. The universes are called
`UU`, which stands for _univalent universe_, although we will not immediately
assume that universes are univalent. This is done in
[foundation.univalence](foundation.univalence.md).
