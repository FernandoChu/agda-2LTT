# Universe levels

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a> <a id="62" class="Keyword">where</a>

<a id="69" class="Keyword">open</a> <a id="74" class="Keyword">import</a> <a id="81" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>
  <a id="98" class="Keyword">using</a> <a id="104" class="Symbol">(</a><a id="105" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="111" class="Symbol">;</a> <a id="113" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="119" class="Symbol">;</a> <a id="121" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="126" class="Symbol">;</a> <a id="128" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="131" class="Symbol">)</a>
  <a id="135" class="Keyword">renaming</a> <a id="144" class="Symbol">(</a><a id="145" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="149" class="Symbol">to</a> <a id="152" class="Primitive">UU</a> <a id="155" class="Symbol">;</a> <a id="157" href="Agda.Primitive.html#512" class="Primitive">Setω</a> <a id="162" class="Symbol">to</a> <a id="165" class="Primitive">UUω</a><a id="168" class="Symbol">)</a>
  <a id="172" class="Keyword">public</a>
</pre>
## Idea

We import Agda's built in mechanism of universe levels. The universes are called
`UU`, which stands for _univalent universe_, although we will not immediately
assume that universes are univalent. This is done in
[foundation.univalence](foundation.univalence.md).
