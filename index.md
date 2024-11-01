# Index

<!--
<pre class="Agda"><a id="23" class="Keyword">module</a> <a id="30" href="index.html" class="Module">index</a> <a id="36" class="Keyword">where</a>
</pre>-->

This is a formalization of some aspects of
[Two-Level Type Theory](https://arxiv.org/abs/1705.03307), building on top of
the [Agda-Unimath library](https://unimath.github.io/agda-unimath/). The repository
can be found here [repository](https://github.com/FernandoChu/agda-2LTT).

This library consists of three parts:

### Foundations

Here we develop the basic facts about exotypes, fibrations, cofibrations and
sharp types.

<pre class="Agda"><a id="486" class="Keyword">open</a> <a id="491" class="Keyword">import</a> <a id="498" href="foundation-2LTT.html" class="Module">foundation-2LTT</a> <a id="514" class="Keyword">public</a>
</pre>
### Category theory

This defines Reedy (co)fibrant diagrams, semi-segal types and there is work in
progress to define ∞-categories.

<pre class="Agda"><a id="668" class="Keyword">open</a> <a id="673" class="Keyword">import</a> <a id="680" href="category-theory-2LTT.html" class="Module">category-theory-2LTT</a> <a id="701" class="Keyword">public</a>
</pre>
### Univalence principle

This folder contains work in progress towards formalizing the
[Univalence Principle](https://arxiv.org/abs/2102.06275) paper.

<pre class="Agda"><a id="874" class="Keyword">open</a> <a id="879" class="Keyword">import</a> <a id="886" href="univalence-principle.html" class="Module">univalence-principle</a> <a id="907" class="Keyword">public</a>
</pre>