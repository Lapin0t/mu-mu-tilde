# A formalization of μμ͂ and classical realizability

## Introduction

μμ͂ is an awesome language. If you know a bit about the curry-howard
correspondance you should be stunned by this term realizing the
excluded middle:

```
LEM : A + (A → ⊥)
LEM = μx. ⟨ inr ( λy. μz. ⟨ inl y ∥ x ⟩ ) ∥ x ⟩
```

If you're still not convinced here's the double negation elimination:

```
DNE : ((A → ⊥) → ⊥) → A
DNE = λf. μx. ⟨ f ∥ app ( λa. μy. ⟨ a ∥ x ⟩ ) elim⊥ ⟩
```

This development is a follow up on [my previous
attempt](https://github.com/Lapin0t/amcr) to formalize some classical
realizability after OPLSS 2022 which i rebooted after my lab (the LAMA in
Chambéry) hosted a workshop on realizability.

μμ͂ is a language that came from looking at the Krivine abstract machine (KAM)
and taking full advantage of its facilities by generalizing its rules and input
language. It is very much a direct computational counterpart to classical
sequent calculus.

Coming from abstract machine transitions, the μμ͂ constructs are quite
"low-level", being able to manipulate the (call-)stack, suspend evaluation and
resume them with a kind of "goto with argument". In fact one can remove the
primitive function type and let it for the user to define.

> **Future work:** actually remove arrow types and add the whole dual bunch of
> type formers. A more ambitious change of language would be to add `∀` and `∃`
> (first order), to have all the actual tools to build realizability models
> for classical first-order theories.

## Design choices

This presentation of μμ͂ and nomenclature for classical realizability
approximately follows what i understood from the 2022 class of Paul Downen at
the OPLSS on classical realizability [^1]. I also looked into his paper with
Zena Ariola [^2], which i find very beautiful and i think you should read! Now
is probably the time to mention that i don't know the bibliography or history
of classical realizability particularly well, afaik the μμ͂ family was initiated
mostly by Hugo Herbelin, Pierre-Louis Curien and Guillaume Munch-Maccagnoni.
Sorry for not citing everything relevant, please do tell me if i'm missing
important facts or getting things wrong.

### Well-typedness

All of the development is presented in well-typed well-scoped fashion. This
means that **untyped terms don't exist**. This might be surprising at first, in
particular in the context of realizability and is simply how i am most
comfortable programming in type theory.

*Well-typed* means that what i call *terms* is isomorphic to what would usually
be a context, a type, a term and a typing derivation relating them.

*Well-scoped* means that variables are not free-standing names but look closer
to pointers or indices into the scope (given by the index).

> **Future work:** it might be interesting to define untyped terms (but still
> well-scoped, we're not barbarians) and typing derivations and relate them to
> my current definitions. Since realizability aims to semantically tie a
> computational layer with a logic layer it might be morally required to make
> the computational layer untyped to be able to call this realizability. Still
> i would prefer making this an addon to the development, perhaps using
> ornaments of some kind.

### Single-sided presentation

The typing derivations of μμ͂ are in close correspondance with sequent calculus
proofs, where instead of introduction and elimination rules from natural
deduction, there are the more symmetric *left-rules* and *right-rules*.
Left-rules act mostly on the *left-context* -- the context of hypothesis.
Correspondingly right-rules act on the *right-context* -- the context of
possible conclusions (exhibiting an element of any type from it enables to
conclude a proof).

Managing contexts in formal syntax developments is hard already so i wanted to
avoid having two contexts (and constructing the direct sum of monoids as `ctx
ty × ctx ty`). Although perfectly valid theoretically, this would mean to
duplicate all the renaming and substitution lemmas in both their left and right
variants, together with compatibility conditions. Instead i adopt a
single-sided presentation, where both contexts are merged into one, containing
types annotated with their "side": `ctx (ty + ty)`, ie "normal" (left)
types and "formally negated" (right) types.

This single-sided presentation has two benefits to me: (1) it factors several
pairs definitions into single polarized versions and (2) it enables me to work
in the usual setting of substitution as a monoid on the monoidal category
`Ctx(T) × T → Set` [^3] [^4]. The classes of terms and co-terms are now simply a
single class of side-annotated terms and likewise variables and co-variables
are merged into a single construct. In the formalization "atomic" types are
elements of `ty0` and "side-annotated" types are elements of `ty`.

> I am happy to report that this is not unheard of: Guillaume Munch-Maccagnoni
> refers to something similar as "Girard's one-sided sequents", versus
> "Gentzen's two-sided sequents" (thanks to Etienne Miquey for spotting this).

### Polarization

Apart from types and formally negated types, there is another level of
polarization going on. In fact μμ͂ as i presented together with weak head
reduction is not confluent! There is an irreconciliable critical pair between
the beta rules for of `μ` (bind current context, aka call-cc) and `μ͂` (bind
current value, aka let). The usual way to resolve this issue and make μμ͂ into a
proper programming language is to treat polarities of types seriously.

Indeed types in μμ͂ have a natural polarity -- reminescent of the CBPV
distinction between programs and values -- according to whether they are
defined by their constructors or by their destructors. Positive types like `⊥`,
`A ⊕ B` or `A & B` have constructors as terms and a matching construct as
co-terms, while `⊤`, `A ⊗ B` and `A ⅋ B` have projections (co-constructors) as
co-terms and abstractions (co-match) as terms. These polarities are what defines
weak reduction, which doesn't happen below match and co-match. Hence
positive types have a call-by-value flavour while negative types have a
call-by-name flavour.

> **Future work**: Realizability is pretty robust and all of this is not needed
> to prove adequacy, so i will leave a properly polarized version for later.

## Map of the code

The support code has been extracted from a bigger development of mine, so some
utilities might not be needed...

- `Prelude.v`: Some generic setup and external library imports.
- `Utils/Psh.v`: Despite the name this defines some construction on indexed
  types or more pedanticly presheaves on *discrete* categories (with no action
  on morphisms).
- `Utils/Rel.v`: Some helpers on indexed relations (relations between
  indexed types).
- `Utils/Ctx.v`: The generic theory of contexts, variables and assignments.
  The category of contexts that i take is mostly the category of finite ordered
  multisets (aka lists) with arbitrary functions between them. Future work
  would be to switch to the more precise category of finite ordered multisets
  with order-preserving embeddings between them, since this is the minimal set
  of arrows needed and they admit a cute inductive presentation based on
  dependently-typed bitvectors.
- `Lang/Syntax.v`: Basic definitions about the types, syntax, renaming,
  substitution and head-reduction relation.
- `Lang/Properties.v`: All the lemmas about renamings and substitutions.
- `CR.v`: The realizability model, together with the adequacy lemma.

The code builds with Coq 8.17 and Coq-Equations 1.3 by typing `dune build`.

## License

Copyright 2023 Peio Borthelle

This program is free software: you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

This program is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with
this program. If not, see <https://www.gnu.org/licenses/>. 

[^1]: Various lecture notes and recordings: https://www.cs.uoregon.edu/research/summerschool/summer22/lectures/
[^2]: Downen & Ariola, "Compiling with Classical Connectives": https://www.pauldownen.com/publications/1907.13227.pdf
[^3]: Fiore & Szamozvancev, "Formal Metatheory of Second-Order Abstract Syntax": https://arxiv.org/abs/2201.03504
[^4]: Allais et al, "A type- and scope-safe universe of syntaxes with binding": https://arxiv.org/abs/2001.11001
[^5]: A similar but unfinished development in Agda: https://github.com/lapin0t/amcr
