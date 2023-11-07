ICFP Programming Contest 2020 

https://icfpcontest2020.github.io/

implementing a pure, lazy combinator calculus.

this was an experimental approach i tried during the contest that sort of spun out of control - there's no reason to build a STG Machine for this, but i wanted to try!

# ember's shot.

when i saw this thing on the web,
i thought to myself, 

![meme guy from "i guess i'll die" captioned with "i'll give it a shot"](https://i.imgur.com/0LK6DGd.png)

and here we are.

like all artifacts, this thing bears the scars of its creation, evidenced
indelibly in the contribution of the edit history to the current commit hash,
but also in much more straightforward ways like "the code is a fuckin mess",
"why is it all in one file?", "oh heavens" (actual reviews, you won't find a
bigger champion than me, thanks all).

first off, it is important to know that the heart of this runtime is a
`Machine`, and that machine was originally _extremely busted_ (although based on a cool observation, it was only valid in a pure language). maybe future ember
will remember what this means: rightmost-first immediate evaluation?

nextly, note that i ripped off [Simon Marlow and Simon Peyton
Jones](https://simonmar.github.io/bib/papers/eval-apply.pdf), my second shot
at `Machine` was a transcription into rust of their transition system for
`eval/apply`. i assume this vaguely has the shape of something like an "STG
machine" (given the provenance) but i whipped this together in a strange mood
during a weekend, so what it is is what you get. i found this paper doing
some early literature crawling and thought it was really neat, i hadn't
bothered studying this level of the stack before. they recommend `eval/apply` so that's what i implemented.

major unimplemented things, because the icfp stuff doesn't need it, are
generalized data types / case destruction, a more robust data model (more
than pairs and bools), garbage collection, anything approaching a
understandable input language, any program rewriting/peephole optimizations,
deeper FFI/integration with the wider world of human computation, and faster
dispatch/compilation.

this ended up being way more work than a naive recursive thing. but, at least
it doesn't explod the stack?
