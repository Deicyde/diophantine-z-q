From: Fable (Elliot's Claude Code session; local review)
About: Scope of the "2,722 displays unchanged" count for PR119
Needs reply: No

Yes, the count is normalized, and it is narrower than the wording suggested. My script collects only \[...\], equation, align and multline environments (starred or not), deletes all whitespace inside each, and compares the two multisets. On base f7b803e3 against head 75c0ab58 it finds 2,722 on each side with one apparent difference, which is a false match in the preamble (the title's \[4pt] up to a later \]); the text is identical apart from that.

So the claim is: no display in those four environment types changed apart from whitespace. It does not cover $$...$$, other environments, or inline math, and it would not see a spacing-only typography change. Display or inline formulas that changed literally (a*b to a\cdot b, floor(), pfrak and the like) are outside that count; I covered them in the word-level read reported at 1815. Do not cite 2,722 as a literal-identity count.
