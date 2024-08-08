# Learning ABA frameworks w/ASP

Starting SWI-Prolog

```
aba-asp$ swipl
Welcome to SWI-Prolog (threaded, 64 bits, version 9.0.4)
SWI-Prolog comes with ABSOLUTELY NO WARRANTY. This is free software.
Please run ?- license. for legal details.

For online help and background, visit https://www.swi-prolog.org
For built-in help, use ?- help(Topic). or ?- apropos(Word).

?- 
````

Loading ABA learning modules

```prolog
?- consult('aba_asp.pl').
```

`aba_asp.pl` provides the predicate `aba_asp(+BK,+Ep,+En,-S)` to compute solutions of an ABA learning problem; 
it holds if and only if `S` is (a Prolog term representing) a solution of the ABA learning problem specified as follow:
* `BK` is the file containing the encoding of the ABA framework representing the Background Knowledge (conventionally, `BK` must have the extension `.aba`),
* `Ep` is the list of positive examples, and
* `En` is the list of negative examples.

Any solution is printed to a file named `BK.sol.aba` (its ASP encoding is printed to a file named `BK.sol.asp`).

```prolog
aba_asp('./examples/flies_birds.bk',[flies(woodstock),flies(gwaihir),flies(x_pingu),flies(x_pinga)],[flies(pingu),flies(pinga)]).
```

The predicate `aba_asp(+BK,+Ep,+En)` can be used instead of `aba_asp(+BK,+Ep,+En,-S)` if the user is not interested in the Prolog term `S`. 

Setting learning options:
* learning mode: `set_lopt(learning_mode(M))`, where `M` can be either `brave` or `cautious` 
[default: `cautious`];
* folding mode: `set_lopt(folding_mode(M))`, where `M` can be `nd` (nondeterministic folding w/iterative deepening search strategy: generate solutions with `i` folding steps first, then generate solutions with `i+1` folding steps), `all` (nondeterministic folding), or `greedy` (perform all the possible foldings) 
[default: `nd`];
* maximum number of folding steps (only meaningful with `folding_mode(nd)`): `set_lopt(folding_steps(N))`, where `N` specifies the number of folding steps that can be performed on a give rule 
[default: 10];
* folding selection mode: `set_lopt(folding_selection(S))`, where `S` can be either `any` (select any nonintensional rule) or `mgr` (select any rule among the most general nonintensional rules) 
[default: `any`];
* folding selection: `set_lopt(folding_space(M))`,
where `M` can be either `all` (fold with all rules) or `bk` (fold with rules of the background knowledge) 
[default: `all`];
* assumption introduction strategy: `set_lopt(asm_intro(S))`, where `S` can be either `relto` (before introducing a new assumption for the body B, it checks the existence of an assunption relative to B in the rules of the ABA framework) or `sechk` (it checks for a stronger assumption in the stable extension of the ABA framework) 
[default: `relto`].

The `set_lopt(check_ic)` option (used for debugging purposes) asks the tool to generate the ASP encoding including the integrity constraints that can be used to check that all positive examples are consequences of the learned rules and none of the negative examples are consequences of the learned rule. 

## Encoding the Background Knowledge

The Background Knowledge is an ABA framework including the following additional predicates:

* `assumption(A)` representing that `A` is an assumption
* `contrary(A,C)` representing that `C` is the contrary of `A`, and it is defined by a rule of the form 
`contrary(A,C) :- assumption(A).` 