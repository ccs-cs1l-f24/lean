
# An Exploration of Interactive Theorem Proving in Lean

The following writeup is a summary of the progress that I made on exploring the Lean interactive proof verification language. Through this quarter I intended to gain familiarity with lean as an interactive theorem prover for mathematical statements, and my goal was to work up to a proof of a substantial theorem in mathematics. I ended up proving that there are infinitely many primes.

## The Natural Number Game

I started by completing the [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4), an introductory game where the goal is to prove some statements about the natural numbers from the Peano axioms. The game slowly introduces players both to the proofs of various properties of the natural numbers and the general structure of lean proofs. In particular, it explains the framework lean uses of starting with a "goal" statement and transforming it using given results into the statement "True". 

The main tools I learned from playing this game were the `rw` and `apply` tactics (used to rewrite expressions and apply theorems, respectively). I also gained familiarity with constructing inductive arguments using the language. Additionally, I learned some philosophical lessons about lean, in particular that sometimes the most "obvious" statements can be the hardest to prove. For instance, I had a lot of trouble converting a statement that "an integer with certain properties exists" to a form where I could use that integer to do other computations.

## Proving that $\sqrt{2}$ is Irrational

The main goal for this proof was to understand the mechanics of a proof by contradiction, as well as to use the tools given by [Mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib.html). Lean itself has very little support for simple mathematical statements, and Mathlib attempts to account for this by providing as many simple statements as possible (e.g. all primes are at least 2, and similar statements). However, it can be very hard to navigate this, because it often feels like Mathlib has too much and too little information.

I learned the value of the `apply?` tactic, which you can use to search mathlib for tools that can be applied to a particular situation in a proof. I also learned the `refine` tactic, which reduces a proof from the result of a theorem to the preconditions under which it is true, and the `obtain` tactic, which allows you to extract variables from an "exists" ($\exists$) statement.

## Proving that there are Infinitely Many Primes

This proof required much more effort and was much more complicated than the previous work I had done. I had to craft a strategy for the proof and work out the details. Part of the difficulty of Lean is formalizing the statements that might be easy to state in words, but are difficult to put into symbols. I settled on the statement $\forall n \in \mathbb{N}, \exists p \in \mathbb{N}, p > n \wedge p \text{ prime}$ (for every natural number $n,$ there is a prime larger than $n$).

The general argument for the proof is as follows: pick any $n$; we will show that there is a prime number larger than $n$. To do this, take any prime divisor of $n! + 1.$ Then $p \cdot (l + 1) = n! + 1$ for some $l \in \mathbb{N},$ so $p \cdot l < n! < p \cdot (l + 1).$ It follows that $\gcd(p, n!) = 1,$ so $p$ is coprime to all natural numbers smaller than $n$, hence is greater than $n.$ Thus $p$ is such a prime number.

## Possible Next Steps

There are many possibilities for more advanced projects, but these can generally be split into a few different directions. One natural extension of the work done this quarter would be to try to prove more advanced results, or to try to build a knowledge base of tools in one specific field (e.g. number theory or analysis). 

Another option would be to explore lean more from the standpoint of a programming language. For instance, how does lean actually process theorems? What does it mean to interpret statements as types or check types against each other? How does lean perform computations?

The final option would be to explore lean as a logic system. Lean uses a framework called the calculus of constructions, which as a logic system likely has some limitations when compared to logic systems that we use for manual proofs. Exploring the limits of this proof method could lead to interesting results.

 
