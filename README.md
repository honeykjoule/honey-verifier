# Eden Verifier

Welcome to the Eden Verifier. This codebase includes a `%verifier` agent along with a few threads that enable you to send Eden computations to a prover to generate proofs that can be passed around and verified. Please see our [blog post](https://zorp.io/blog/hackathon/) for more details.

## Obtaining the proof object from the `%verifier` agent.

So, say you've requested a proof using the `-prove-eden` thread and you want to obtain
the proof you received so that you can, for instance, send it to another ship.

Here's how you would do that in the dojo:


```hoon
::  assumes `cmp` stores the nock sub/fol that you're after
::  and you've already made a call to -prove-eden using cmp
::
=st .^(versioned-state:ver-sur %gx /=verifier=/all/noun)
=rid (~(got by ids.st) cmp)
=prf (~(got by proofs.st) rid)
=proof =+(response.prf ?>(?=(%proof -.-) proof.-))
~&  size-kb+(met 13 (jam proof))
```

1. Line 1 gets the agent state. This contains all of the relevant data we'll need for the next steps, including the proofs themselves.
2. Line 2 gets the associated request id for the computation
3. Line 3 gets the proof update that was provided in the response to our request based on the request id
4. Finally, Line 4 extracts the proof object from the proof update. This line assumes that the proof was successful.

This pattern can be replicated in any generator, thread, or agent in which you make use of the proof system.

A final note: we recommend that you do *not* try to print out the proof since its a big object to print and largely made up of hex data.




