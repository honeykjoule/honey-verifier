# Eden Verifier

Welcome to the Eden Verifier. This codebase includes a `%verifier` agent along with a few threads that enable you to send Eden computations to a prover to generate proofs that can be passed around and verified. Please see our [blog post](https://zorp.io/blog/hackathon/) for more details.




## Obtaining the verification result after the thread has timed out

In the ideal case, the `-prove-eden` thread returns a `verify-result`.
However, for various reasons, the thread can time out before the proof is received from the prover.
All is not lost, though; you can still scry out the `verify-result` from the `%verifier` agent once the 


You'll know the request completed when you see printfs like `"verifier: got proof update for 0v7.864ms.t3bnh.vrr35.ipg91.5ct89"`, and then `"proof has been processed"` in the dojo. This means that the verifier received the proof object and finished verifying it. We'll still confirm this using a scry though.


Here's the recipe:

```hoon
::  assumes you're developing on the `%zkvm` desk, and
::  assumes `cmp` stores the nock sub/fol that you're after
::  and you've already made a call to -prove-eden using cmp
::
=ver-sur -build-file /=zkvm=/sur/verifier-app/hoon
=st .^(versioned-state:ver-sur %gx /=verifier=/all/noun)
=rid (~(got by ids.st) cmp)
=has-result .^(? %gx /=verifier=/has-result/(scot %uv rid)/noun)
```
Ensure that `has-result` is `%.y`. If it isn't, try again later once you see the printfs.

Then, you can simply scry out the the verify result like so.


```hoon
=vr ?:  has-result
      .^((unit verify-result:ver-sur) %gx /=verifier=/proof-result/(scot %uv rid)/noun)
    ~|(%verify-result-not-present !!)
```



## Obtaining the proof object from the `%verifier` agent.

So, say you've requested a proof using the `-prove-eden` thread and you want to obtain
the proof you received so that you can, for instance, send it to another ship.

Here's how you would do that in the dojo:


```hoon
::  assumes you're developing on the `%zkvm` desk, and
::  assumes `cmp` stores the nock sub/fol that you're after
::  and you've already made a call to -prove-eden using cmp
::
=ver-sur -build-file /=zkvm=/sur/verifier-app/hoon
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




